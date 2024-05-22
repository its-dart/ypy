use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use std::rc::Weak;

use crate::type_conversions::ToPython;
use crate::y_array::YArray;
use crate::y_map::YMap;
use crate::y_text::YText;
use crate::y_transaction::YTransaction;
use crate::y_transaction::YTransactionInner;
use crate::y_xml::YXmlElement;
use crate::y_xml::YXmlFragment;
use crate::y_xml::YXmlText;
use lib0::any::Any;
use pyo3::prelude::*;
use pyo3::types::PyBytes;
use pyo3::types::PyTuple;
use yrs::block::ItemContent;
use yrs::types::{BranchPtr, ToJson, TYPE_REFS_MAP, TYPE_REFS_XML_TEXT};
use yrs::updates::decoder::Decode;
use yrs::updates::encoder::Encode;
use yrs::OffsetKind;
use yrs::Options;
use yrs::SubscriptionId;
use yrs::Transact;
use yrs::TransactionCleanupEvent;
use yrs::TransactionMut;
use yrs::{
    Doc, MapRef, Transaction, Update, Xml, XmlFragment, XmlFragmentRef, XmlNode, XmlTextRef,
};

pub trait WithDoc<T> {
    fn with_doc(self, doc: Rc<RefCell<YDocInner>>) -> T;
}
pub trait WithTransaction {
    fn get_doc(&self) -> Rc<RefCell<YDocInner>>;

    fn with_transaction<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&YTransactionInner) -> R,
    {
        let txn = self.get_transaction();
        let mut txn = txn.borrow_mut();
        f(&mut txn)
    }

    fn get_transaction(&self) -> Rc<RefCell<YTransactionInner>> {
        let doc = self.get_doc();
        let txn = doc.borrow_mut().begin_transaction();
        txn
    }
}

pub struct YDocInner {
    doc: Doc,
    txn: Option<Weak<RefCell<YTransactionInner>>>,
}

impl YDocInner {
    pub fn has_transaction(&self) -> bool {
        if let Some(weak_txn) = &self.txn {
            if let Some(txn) = weak_txn.upgrade() {
                return !txn.borrow().committed;
            }
        }
        false
    }

    pub fn begin_transaction(&mut self) -> Rc<RefCell<YTransactionInner>> {
        // Check if we think we still have a transaction
        if let Some(weak_txn) = &self.txn {
            // And if it's actually around
            if let Some(txn) = weak_txn.upgrade() {
                if !txn.borrow().committed {
                    return txn;
                }
            }
        }
        // HACK: get rid of lifetime
        let txn = unsafe {
            std::mem::transmute::<TransactionMut, TransactionMut<'static>>(self.doc.transact_mut())
        };
        let txn = YTransactionInner::new(txn);
        let txn = Rc::new(RefCell::new(txn));
        self.txn = Some(Rc::downgrade(&txn));
        txn
    }

    pub fn commit_transaction(&mut self) {
        if let Some(weak_txn) = &self.txn {
            if let Some(txn) = weak_txn.upgrade() {
                let mut txn = txn.borrow_mut();
                txn.commit();
            }
        }
        self.txn = None;
    }

    pub fn transact_mut<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut YTransactionInner) -> R,
    {
        // HACK: get rid of lifetime
        let txn = unsafe {
            std::mem::transmute::<TransactionMut, TransactionMut<'static>>(self.doc.transact_mut())
        };
        let mut txn = YTransactionInner::new(txn);
        f(&mut txn)
    }
}

/// A Ypy document type. Documents are most important units of collaborative resources management.
/// All shared collections live within a scope of their corresponding documents. All updates are
/// generated on per document basis (rather than individual shared type). All operations on shared
/// collections happen via [YTransaction], which lifetime is also bound to a document.
///
/// Document manages so called root types, which are top-level shared types definitions (as opposed
/// to recursively nested types).
///
/// A basic workflow sample:
///
/// ```python
/// from y_py import YDoc
///
/// doc = YDoc()
/// with doc.begin_transaction() as txn:
///     text = txn.get_text('name')
///     text.push(txn, 'hello world')
///     output = text.to_string(txn)
///     print(output)
/// ```
#[pyclass(unsendable, subclass)]
pub struct YDoc(Rc<RefCell<YDocInner>>);

impl YDoc {
    pub fn guard_store(&self) -> PyResult<()> {
        if self.0.borrow().has_transaction() {
            return Err(pyo3::exceptions::PyAssertionError::new_err(
                "Transaction already started!",
            ));
        }
        Ok(())
    }
}

#[pymethods]
impl YDoc {
    /// Creates a new Ypy document. If `client_id` parameter was passed it will be used as this
    /// document globally unique identifier (it's up to caller to ensure that requirement).
    /// Otherwise it will be assigned a randomly generated number.
    #[new]
    pub fn new(
        client_id: Option<u64>,
        offset_kind: Option<String>,
        skip_gc: Option<bool>,
    ) -> PyResult<Self> {
        let mut options = Options::default();
        if let Some(client_id) = client_id {
            options.client_id = client_id;
        }

        if let Some(raw_offset) = offset_kind {
            let clean_offset = raw_offset.to_lowercase().replace('-', "");
            let offset = match clean_offset.as_str() {
                "utf8" => Ok(OffsetKind::Bytes),
                "utf16" => Ok(OffsetKind::Utf16),
                "utf32" => Ok(OffsetKind::Utf32),
                _ => Err(pyo3::exceptions::PyValueError::new_err(format!(
                    "'{}' is not a valid offset kind (utf8, utf16, or utf32).",
                    clean_offset
                ))),
            }?;
            options.offset_kind = offset;
        }

        if let Some(skip_gc) = skip_gc {
            options.skip_gc = skip_gc;
        }

        let inner = YDocInner {
            doc: Doc::with_options(options),
            txn: None,
        };

        Ok(YDoc(Rc::new(RefCell::new(inner))))
    }

    /// Gets globally unique identifier of this `YDoc` instance.
    #[getter]
    pub fn client_id(&self) -> u64 {
        self.0.borrow().doc.client_id()
    }

    /// Returns a new transaction for this document. Ypy shared data types execute their
    /// operations in a context of a given transaction. Each document can have only one active
    /// transaction at the time - subsequent attempts will cause exception to be thrown.
    ///
    /// Transactions started with `doc.begin_transaction` can be released by deleting the transaction object
    /// method.
    ///
    /// Example:
    ///
    /// ```python
    /// from y_py import YDoc
    /// doc = YDoc()
    /// text = doc.get_text('name')
    /// with doc.begin_transaction() as txn:
    ///     text.insert(txn, 0, 'hello world')
    /// ```
    pub fn begin_transaction(&self) -> YTransaction {
        YTransaction::new(self.0.borrow_mut().begin_transaction())
    }

    pub fn transact(&mut self, callback: PyObject) -> PyResult<PyObject> {
        let txn = YTransaction::new(self.0.borrow_mut().begin_transaction());
        let result = Python::with_gil(|py| {
            let args = PyTuple::new(py, vec![txn.into_py(py)]);
            callback.call(py, args, None)
        });
        // Make transaction commit after callback returns
        let mut doc = self.0.borrow_mut();
        doc.commit_transaction();
        result
    }

    /// Returns a `YMap` shared data type, that's accessible for subsequent accesses using given
    /// `name`.
    ///
    /// If there was no instance with this name before, it will be created and then returned.
    ///
    /// If there was an instance with this name, but it was of different type, it will be projected
    /// onto `YMap` instance.
    pub fn get_map(&mut self, name: &str) -> PyResult<YMap> {
        self.guard_store()?;
        Ok(self
            .0
            .borrow()
            .doc
            .get_or_insert_map(name)
            .with_doc(self.0.clone()))
    }

    /// Returns a `YXmlElement` shared data type, that's accessible for subsequent accesses using
    /// given `name`.
    ///
    /// If there was no instance with this name before, it will be created and then returned.
    ///
    /// If there was an instance with this name, but it was of different type, it will be projected
    /// onto `YXmlElement` instance.
    pub fn get_xml_element(&mut self, name: &str) -> PyResult<YXmlElement> {
        self.guard_store()?;
        Ok(self
            .0
            .borrow()
            .doc
            .get_or_insert_xml_element(name)
            .with_doc(self.0.clone()))
    }

    /// Returns a `YXmlText` shared data type, that's accessible for subsequent accesses using given
    /// `name`.
    ///
    /// If there was no instance with this name before, it will be created and then returned.
    ///
    /// If there was an instance with this name, but it was of different type, it will be projected
    /// onto `YXmlText` instance.
    pub fn get_xml_text(&mut self, name: &str) -> PyResult<YXmlText> {
        self.guard_store()?;
        Ok(self
            .0
            .borrow()
            .doc
            .get_or_insert_xml_text(name)
            .with_doc(self.0.clone()))
    }

    /// Returns a `YXmlFragment` shared data type, that's accessible for subsequent accesses using
    /// given `name`.
    ///
    /// If there was no instance with this name before, it will be created and then returned.
    ///
    /// If there was an instance with this name, but it was of different type, it will be projected
    /// onto `YXmlFragment` instance.
    pub fn get_xml_fragment(&mut self, name: &str) -> PyResult<YXmlFragment> {
        self.guard_store()?;
        Ok(self
            .0
            .borrow()
            .doc
            .get_or_insert_xml_fragment(name)
            .with_doc(self.0.clone()))
    }

    /// Returns a `YArray` shared data type, that's accessible for subsequent accesses using given
    /// `name`.
    ///
    /// If there was no instance with this name before, it will be created and then returned.
    ///
    /// If there was an instance with this name, but it was of different type, it will be projected
    /// onto `YArray` instance.
    pub fn get_array(&mut self, name: &str) -> PyResult<YArray> {
        self.guard_store()?;
        Ok(self
            .0
            .borrow()
            .doc
            .get_or_insert_array(name)
            .with_doc(self.0.clone()))
    }

    /// Returns a `YText` shared data type, that's accessible for subsequent accesses using given
    /// `name`.
    ///
    /// If there was no instance with this name before, it will be created and then returned.
    ///
    /// If there was an instance with this name, but it was of different type, it will be projected
    /// onto `YText` instance.
    pub fn get_text(&mut self, name: &str) -> PyResult<YText> {
        self.guard_store()?;
        Ok(self
            .0
            .borrow()
            .doc
            .get_or_insert_text(name)
            .with_doc(self.0.clone()))
    }

    /// Subscribes a callback to a `YDoc` lifecycle event.
    pub fn observe_after_transaction(&mut self, callback: PyObject) -> SubscriptionId {
        self.0
            .borrow()
            .doc
            .observe_transaction_cleanup(move |txn, event| {
                Python::with_gil(|py| {
                    let event = AfterTransactionEvent::new(event, txn);
                    if let Err(err) = callback.call1(py, (event,)) {
                        err.restore(py)
                    }
                })
            })
            .unwrap()
            .into()
    }
}

/// Encodes a state vector of a given Ypy document into its binary representation using lib0 v1
/// encoding. State vector is a compact representation of updates performed on a given document and
/// can be used by `encode_state_as_update` on remote peer to generate a delta update payload to
/// synchronize changes between peers.
///
/// Example:
///
/// ```python
/// from y_py import YDoc, encode_state_vector, encode_state_as_update, apply_update from y_py
///
/// # document on machine A
/// local_doc = YDoc()
/// local_sv = encode_state_vector(local_doc)
///
/// # document on machine B
/// remote_doc = YDoc()
/// remote_delta = encode_state_as_update(remote_doc, local_sv)
///
/// apply_update(local_doc, remote_delta)
/// ```
#[pyfunction]
pub fn encode_state_vector(doc: &mut YDoc) -> PyObject {
    let txn = doc.0.borrow_mut().begin_transaction();
    let txn = YTransaction::new(txn);
    txn.state_vector_v1()
}

/// Encodes all updates that have happened since a given version `vector` into a compact delta
/// representation using lib0 v1 encoding. If `vector` parameter has not been provided, generated
/// delta payload will contain all changes of a current Ypy document, working effectively as its
/// state snapshot.
///
/// Example:
///
/// ```python
/// from y_py import YDoc, encode_state_vector, encode_state_as_update, apply_update
///
/// # document on machine A
/// local_doc = YDoc()
/// local_sv = encode_state_vector(local_doc)
///
/// # document on machine B
/// remote_doc = YDoc()
/// remote_delta = encode_state_as_update(remote_doc, local_sv)
///
/// apply_update(local_doc, remote_delta)
/// ```
#[pyfunction]
pub fn encode_state_as_update(doc: &mut YDoc, vector: Option<Vec<u8>>) -> PyResult<PyObject> {
    let txn = doc.0.borrow_mut().begin_transaction();
    YTransaction::new(txn).diff_v1(vector)
}

/// Applies delta update generated by the remote document replica to a current document. This
/// method assumes that a payload maintains lib0 v1 encoding format.
///
/// Example:
///
/// ```python
/// from y_py import YDoc, encode_state_vector, encode_state_as_update, apply_update
///
/// # document on machine A
/// local_doc = YDoc()
/// local_sv = encode_state_vector(local_doc)
///
/// # document on machine B
/// remote_doc = YDoc()
/// remote_delta = encode_state_as_update(remote_doc, local_sv)
///
/// apply_update(local_doc, remote_delta)
/// ```
#[pyfunction]
pub fn apply_update(doc: &mut YDoc, diff: Vec<u8>) -> PyResult<()> {
    let txn = doc.0.borrow_mut().begin_transaction();
    YTransaction::new(txn).apply_v1(diff)?;

    Ok(())
}

pub fn process_xml_text_node(txn: &Transaction, xml_text_ref: &XmlTextRef) -> Any {
    let mut result: HashMap<String, Any> = HashMap::new();
    // Update attributes of the current Text XmlNode
    let xml_text_map_ref: MapRef = xml_text_ref.clone().into();
    if let Any::Map(at) = xml_text_map_ref.to_json(txn) {
        for (k, v) in at.iter() {
            result.insert(k.to_string(), v.clone());
        }
    }
    if let Some(xml_text_children) = xml_text_ref.successors() {
        let mut children: Vec<Any> = vec![];
        let mut child_result: HashMap<String, Any> = HashMap::new();
        /* xml_text_children contains a sequence of ItemContent instances:
           ItemContent::Type(YMap) => {"__type": "text", "__format": 0, "__style": "", "__mode": 0, "__detail": 0}
           ItemContent::String(SplittableString) => "a"
           ItemContent::String(SplittableString) => " "
           ...
           ItemContent::Type(YMap) => {"__type": "text", "__format": 0, "__style": "", "__mode": 0, "__detail": 0}
           ItemContent::String(SplittableString) => "b"
        */
        for child in xml_text_children {
            match &child {
                ItemContent::Type(c) => {
                    let ptr = BranchPtr::from(c);
                    match ptr.type_ref() {
                        TYPE_REFS_MAP => {
                            if !child_result.is_empty() {
                                children.push(Any::Map(Box::new(child_result)));
                                child_result = HashMap::new();
                            }
                            if let Any::Map(at) = MapRef::from(ptr).to_json(txn) {
                                for (k, v) in at.iter() {
                                    child_result.insert(k.to_string(), v.clone());
                                }
                            }
                        }
                        TYPE_REFS_XML_TEXT => {
                            let child_xml_text_ref = XmlTextRef::from(ptr);
                            if !child_result.is_empty() {
                                children.push(Any::Map(Box::new(child_result)));
                                child_result = HashMap::new();
                            }
                            children.push(process_xml_text_node(txn, &child_xml_text_ref));
                        }
                        _ => {
                            panic!("Unexpected type ref: {:?}", ptr.type_ref());
                        }
                    }
                }
                ItemContent::String(child_text_part) => {
                    if !child_result.is_empty() {
                        let mut child_text = child_result
                            .get("text")
                            .unwrap_or(&Any::String("".to_string().into()))
                            .to_string();
                        child_text.push_str(child_text_part.as_str());
                        child_result.insert("text".to_string(), Any::String(child_text.into()));
                    }
                }
                ItemContent::Deleted(_) => (),
                _ => {
                    eprintln!("Ignored child of XmlTextRef: {:?}", child);
                }
            }
        }
        if !child_result.is_empty() {
            children.push(Any::Map(Box::new(child_result)));
        }
        if !children.is_empty() {
            result.insert(
                "children".to_string(),
                Any::Array(children.into_boxed_slice()),
            );
        }
    }
    Any::Map(Box::new(result))
}

pub fn process_xml_node(
    txn: &Transaction,
    result: &mut HashMap<String, Any>,
    first_child_maybe: Option<XmlNode>,
) {
    let first_child = match first_child_maybe {
        Some(first_child) => first_child,
        None => {
            return;
        }
    };
    let mut children: Vec<Any> = vec![];
    match first_child {
        XmlNode::Text(text) => {
            children.push(process_xml_text_node(txn, &text));
            text.siblings(txn)
                .for_each(|sibling: XmlNode| match sibling {
                    XmlNode::Text(text) => {
                        children.push(process_xml_text_node(txn, &text));
                    }
                    _ => {
                        eprintln!("Unhandled XmlNode::Text sibling: {:?}", sibling);
                    }
                });
        }
        XmlNode::Fragment(fragment) => {
            eprintln!("Unhandled Fragment: {:?}", fragment);
        }
        XmlNode::Element(element) => {
            eprintln!("Unhandled Element: {:?}", element);
        }
    }
    result.insert(
        "children".to_string(),
        Any::Array(children.into_boxed_slice()),
    );
}

pub fn process_doc(diff: Vec<u8>) -> HashMap<String, Any> {
    let mut result: HashMap<String, Any> = HashMap::new();
    let doc: Doc = Doc::new();
    let root: XmlFragmentRef = doc.get_or_insert_xml_fragment("root");
    doc.transact_mut()
        .apply_update(Update::decode_v1(diff.as_slice()).unwrap());
    let txn: Transaction = doc.transact();

    // Update attributes of the root XmlNode
    let root_map: MapRef = root.clone().into();
    if let Any::Map(at) = root_map.to_json(&txn) {
        for (k, v) in at.iter() {
            result.insert(k.to_string(), v.clone());
        }
    }

    // Process the children of the root XmlNode
    process_xml_node(&txn, &mut result, root.first_child());

    result
}

#[pyfunction]
pub fn update_to_nodes(diff: Vec<u8>) -> PyObject {
    let result = process_doc(diff);

    Python::with_gil(|py| result.into_py(py))
}

#[pyclass(unsendable)]
pub struct AfterTransactionEvent {
    before_state: PyObject,
    after_state: PyObject,
    delete_set: PyObject,
    update: PyObject,
}

impl AfterTransactionEvent {
    fn new(event: &TransactionCleanupEvent, txn: &TransactionMut) -> Self {
        // Convert all event data into Python objects eagerly, so that we don't have to hold
        // on to the transaction.
        let before_state = event.before_state.encode_v1();
        let before_state: PyObject = Python::with_gil(|py| PyBytes::new(py, &before_state).into());
        let after_state = event.after_state.encode_v1();
        let after_state: PyObject = Python::with_gil(|py| PyBytes::new(py, &after_state).into());
        let delete_set = event.delete_set.encode_v1();
        let delete_set: PyObject = Python::with_gil(|py| PyBytes::new(py, &delete_set).into());
        let update = txn.encode_update_v1();
        let update = Python::with_gil(|py| PyBytes::new(py, &update).into());
        AfterTransactionEvent {
            before_state,
            after_state,
            delete_set,
            update,
        }
    }
}

#[pymethods]
impl AfterTransactionEvent {
    /// Returns a current shared type instance, that current event changes refer to.
    #[getter]
    pub fn before_state(&mut self) -> PyObject {
        self.before_state.clone()
    }

    #[getter]
    pub fn after_state(&mut self) -> PyObject {
        self.after_state.clone()
    }

    #[getter]
    pub fn delete_set(&mut self) -> PyObject {
        self.delete_set.clone()
    }

    pub fn get_update(&self) -> PyObject {
        self.update.clone()
    }
}

#[cfg(test)]
mod test {
    use crate::y_doc::process_doc;
    use assert_json_diff::assert_json_eq;
    use lib0::any::Any;
    use serde_json::{from_str, json, to_string_pretty, Value};

    #[test]
    fn parse_nested_xml_text_nodes() {
        let update_bytes: Vec<u8> = b"\x01\x61\x9c\xb5\xe4\xcf\x0e\x00\x28\x01\x04\x72\x6f\x6f\x74\x05\x5f\x5f\x64\x69\x72\x01\x77\x03\x6c\x74\x72\x07\x01\x04\x72\x6f\x6f\x74\x06\x28\x00\x9c\xb5\xe4\xcf\x0e\x01\x06\x5f\x5f\x74\x79\x70\x65\x01\x77\x09\x70\x61\x72\x61\x67\x72\x61\x70\x68\x28\x00\x9c\xb5\xe4\xcf\x0e\x01\x08\x5f\x5f\x66\x6f\x72\x6d\x61\x74\x01\x7d\x00\x28\x00\x9c\xb5\xe4\xcf\x0e\x01\x08\x5f\x5f\x69\x6e\x64\x65\x6e\x74\x01\x7d\x00\x28\x00\x9c\xb5\xe4\xcf\x0e\x01\x05\x5f\x5f\x64\x69\x72\x01\x77\x03\x6c\x74\x72\x07\x00\x9c\xb5\xe4\xcf\x0e\x01\x01\x28\x00\x9c\xb5\xe4\xcf\x0e\x06\x06\x5f\x5f\x74\x79\x70\x65\x01\x77\x04\x74\x65\x78\x74\x28\x00\x9c\xb5\xe4\xcf\x0e\x06\x08\x5f\x5f\x66\x6f\x72\x6d\x61\x74\x01\x7d\x00\x28\x00\x9c\xb5\xe4\xcf\x0e\x06\x07\x5f\x5f\x73\x74\x79\x6c\x65\x01\x77\x00\x28\x00\x9c\xb5\xe4\xcf\x0e\x06\x06\x5f\x5f\x6d\x6f\x64\x65\x01\x7d\x00\x28\x00\x9c\xb5\xe4\xcf\x0e\x06\x08\x5f\x5f\x64\x65\x74\x61\x69\x6c\x01\x7d\x00\x84\x9c\xb5\xe4\xcf\x0e\x06\x01\x61\x87\x9c\xb5\xe4\xcf\x0e\x01\x06\x28\x00\x9c\xb5\xe4\xcf\x0e\x0d\x06\x5f\x5f\x74\x79\x70\x65\x01\x77\x04\x6c\x69\x73\x74\x28\x00\x9c\xb5\xe4\xcf\x0e\x0d\x08\x5f\x5f\x66\x6f\x72\x6d\x61\x74\x01\x7d\x00\x28\x00\x9c\xb5\xe4\xcf\x0e\x0d\x08\x5f\x5f\x69\x6e\x64\x65\x6e\x74\x01\x7d\x00\x21\x00\x9c\xb5\xe4\xcf\x0e\x0d\x05\x5f\x5f\x64\x69\x72\x01\x28\x00\x9c\xb5\xe4\xcf\x0e\x0d\x0a\x5f\x5f\x6c\x69\x73\x74\x54\x79\x70\x65\x01\x77\x06\x6e\x75\x6d\x62\x65\x72\x28\x00\x9c\xb5\xe4\xcf\x0e\x0d\x05\x5f\x5f\x74\x61\x67\x01\x77\x02\x6f\x6c\x28\x00\x9c\xb5\xe4\xcf\x0e\x0d\x07\x5f\x5f\x73\x74\x61\x72\x74\x01\x7d\x01\x07\x00\x9c\xb5\xe4\xcf\x0e\x0d\x06\x28\x00\x9c\xb5\xe4\xcf\x0e\x15\x06\x5f\x5f\x74\x79\x70\x65\x01\x77\x08\x6c\x69\x73\x74\x69\x74\x65\x6d\x28\x00\x9c\xb5\xe4\xcf\x0e\x15\x08\x5f\x5f\x66\x6f\x72\x6d\x61\x74\x01\x7d\x00\x28\x00\x9c\xb5\xe4\xcf\x0e\x15\x08\x5f\x5f\x69\x6e\x64\x65\x6e\x74\x01\x7d\x00\x21\x00\x9c\xb5\xe4\xcf\x0e\x15\x05\x5f\x5f\x64\x69\x72\x01\x28\x00\x9c\xb5\xe4\xcf\x0e\x15\x07\x5f\x5f\x76\x61\x6c\x75\x65\x01\x7d\x01\x01\x00\x9c\xb5\xe4\xcf\x0e\x15\x01\x00\x05\x81\x9c\xb5\xe4\xcf\x0e\x1b\x01\x84\x9c\xb5\xe4\xcf\x0e\x0c\x01\x20\x87\x9c\xb5\xe4\xcf\x0e\x22\x01\x28\x00\x9c\xb5\xe4\xcf\x0e\x23\x06\x5f\x5f\x74\x79\x70\x65\x01\x77\x04\x74\x65\x78\x74\x28\x00\x9c\xb5\xe4\xcf\x0e\x23\x08\x5f\x5f\x66\x6f\x72\x6d\x61\x74\x01\x7d\x01\x28\x00\x9c\xb5\xe4\xcf\x0e\x23\x07\x5f\x5f\x73\x74\x79\x6c\x65\x01\x77\x00\x28\x00\x9c\xb5\xe4\xcf\x0e\x23\x06\x5f\x5f\x6d\x6f\x64\x65\x01\x7d\x00\x28\x00\x9c\xb5\xe4\xcf\x0e\x23\x08\x5f\x5f\x64\x65\x74\x61\x69\x6c\x01\x7d\x00\x84\x9c\xb5\xe4\xcf\x0e\x23\x01\x62\xa1\x9c\xb5\xe4\xcf\x0e\x11\x01\xa1\x9c\xb5\xe4\xcf\x0e\x19\x01\xa8\x9c\xb5\xe4\xcf\x0e\x2a\x01\x77\x03\x6c\x74\x72\xa8\x9c\xb5\xe4\xcf\x0e\x2b\x01\x77\x03\x6c\x74\x72\x87\x9c\xb5\xe4\xcf\x0e\x21\x01\x28\x00\x9c\xb5\xe4\xcf\x0e\x2e\x06\x5f\x5f\x74\x79\x70\x65\x01\x77\x04\x74\x65\x78\x74\x28\x00\x9c\xb5\xe4\xcf\x0e\x2e\x08\x5f\x5f\x66\x6f\x72\x6d\x61\x74\x01\x7d\x00\x28\x00\x9c\xb5\xe4\xcf\x0e\x2e\x07\x5f\x5f\x73\x74\x79\x6c\x65\x01\x77\x00\x28\x00\x9c\xb5\xe4\xcf\x0e\x2e\x06\x5f\x5f\x6d\x6f\x64\x65\x01\x7d\x00\x28\x00\x9c\xb5\xe4\xcf\x0e\x2e\x08\x5f\x5f\x64\x65\x74\x61\x69\x6c\x01\x7d\x00\x84\x9c\xb5\xe4\xcf\x0e\x2e\x01\x63\x81\x9c\xb5\xe4\xcf\x0e\x15\x01\x00\x05\x87\x9c\xb5\xe4\xcf\x0e\x35\x06\x28\x00\x9c\xb5\xe4\xcf\x0e\x3b\x06\x5f\x5f\x74\x79\x70\x65\x01\x77\x08\x6c\x69\x73\x74\x69\x74\x65\x6d\x28\x00\x9c\xb5\xe4\xcf\x0e\x3b\x08\x5f\x5f\x66\x6f\x72\x6d\x61\x74\x01\x7d\x00\x28\x00\x9c\xb5\xe4\xcf\x0e\x3b\x08\x5f\x5f\x69\x6e\x64\x65\x6e\x74\x01\x7d\x00\x21\x00\x9c\xb5\xe4\xcf\x0e\x3b\x05\x5f\x5f\x64\x69\x72\x01\x28\x00\x9c\xb5\xe4\xcf\x0e\x3b\x07\x5f\x5f\x76\x61\x6c\x75\x65\x01\x7d\x02\x07\x00\x9c\xb5\xe4\xcf\x0e\x3b\x06\x28\x00\x9c\xb5\xe4\xcf\x0e\x41\x06\x5f\x5f\x74\x79\x70\x65\x01\x77\x04\x6c\x69\x73\x74\x28\x00\x9c\xb5\xe4\xcf\x0e\x41\x08\x5f\x5f\x66\x6f\x72\x6d\x61\x74\x01\x7d\x00\x28\x00\x9c\xb5\xe4\xcf\x0e\x41\x08\x5f\x5f\x69\x6e\x64\x65\x6e\x74\x01\x7d\x00\x28\x00\x9c\xb5\xe4\xcf\x0e\x41\x05\x5f\x5f\x64\x69\x72\x01\x77\x03\x6c\x74\x72\x28\x00\x9c\xb5\xe4\xcf\x0e\x41\x0a\x5f\x5f\x6c\x69\x73\x74\x54\x79\x70\x65\x01\x77\x06\x6e\x75\x6d\x62\x65\x72\x28\x00\x9c\xb5\xe4\xcf\x0e\x41\x05\x5f\x5f\x74\x61\x67\x01\x77\x02\x6f\x6c\x28\x00\x9c\xb5\xe4\xcf\x0e\x41\x07\x5f\x5f\x73\x74\x61\x72\x74\x01\x7d\x01\x07\x00\x9c\xb5\xe4\xcf\x0e\x41\x06\x28\x00\x9c\xb5\xe4\xcf\x0e\x49\x06\x5f\x5f\x74\x79\x70\x65\x01\x77\x08\x6c\x69\x73\x74\x69\x74\x65\x6d\x28\x00\x9c\xb5\xe4\xcf\x0e\x49\x08\x5f\x5f\x66\x6f\x72\x6d\x61\x74\x01\x7d\x00\x28\x00\x9c\xb5\xe4\xcf\x0e\x49\x08\x5f\x5f\x69\x6e\x64\x65\x6e\x74\x01\x7d\x00\x21\x00\x9c\xb5\xe4\xcf\x0e\x49\x05\x5f\x5f\x64\x69\x72\x01\x28\x00\x9c\xb5\xe4\xcf\x0e\x49\x07\x5f\x5f\x76\x61\x6c\x75\x65\x01\x7d\x01\xa8\x9c\xb5\xe4\xcf\x0e\x4d\x01\x77\x03\x6c\x74\x72\x07\x00\x9c\xb5\xe4\xcf\x0e\x49\x01\x28\x00\x9c\xb5\xe4\xcf\x0e\x50\x06\x5f\x5f\x74\x79\x70\x65\x01\x77\x04\x74\x65\x78\x74\x28\x00\x9c\xb5\xe4\xcf\x0e\x50\x08\x5f\x5f\x66\x6f\x72\x6d\x61\x74\x01\x7d\x00\x28\x00\x9c\xb5\xe4\xcf\x0e\x50\x07\x5f\x5f\x73\x74\x79\x6c\x65\x01\x77\x00\x28\x00\x9c\xb5\xe4\xcf\x0e\x50\x06\x5f\x5f\x6d\x6f\x64\x65\x01\x7d\x00\x28\x00\x9c\xb5\xe4\xcf\x0e\x50\x08\x5f\x5f\x64\x65\x74\x61\x69\x6c\x01\x7d\x00\x84\x9c\xb5\xe4\xcf\x0e\x50\x01\x64\x81\x9c\xb5\xe4\xcf\x0e\x49\x01\x00\x05\x81\x9c\xb5\xe4\xcf\x0e\x3b\x01\x00\x05\xa8\x9c\xb5\xe4\xcf\x0e\x3f\x01\x7e\x87\x9c\xb5\xe4\xcf\x0e\x0d\x06\x28\x00\x9c\xb5\xe4\xcf\x0e\x64\x06\x5f\x5f\x74\x79\x70\x65\x01\x77\x09\x70\x61\x72\x61\x67\x72\x61\x70\x68\x28\x00\x9c\xb5\xe4\xcf\x0e\x64\x08\x5f\x5f\x66\x6f\x72\x6d\x61\x74\x01\x7d\x00\x28\x00\x9c\xb5\xe4\xcf\x0e\x64\x08\x5f\x5f\x69\x6e\x64\x65\x6e\x74\x01\x7d\x00\x21\x00\x9c\xb5\xe4\xcf\x0e\x64\x05\x5f\x5f\x64\x69\x72\x01\xa8\x9c\xb5\xe4\xcf\x0e\x68\x01\x77\x03\x6c\x74\x72\x07\x00\x9c\xb5\xe4\xcf\x0e\x64\x01\x28\x00\x9c\xb5\xe4\xcf\x0e\x6a\x06\x5f\x5f\x74\x79\x70\x65\x01\x77\x04\x74\x65\x78\x74\x28\x00\x9c\xb5\xe4\xcf\x0e\x6a\x08\x5f\x5f\x66\x6f\x72\x6d\x61\x74\x01\x7d\x00\x28\x00\x9c\xb5\xe4\xcf\x0e\x6a\x07\x5f\x5f\x73\x74\x79\x6c\x65\x01\x77\x00\x28\x00\x9c\xb5\xe4\xcf\x0e\x6a\x06\x5f\x5f\x6d\x6f\x64\x65\x01\x7d\x00\x28\x00\x9c\xb5\xe4\xcf\x0e\x6a\x08\x5f\x5f\x64\x65\x74\x61\x69\x6c\x01\x7d\x00\x84\x9c\xb5\xe4\xcf\x0e\x6a\x01\x65\x01\x9c\xb5\xe4\xcf\x0e\x09\x11\x01\x19\x01\x1b\x07\x2a\x02\x35\x06\x3f\x01\x4d\x01\x57\x0c\x68\x01".to_vec();
        let expected_json: Value = json!({
            "__dir": "ltr",
            "children": [
                {
                    "__type": "paragraph",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "children": [
                        {
                            "__type": "text",
                            "__format": 0,
                            "__style": "",
                            "__mode": 0,
                            "__detail": 0,
                            "text": "a "
                        },
                        {
                            "__type": "text",
                            "__format": 1,
                            "__style": "",
                            "__mode": 0,
                            "__detail": 0,
                            "text": "b"
                        }
                    ]
                },
                {
                    "__type": "list",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__listType": "number",
                    "__tag": "ol",
                    "__start": 1,
                    "children": [
                        {
                            "__type": "listitem",
                            "__format": 0,
                            "__indent": 0,
                            "__dir": "ltr",
                            "__value": 1,
                            "children": [
                                {
                                    "__type": "text",
                                    "__format": 0,
                                    "__style": "",
                                    "__mode": 0,
                                    "__detail": 0,
                                    "text": "c"
                                }
                            ]
                        },
                        {
                            "__type": "listitem",
                            "__format": 0,
                            "__indent": 0,
                            "__dir": null,
                            "__value": 2,
                            "children": [
                                {
                                    "__type": "list",
                                    "__format": 0,
                                    "__indent": 0,
                                    "__dir": "ltr",
                                    "__listType": "number",
                                    "__tag": "ol",
                                    "__start": 1,
                                    "children": [
                                        {
                                            "__type": "listitem",
                                            "__format": 0,
                                            "__indent": 0,
                                            "__dir": "ltr",
                                            "__value": 1,
                                            "children": [
                                                {
                                                    "__type": "text",
                                                    "__format": 0,
                                                    "__style": "",
                                                    "__mode": 0,
                                                    "__detail": 0,
                                                    "text": "d"
                                                }
                                            ]
                                        }
                                    ]
                                }
                            ]
                        }
                    ]
                },
                {
                    "__type": "paragraph",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "children": [
                        {
                            "__type": "text",
                            "__format": 0,
                            "__style": "",
                            "__mode": 0,
                            "__detail": 0,
                            "text": "e"
                        }
                    ]
                }
            ]
        });

        let result = process_doc(update_bytes);
        let mut result_buf = String::new();

        Any::Map(Box::new(result)).to_json(&mut result_buf);
        let result_json: Value = from_str(&result_buf).unwrap();

        println!("Result:\n{}", to_string_pretty(&result_json).unwrap());

        assert_json_eq!(result_json, expected_json);
    }
}
