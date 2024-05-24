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

pub fn process_xml_fragment(diff: Vec<u8>) -> HashMap<String, Any> {
    let mut result: HashMap<String, Any> = HashMap::new();
    let doc: Doc = Doc::new();
    let xml_fragment_root: XmlFragmentRef = doc.get_or_insert_xml_fragment("root");
    doc.transact_mut()
        .apply_update(Update::decode_v1(diff.as_slice()).unwrap());
    let txn: Transaction = doc.transact();

    // Update attributes of the root XmlFragment
    let xml_fragment_root_map: MapRef = xml_fragment_root.clone().into();
    if let Any::Map(at) = xml_fragment_root_map.to_json(&txn) {
        for (k, v) in at.iter() {
            result.insert(k.to_string(), v.clone());
        }
    }

    // Process the children of the root XmlFragment
    process_xml_node(&txn, &mut result, xml_fragment_root.first_child());

    result
}

#[pyfunction]
pub fn update_to_nodes(diff: Vec<u8>) -> PyObject {
    let result = process_xml_fragment(diff);

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
    use crate::y_doc::process_xml_fragment;
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

        let result = process_xml_fragment(update_bytes);
        let mut result_buf = String::new();

        Any::Map(Box::new(result)).to_json(&mut result_buf);
        let result_json: Value = from_str(&result_buf).unwrap();

        println!("Result:\n{}", to_string_pretty(&result_json).unwrap());

        assert_json_eq!(result_json, expected_json);
    }

    #[test]
    fn parse_nested_xml_text_nodes_of_long_checklist() {
        let update_bytes: Vec<u8> = b"\x01\x9d\x07\x9e\xa8\xf0\xe9\x0f\x00(\x01\x04root\x05__dir\x01w\x03ltr\x07\x01\x04root\x06(\x00\x9e\xa8\xf0\xe9\x0f\x01\x06__type\x01w\x04list(\x00\x9e\xa8\xf0\xe9\x0f\x01\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x01\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x01\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\x01\n__listType\x01w\x05check(\x00\x9e\xa8\xf0\xe9\x0f\x01\x05__tag\x01w\x02ul(\x00\x9e\xa8\xf0\xe9\x0f\x01\x07__start\x01}\x01\x07\x00\x9e\xa8\xf0\xe9\x0f\x01\x06(\x00\x9e\xa8\xf0\xe9\x0f\t\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\t\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\t\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\t\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\t\x07__value\x01}\x01(\x00\x9e\xa8\xf0\xe9\x0f\t\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\t\x01(\x00\x9e\xa8\xf0\xe9\x0f\x10\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\x10\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x10\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\x10\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x10\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\x10)color change failed for newly created tag\x87\x9e\xa8\xf0\xe9\x0f\t\x06(\x00\x9e\xa8\xf0\xe9\x0f?\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f?\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f?\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f?\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f?\x07__value\x01}\x02(\x00\x9e\xa8\xf0\xe9\x0f?\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f?\x01(\x00\x9e\xa8\xf0\xe9\x0fF\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0fF\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0fF\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0fF\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0fF\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0fF2convert local storage event listener to usestorage\x87\x9e\xa8\xf0\xe9\x0f?\x06(\x00\x9e\xa8\xf0\xe9\x0f~\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f~\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f~\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f~\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f~\x07__value\x01}\x03(\x00\x9e\xa8\xf0\xe9\x0f~\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f~\x01(\x00\x9e\xa8\xf0\xe9\x0f\x85\x01\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\x85\x01\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x85\x01\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\x85\x01\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x85\x01\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\x85\x01\\remove sorts and filters from the list headers and rework those a bit to be less complicated\x87\x9e\xa8\xf0\xe9\x0f~\x06(\x00\x9e\xa8\xf0\xe9\x0f\xe7\x01\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xe7\x01\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xe7\x01\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xe7\x01\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xe7\x01\x07__value\x01}\x04(\x00\x9e\xa8\xf0\xe9\x0f\xe7\x01\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xe7\x01\x01(\x00\x9e\xa8\xf0\xe9\x0f\xee\x01\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xee\x01\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xee\x01\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xee\x01\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xee\x01\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xee\x01%title of tab still says \"set up Dart\"\x87\x9e\xa8\xf0\xe9\x0f\xe7\x01\x06(\x00\x9e\xa8\xf0\xe9\x0f\x99\x02\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\x99\x02\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x99\x02\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x99\x02\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\x99\x02\x07__value\x01}\x05(\x00\x9e\xa8\xf0\xe9\x0f\x99\x02\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\x99\x02\x01(\x00\x9e\xa8\xf0\xe9\x0f\xa0\x02\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xa0\x02\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xa0\x02\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xa0\x02\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xa0\x02\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xa0\x026recent tasks doesn\'t seem to be ordered by most recent\x87\x9e\xa8\xf0\xe9\x0f\x99\x02\x06(\x00\x9e\xa8\xf0\xe9\x0f\xdc\x02\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xdc\x02\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xdc\x02\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xdc\x02\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xdc\x02\x07__value\x01}\x06(\x00\x9e\xa8\xf0\xe9\x0f\xdc\x02\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xdc\x02\x01(\x00\x9e\xa8\xf0\xe9\x0f\xe3\x02\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xe3\x02\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xe3\x02\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xe3\x02\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xe3\x02\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xe3\x02@sync new tailwind names with stuff defined in ~/constants/styles\x87\x9e\xa8\xf0\xe9\x0f\xdc\x02\x06(\x00\x9e\xa8\xf0\xe9\x0f\xa9\x03\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xa9\x03\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xa9\x03\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xa9\x03\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xa9\x03\x07__value\x01}\x07(\x00\x9e\xa8\xf0\xe9\x0f\xa9\x03\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xa9\x03\x01(\x00\x9e\xa8\xf0\xe9\x0f\xb0\x03\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xb0\x03\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb0\x03\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb0\x03\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb0\x03\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xb0\x03Pit\'d be nice to get a notification or something when deployment is actually done\x87\x9e\xa8\xf0\xe9\x0f\xa9\x03\x06(\x00\x9e\xa8\xf0\xe9\x0f\x86\x04\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\x86\x04\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x86\x04\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x86\x04\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\x86\x04\x07__value\x01}\x08(\x00\x9e\xa8\xf0\xe9\x0f\x86\x04\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\x86\x04\x01(\x00\x9e\xa8\xf0\xe9\x0f\x8d\x04\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\x8d\x04\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x8d\x04\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\x8d\x04\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x8d\x04\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\x8d\x04\x19right click column header\x87\x9e\xa8\xf0\xe9\x0f\x86\x04\x06(\x00\x9e\xa8\xf0\xe9\x0f\xac\x04\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xac\x04\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xac\x04\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xac\x04\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xac\x04\x07__value\x01}\t(\x00\x9e\xa8\xf0\xe9\x0f\xac\x04\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xac\x04\x01(\x00\x9e\xa8\xf0\xe9\x0f\xb3\x04\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xb3\x04\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb3\x04\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb3\x04\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb3\x04\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xb3\x04=should have option to hide status for sharable views at least\x87\x9e\xa8\xf0\xe9\x0f\xac\x04\x06(\x00\x9e\xa8\xf0\xe9\x0f\xf6\x04\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xf6\x04\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xf6\x04\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xf6\x04\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xf6\x04\x07__value\x01}\n(\x00\x9e\xa8\xf0\xe9\x0f\xf6\x04\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xf6\x04\x01(\x00\x9e\xa8\xf0\xe9\x0f\xfd\x04\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xfd\x04\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xfd\x04\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xfd\x04\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xfd\x04\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xfd\x04<shouldn\'t have option to hide dartboard column if it\'s shown\x87\x9e\xa8\xf0\xe9\x0f\xf6\x04\x06(\x00\x9e\xa8\xf0\xe9\x0f\xbf\x05\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xbf\x05\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xbf\x05\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xbf\x05\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xbf\x05\x07__value\x01}\x0b(\x00\x9e\xa8\xf0\xe9\x0f\xbf\x05\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xbf\x05\x01(\x00\x9e\xa8\xf0\xe9\x0f\xc6\x05\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xc6\x05\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xc6\x05\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xc6\x05\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xc6\x05\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xc6\x05Jwhen you first join a lot of other tools, they put you in a personal space\x87\x9e\xa8\xf0\xe9\x0f\xbf\x05\x06(\x00\x9e\xa8\xf0\xe9\x0f\x96\x06\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\x96\x06\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x96\x06\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x96\x06\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\x96\x06\x07__value\x01}\x0c(\x00\x9e\xa8\xf0\xe9\x0f\x96\x06\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\x96\x06\x01(\x00\x9e\xa8\xf0\xe9\x0f\x9d\x06\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\x9d\x06\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x9d\x06\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\x9d\x06\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x9d\x06\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\x9d\x06*move most of the local storage stuff to BE\x87\x9e\xa8\xf0\xe9\x0f\x96\x06\x06(\x00\x9e\xa8\xf0\xe9\x0f\xcd\x06\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xcd\x06\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xcd\x06\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xcd\x06\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xcd\x06\x07__value\x01}\r(\x00\x9e\xa8\xf0\xe9\x0f\xcd\x06\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xcd\x06\x01(\x00\x9e\xa8\xf0\xe9\x0f\xd4\x06\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xd4\x06\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xd4\x06\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xd4\x06\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xd4\x06\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xd4\x062there are a lot of tasks with deleted dartboards: \x87\x9e\xa8\xf0\xe9\x0f\x8b\x07\x01(\x00\x9e\xa8\xf0\xe9\x0f\x8c\x07\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\x8c\x07\x08__format\x01}\x10(\x00\x9e\xa8\xf0\xe9\x0f\x8c\x07\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\x8c\x07\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x8c\x07\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\x8c\x073Task.hidden_manager.filter(dartboard__deleted=True)\x87\x9e\xa8\xf0\xe9\x0f\xcd\x06\x06(\x00\x9e\xa8\xf0\xe9\x0f\xc5\x07\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xc5\x07\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xc5\x07\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xc5\x07\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xc5\x07\x07__value\x01}\x0e(\x00\x9e\xa8\xf0\xe9\x0f\xc5\x07\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xc5\x07\x01(\x00\x9e\xa8\xf0\xe9\x0f\xcc\x07\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xcc\x07\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xcc\x07\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xcc\x07\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xcc\x07\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xcc\x07\x10limit image size\x87\x9e\xa8\xf0\xe9\x0f\xc5\x07\x06(\x00\x9e\xa8\xf0\xe9\x0f\xe2\x07\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xe2\x07\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xe2\x07\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xe2\x07\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xe2\x07\x07__value\x01}\x0f(\x00\x9e\xa8\xf0\xe9\x0f\xe2\x07\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xe2\x07\x01(\x00\x9e\xa8\xf0\xe9\x0f\xe9\x07\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xe9\x07\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xe9\x07\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xe9\x07\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xe9\x07\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xe9\x07fgetting a bit of a collapse when making a new modal in the SEM, probably from the button at the bottom\x87\x9e\xa8\xf0\xe9\x0f\xe2\x07\x06(\x00\x9e\xa8\xf0\xe9\x0f\xd5\x08\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xd5\x08\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xd5\x08\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xd5\x08\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xd5\x08\x07__value\x01}\x10(\x00\x9e\xa8\xf0\xe9\x0f\xd5\x08\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xd5\x08\x01(\x00\x9e\xa8\xf0\xe9\x0f\xdc\x08\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xdc\x08\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xdc\x08\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xdc\x08\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xdc\x08\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xdc\x08\xb3\x01dartboard is hard-on in list for view, should be disableable or at least shown and locked. whatever it is, same in RM. then make sure for RM it doesn\'t flow through to public view\x87\x9e\xa8\xf0\xe9\x0f\xd5\x08\x06(\x00\x9e\xa8\xf0\xe9\x0f\x95\n\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\x95\n\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x95\n\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x95\n\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\x95\n\x07__value\x01}\x11(\x00\x9e\xa8\xf0\xe9\x0f\x95\n\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\x95\n\x01(\x00\x9e\xa8\xf0\xe9\x0f\x9c\n\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\x9c\n\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x9c\n\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\x9c\n\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x9c\n\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\x9c\n;when dragging the LB for example, need to move the tooltips\x87\x9e\xa8\xf0\xe9\x0f\x95\n\x06(\x00\x9e\xa8\xf0\xe9\x0f\xdd\n\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xdd\n\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xdd\n\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xdd\n\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xdd\n\x07__value\x01}\x12(\x00\x9e\xa8\xf0\xe9\x0f\xdd\n\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xdd\n\x01(\x00\x9e\xa8\xf0\xe9\x0f\xe4\n\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xe4\n\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xe4\n\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xe4\n\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xe4\n\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xe4\n&doc titles can overflow in folder view\x87\x9e\xa8\xf0\xe9\x0f\xdd\n\x06(\x00\x9e\xa8\xf0\xe9\x0f\x90\x0b\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\x90\x0b\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x90\x0b\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x90\x0b\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\x90\x0b\x07__value\x01}\x13(\x00\x9e\xa8\xf0\xe9\x0f\x90\x0b\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\x90\x0b\x01(\x00\x9e\xa8\xf0\xe9\x0f\x97\x0b\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\x97\x0b\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x97\x0b\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\x97\x0b\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x97\x0b\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\x97\x0b)really need to make RB and LB pixel-based\x87\x9e\xa8\xf0\xe9\x0f\x90\x0b\x06(\x00\x9e\xa8\xf0\xe9\x0f\xc6\x0b\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xc6\x0b\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xc6\x0b\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xc6\x0b\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xc6\x0b\x07__value\x01}\x14(\x00\x9e\xa8\xf0\xe9\x0f\xc6\x0b\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xc6\x0b\x01(\x00\x9e\xa8\xf0\xe9\x0f\xcd\x0b\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xcd\x0b\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xcd\x0b\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xcd\x0b\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xcd\x0b\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xcd\x0b*more RB title editing performance in board\x87\x9e\xa8\xf0\xe9\x0f\xc6\x0b\x06(\x00\x9e\xa8\xf0\xe9\x0f\xfd\x0b\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xfd\x0b\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xfd\x0b\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xfd\x0b\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xfd\x0b\x07__value\x01}\x15(\x00\x9e\xa8\xf0\xe9\x0f\xfd\x0b\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xfd\x0b\x01(\x00\x9e\xa8\xf0\xe9\x0f\x84\x0c\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\x84\x0c\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x84\x0c\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\x84\x0c\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x84\x0c\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\x84\x0c\x0cbad lexical \x87\x9e\xa8\xf0\xe9\x0f\x95\x0c\x06(\x00\x9e\xa8\xf0\xe9\x0f\x96\x0c\x06__type\x01w\x04link(\x00\x9e\xa8\xf0\xe9\x0f\x96\x0c\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x96\x0c\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x96\x0c\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\x96\x0c\x05__url\x01w-https://its-dart.sentry.io/issues/5312404137/(\x00\x9e\xa8\xf0\xe9\x0f\x96\x0c\x08__target\x01~(\x00\x9e\xa8\xf0\xe9\x0f\x96\x0c\x05__rel\x01~(\x00\x9e\xa8\xf0\xe9\x0f\x96\x0c\x07__title\x01~\x07\x00\x9e\xa8\xf0\xe9\x0f\x96\x0c\x01(\x00\x9e\xa8\xf0\xe9\x0f\x9f\x0c\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\x9f\x0c\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x9f\x0c\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\x9f\x0c\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x9f\x0c\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\x9f\x0c-https://its-dart.sentry.io/issues/5312404137/\x87\x9e\xa8\xf0\xe9\x0f\xfd\x0b\x06(\x00\x9e\xa8\xf0\xe9\x0f\xd2\x0c\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xd2\x0c\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xd2\x0c\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xd2\x0c\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xd2\x0c\x07__value\x01}\x16(\x00\x9e\xa8\xf0\xe9\x0f\xd2\x0c\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xd2\x0c\x01(\x00\x9e\xa8\xf0\xe9\x0f\xd9\x0c\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xd9\x0c\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xd9\x0c\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xd9\x0c\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xd9\x0c\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xd9\x0c\x80\x01locally, sign up in same account or different one with two buttons directly from start page, remove hardcoded emails for testing\x87\x9e\xa8\xf0\xe9\x0f\xd2\x0c\x06(\x00\x9e\xa8\xf0\xe9\x0f\xdf\r\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xdf\r\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xdf\r\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xdf\r\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xdf\r\x07__value\x01}\x17(\x00\x9e\xa8\xf0\xe9\x0f\xdf\r\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xdf\r\x01(\x00\x9e\xa8\xf0\xe9\x0f\xe6\r\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xe6\r\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xe6\r\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xe6\r\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xe6\r\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xe6\r!RM empty state centered and faded\x87\x9e\xa8\xf0\xe9\x0f\xdf\r\x06(\x00\x9e\xa8\xf0\xe9\x0f\x8d\x0e\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\x8d\x0e\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x8d\x0e\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x8d\x0e\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\x8d\x0e\x07__value\x01}\x18(\x00\x9e\xa8\xf0\xe9\x0f\x8d\x0e\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\x8d\x0e\x01(\x00\x9e\xa8\xf0\xe9\x0f\x94\x0e\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\x94\x0e\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x94\x0e\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\x94\x0e\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x94\x0e\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\x94\x0ePanywhere you can drag something, editing text on it you can\'t highlight and drag\x87\x9e\xa8\xf0\xe9\x0f\x8d\x0e\x06(\x00\x9e\xa8\xf0\xe9\x0f\xea\x0e\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xea\x0e\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xea\x0e\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xea\x0e\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xea\x0e\x07__value\x01}\x19(\x00\x9e\xa8\xf0\xe9\x0f\xea\x0e\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xea\x0e\x06(\x00\x9e\xa8\xf0\xe9\x0f\xf1\x0e\x06__type\x01w\x04list(\x00\x9e\xa8\xf0\xe9\x0f\xf1\x0e\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xf1\x0e\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xf1\x0e\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xf1\x0e\n__listType\x01w\x05check(\x00\x9e\xa8\xf0\xe9\x0f\xf1\x0e\x05__tag\x01w\x02ul(\x00\x9e\xa8\xf0\xe9\x0f\xf1\x0e\x07__start\x01}\x01\x07\x00\x9e\xa8\xf0\xe9\x0f\xf1\x0e\x06(\x00\x9e\xa8\xf0\xe9\x0f\xf9\x0e\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xf9\x0e\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xf9\x0e\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xf9\x0e\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xf9\x0e\x07__value\x01}\x01(\x00\x9e\xa8\xf0\xe9\x0f\xf9\x0e\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xf9\x0e\x01(\x00\x9e\xa8\xf0\xe9\x0f\x80\x0f\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\x80\x0f\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x80\x0f\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\x80\x0f\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x80\x0f\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\x80\x0f*click-dragging in titles to highlight text\x87\x9e\xa8\xf0\xe9\x0f\xea\x0e\x06(\x00\x9e\xa8\xf0\xe9\x0f\xb0\x0f\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xb0\x0f\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb0\x0f\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb0\x0f\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xb0\x0f\x07__value\x01}\x19(\x00\x9e\xa8\xf0\xe9\x0f\xb0\x0f\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xb0\x0f\x01(\x00\x9e\xa8\xf0\xe9\x0f\xb7\x0f\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xb7\x0f\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb7\x0f\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb7\x0f\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb7\x0f\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xb7\x0f.TCM bounces first time each dropdown is opened\x87\x9e\xa8\xf0\xe9\x0f\xb0\x0f\x06(\x00\x9e\xa8\xf0\xe9\x0f\xeb\x0f\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xeb\x0f\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xeb\x0f\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xeb\x0f\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xeb\x0f\x07__value\x01}\x1a(\x00\x9e\xa8\xf0\xe9\x0f\xeb\x0f\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xeb\x0f\x01(\x00\x9e\xa8\xf0\xe9\x0f\xf2\x0f\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xf2\x0f\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xf2\x0f\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xf2\x0f\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xf2\x0f\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xf2\x0f6first log in with new account causes full page refresh\x87\x9e\xa8\xf0\xe9\x0f\xeb\x0f\x06(\x00\x9e\xa8\xf0\xe9\x0f\xae\x10\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xae\x10\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xae\x10\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xae\x10\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xae\x10\x07__value\x01}\x1b(\x00\x9e\xa8\xf0\xe9\x0f\xae\x10\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xae\x10\x01(\x00\x9e\xa8\xf0\xe9\x0f\xb5\x10\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xb5\x10\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb5\x10\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb5\x10\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb5\x10\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xb5\x10drace condition on new form field means that it tries to update the default right after it is created\x87\x9e\xa8\xf0\xe9\x0f\xae\x10\x06(\x00\x9e\xa8\xf0\xe9\x0f\x9f\x11\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\x9f\x11\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x9f\x11\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x9f\x11\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\x9f\x11\x07__value\x01}\x1c(\x00\x9e\xa8\xf0\xe9\x0f\x9f\x11\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\x9f\x11\x01(\x00\x9e\xa8\xf0\xe9\x0f\xa6\x11\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xa6\x11\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xa6\x11\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xa6\x11\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xa6\x11\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xa6\x11$we are getting forced logout errors \x87\x9e\xa8\xf0\xe9\x0f\xcf\x11\x06(\x00\x9e\xa8\xf0\xe9\x0f\xd0\x11\x06__type\x01w\x04link(\x00\x9e\xa8\xf0\xe9\x0f\xd0\x11\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xd0\x11\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xd0\x11\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xd0\x11\x05__url\x01w-https://its-dart.sentry.io/issues/5026011253/(\x00\x9e\xa8\xf0\xe9\x0f\xd0\x11\x08__target\x01~(\x00\x9e\xa8\xf0\xe9\x0f\xd0\x11\x05__rel\x01~(\x00\x9e\xa8\xf0\xe9\x0f\xd0\x11\x07__title\x01~\x07\x00\x9e\xa8\xf0\xe9\x0f\xd0\x11\x01(\x00\x9e\xa8\xf0\xe9\x0f\xd9\x11\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xd9\x11\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xd9\x11\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xd9\x11\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xd9\x11\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xd9\x11-https://its-dart.sentry.io/issues/5026011253/\x87\x9e\xa8\xf0\xe9\x0f\x9f\x11\x06(\x00\x9e\xa8\xf0\xe9\x0f\x8c\x12\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\x8c\x12\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x8c\x12\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x8c\x12\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\x8c\x12\x07__value\x01}\x1d(\x00\x9e\xa8\xf0\xe9\x0f\x8c\x12\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\x8c\x12\x01(\x00\x9e\xa8\xf0\xe9\x0f\x93\x12\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\x93\x12\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x93\x12\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\x93\x12\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x93\x12\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\x93\x12\x1fdon\'t log out on basic failures\x87\x9e\xa8\xf0\xe9\x0f\x8c\x12\x06(\x00\x9e\xa8\xf0\xe9\x0f\xb8\x12\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xb8\x12\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb8\x12\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb8\x12\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xb8\x12\x07__value\x01}\x1e(\x00\x9e\xa8\xf0\xe9\x0f\xb8\x12\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xb8\x12\x01(\x00\x9e\xa8\xf0\xe9\x0f\xbf\x12\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xbf\x12\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xbf\x12\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xbf\x12\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xbf\x12\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xbf\x125enter to make new task should copy last task assignee\x87\x9e\xa8\xf0\xe9\x0f\xb8\x12\x06(\x00\x9e\xa8\xf0\xe9\x0f\xfa\x12\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xfa\x12\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xfa\x12\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xfa\x12\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xfa\x12\x07__value\x01}\x1f(\x00\x9e\xa8\xf0\xe9\x0f\xfa\x12\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xfa\x12\x01(\x00\x9e\xa8\xf0\xe9\x0f\x81\x13\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\x81\x13\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x81\x13\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\x81\x13\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x81\x13\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\x81\x13:vertical bouncing every time you switch between list views\x87\x9e\xa8\xf0\xe9\x0f\xfa\x12\x06(\x00\x9e\xa8\xf0\xe9\x0f\xc1\x13\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xc1\x13\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xc1\x13\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xc1\x13\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xc1\x13\x07__value\x01} (\x00\x9e\xa8\xf0\xe9\x0f\xc1\x13\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xc1\x13\x01(\x00\x9e\xa8\xf0\xe9\x0f\xc8\x13\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xc8\x13\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xc8\x13\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xc8\x13\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xc8\x13\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xc8\x13Xgenerated or normal subtasks in TCM sometimes don\'t get cleared when deleting the parent\x87\x9e\xa8\xf0\xe9\x0f\xc1\x13\x06(\x00\x9e\xa8\xf0\xe9\x0f\xa6\x14\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xa6\x14\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xa6\x14\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xa6\x14\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xa6\x14\x07__value\x01}!(\x00\x9e\xa8\xf0\xe9\x0f\xa6\x14\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xa6\x14\x01(\x00\x9e\xa8\xf0\xe9\x0f\xad\x14\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xad\x14\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xad\x14\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xad\x14\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xad\x14\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xad\x14\x1cthis person couldn\'t log in \x87\x9e\xa8\xf0\xe9\x0f\xa6\x14\x06(\x00\x9e\xa8\xf0\xe9\x0f\xcf\x14\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xcf\x14\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xcf\x14\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xcf\x14\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xcf\x14\x07__value\x01}\"(\x00\x9e\xa8\xf0\xe9\x0f\xcf\x14\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xcf\x14\x01(\x00\x9e\xa8\xf0\xe9\x0f\xd6\x14\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xd6\x14\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xd6\x14\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xd6\x14\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xd6\x14\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xd6\x14\x15limitless bad upload \x87\x9e\xa8\xf0\xe9\x0f\xf0\x14\x06(\x00\x9e\xa8\xf0\xe9\x0f\xf1\x14\x06__type\x01w\x04link(\x00\x9e\xa8\xf0\xe9\x0f\xf1\x14\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xf1\x14\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xf1\x14\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xf1\x14\x05__url\x01w\xd0\x01https://its-dart.sentry.io/issues/4969936381/?referrer=alert_email&alert_type=email&alert_timestamp=1707762056818&alert_rule_id=10650917&notification_uuid=f8462053-5574-4116-88a7-80c92a8ca70b&environment=prod(\x00\x9e\xa8\xf0\xe9\x0f\xf1\x14\x08__target\x01~(\x00\x9e\xa8\xf0\xe9\x0f\xf1\x14\x05__rel\x01~(\x00\x9e\xa8\xf0\xe9\x0f\xf1\x14\x07__title\x01~\x07\x00\x9e\xa8\xf0\xe9\x0f\xf1\x14\x01(\x00\x9e\xa8\xf0\xe9\x0f\xfa\x14\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xfa\x14\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xfa\x14\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xfa\x14\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xfa\x14\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xfa\x14\xd0\x01https://its-dart.sentry.io/issues/4969936381/?referrer=alert_email&alert_type=email&alert_timestamp=1707762056818&alert_rule_id=10650917&notification_uuid=f8462053-5574-4116-88a7-80c92a8ca70b&environment=prod\x87\x9e\xa8\xf0\xe9\x0f\xcf\x14\x06(\x00\x9e\xa8\xf0\xe9\x0f\xd0\x16\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xd0\x16\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xd0\x16\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xd0\x16\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xd0\x16\x07__value\x01}#(\x00\x9e\xa8\xf0\xe9\x0f\xd0\x16\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xd0\x16\x01(\x00\x9e\xa8\xf0\xe9\x0f\xd7\x16\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xd7\x16\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xd7\x16\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xd7\x16\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xd7\x16\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xd7\x16 animate onboarding modal closing\x87\x9e\xa8\xf0\xe9\x0f\xd0\x16\x06(\x00\x9e\xa8\xf0\xe9\x0f\xfd\x16\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xfd\x16\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xfd\x16\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xfd\x16\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xfd\x16\x07__value\x01}$(\x00\x9e\xa8\xf0\xe9\x0f\xfd\x16\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xfd\x16\x01(\x00\x9e\xa8\xf0\xe9\x0f\x84\x17\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\x84\x17\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x84\x17\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\x84\x17\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x84\x17\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\x84\x17(subtasks collapse in TCM when discarding\x87\x9e\xa8\xf0\xe9\x0f\xfd\x16\x06(\x00\x9e\xa8\xf0\xe9\x0f\xb2\x17\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xb2\x17\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb2\x17\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb2\x17\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xb2\x17\x07__value\x01}%(\x00\x9e\xa8\xf0\xe9\x0f\xb2\x17\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xb2\x17\x01(\x00\x9e\xa8\xf0\xe9\x0f\xb9\x17\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xb9\x17\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb9\x17\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb9\x17\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb9\x17\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xb9\x17JMM\'s trash in stag is bricked, can get in with login token and look around\x87\x9e\xa8\xf0\xe9\x0f\xb2\x17\x06(\x00\x9e\xa8\xf0\xe9\x0f\x89\x18\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\x89\x18\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x89\x18\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x89\x18\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\x89\x18\x07__value\x01}&(\x00\x9e\xa8\xf0\xe9\x0f\x89\x18\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\x89\x18\x06(\x00\x9e\xa8\xf0\xe9\x0f\x90\x18\x06__type\x01w\x04list(\x00\x9e\xa8\xf0\xe9\x0f\x90\x18\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x90\x18\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x90\x18\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\x90\x18\n__listType\x01w\x05check(\x00\x9e\xa8\xf0\xe9\x0f\x90\x18\x05__tag\x01w\x02ul(\x00\x9e\xa8\xf0\xe9\x0f\x90\x18\x07__start\x01}\x01\x07\x00\x9e\xa8\xf0\xe9\x0f\x90\x18\x06(\x00\x9e\xa8\xf0\xe9\x0f\x98\x18\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\x98\x18\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x98\x18\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x98\x18\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\x98\x18\x07__value\x01}\x01(\x00\x9e\xa8\xf0\xe9\x0f\x98\x18\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\x98\x18\x01(\x00\x9e\xa8\xf0\xe9\x0f\x9f\x18\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\x9f\x18\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x9f\x18\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\x9f\x18\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x9f\x18\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\x9f\x18!maybe export stag along with prod\x87\x9e\xa8\xf0\xe9\x0f\x89\x18\x06(\x00\x9e\xa8\xf0\xe9\x0f\xc6\x18\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xc6\x18\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xc6\x18\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xc6\x18\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xc6\x18\x07__value\x01}&(\x00\x9e\xa8\xf0\xe9\x0f\xc6\x18\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xc6\x18\x01(\x00\x9e\xa8\xf0\xe9\x0f\xcd\x18\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xcd\x18\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xcd\x18\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xcd\x18\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xcd\x18\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xcd\x184accidentally highlighting a lot of text in list view\x87\x9e\xa8\xf0\xe9\x0f\xc6\x18\x06(\x00\x9e\xa8\xf0\xe9\x0f\x87\x19\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\x87\x19\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x87\x19\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x87\x19\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\x87\x19\x07__value\x01}\'(\x00\x9e\xa8\xf0\xe9\x0f\x87\x19\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\x87\x19\x01(\x00\x9e\xa8\xf0\xe9\x0f\x8e\x19\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\x8e\x19\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x8e\x19\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\x8e\x19\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x8e\x19\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\x8e\x19,reenable up and down to get out of quick add\x87\x9e\xa8\xf0\xe9\x0f\x87\x19\x06(\x00\x9e\xa8\xf0\xe9\x0f\xc0\x19\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xc0\x19\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xc0\x19\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xc0\x19\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xc0\x19\x07__value\x01}((\x00\x9e\xa8\xf0\xe9\x0f\xc0\x19\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xc0\x19\x01(\x00\x9e\xa8\xf0\xe9\x0f\xc7\x19\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xc7\x19\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xc7\x19\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xc7\x19\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xc7\x19\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xc7\x191sign in from landing page goes crazy with qparams\x87\x9e\xa8\xf0\xe9\x0f\xc0\x19\x06(\x00\x9e\xa8\xf0\xe9\x0f\xfe\x19\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xfe\x19\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xfe\x19\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xfe\x19\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xfe\x19\x07__value\x01})(\x00\x9e\xa8\xf0\xe9\x0f\xfe\x19\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xfe\x19\x01(\x00\x9e\xa8\xf0\xe9\x0f\x85\x1a\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\x85\x1a\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x85\x1a\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\x85\x1a\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x85\x1a\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\x85\x1a+replicate task with attachment broken again\x87\x9e\xa8\xf0\xe9\x0f\xfe\x19\x06(\x00\x9e\xa8\xf0\xe9\x0f\xb6\x1a\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xb6\x1a\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb6\x1a\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb6\x1a\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xb6\x1a\x07__value\x01}*(\x00\x9e\xa8\xf0\xe9\x0f\xb6\x1a\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xb6\x1a\x01(\x00\x9e\xa8\xf0\xe9\x0f\xbd\x1a\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xbd\x1a\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xbd\x1a\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xbd\x1a\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xbd\x1a\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xbd\x1aaselecting more than just one link in the editor should show text toolbar rather than link toolbar\x87\x9e\xa8\xf0\xe9\x0f\xb6\x1a\x06(\x00\x9e\xa8\xf0\xe9\x0f\xa4\x1b\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xa4\x1b\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xa4\x1b\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xa4\x1b\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xa4\x1b\x07__value\x01}+(\x00\x9e\xa8\xf0\xe9\x0f\xa4\x1b\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xa4\x1b\x01(\x00\x9e\xa8\xf0\xe9\x0f\xab\x1b\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xab\x1b\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xab\x1b\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xab\x1b\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xab\x1b\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xab\x1b#gap size in board for various chips\x87\x9e\xa8\xf0\xe9\x0f\xa4\x1b\x06(\x00\x9e\xa8\xf0\xe9\x0f\xd4\x1b\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xd4\x1b\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xd4\x1b\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xd4\x1b\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xd4\x1b\x07__value\x01},(\x00\x9e\xa8\xf0\xe9\x0f\xd4\x1b\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xd4\x1b\x01(\x00\x9e\xa8\xf0\xe9\x0f\xdb\x1b\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xdb\x1b\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xdb\x1b\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xdb\x1b\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xdb\x1b\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xdb\x1bFboard with one line title changes height when you click into the title\x87\x9e\xa8\xf0\xe9\x0f\xd4\x1b\x06(\x00\x9e\xa8\xf0\xe9\x0f\xa7\x1c\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xa7\x1c\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xa7\x1c\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xa7\x1c\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xa7\x1c\x07__value\x01}-(\x00\x9e\xa8\xf0\xe9\x0f\xa7\x1c\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xa7\x1c\x01(\x00\x9e\xa8\xf0\xe9\x0f\xae\x1c\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xae\x1c\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xae\x1c\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xae\x1c\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xae\x1c\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xae\x1c~discard draft modals in all three places should have buttons swapped and should be more like \"do you want to save this draft?\"\x87\x9e\xa8\xf0\xe9\x0f\xa7\x1c\x06(\x00\x9e\xa8\xf0\xe9\x0f\xb2\x1d\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xb2\x1d\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb2\x1d\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb2\x1d\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xb2\x1d\x07__value\x01}.(\x00\x9e\xa8\xf0\xe9\x0f\xb2\x1d\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xb2\x1d\x01(\x00\x9e\xa8\xf0\xe9\x0f\xb9\x1d\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xb9\x1d\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb9\x1d\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb9\x1d\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb9\x1d\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xb9\x1dnwhen you keep things in the discard/keep draft menu it should close them, make sure that this works everywhere\x87\x9e\xa8\xf0\xe9\x0f\xb2\x1d\x06(\x00\x9e\xa8\xf0\xe9\x0f\xad\x1e\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xad\x1e\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xad\x1e\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xad\x1e\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xad\x1e\x07__value\x01}/(\x00\x9e\xa8\xf0\xe9\x0f\xad\x1e\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xad\x1e\x01(\x00\x9e\xa8\xf0\xe9\x0f\xb4\x1e\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xb4\x1e\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb4\x1e\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb4\x1e\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb4\x1e\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xb4\x1e\x1flinks really are opening in app\x87\x9e\xa8\xf0\xe9\x0f\xad\x1e\x06(\x00\x9e\xa8\xf0\xe9\x0f\xd9\x1e\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xd9\x1e\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xd9\x1e\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xd9\x1e\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xd9\x1e\x07__value\x01}0(\x00\x9e\xa8\xf0\xe9\x0f\xd9\x1e\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xd9\x1e\x01(\x00\x9e\xa8\xf0\xe9\x0f\xe0\x1e\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xe0\x1e\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xe0\x1e\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xe0\x1e\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xe0\x1e\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xe0\x1e0opening blocker menu caused weird page scrolling\x87\x9e\xa8\xf0\xe9\x0f\xd9\x1e\x06(\x00\x9e\xa8\xf0\xe9\x0f\x96\x1f\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\x96\x1f\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x96\x1f\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x96\x1f\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\x96\x1f\x07__value\x01}1(\x00\x9e\xa8\xf0\xe9\x0f\x96\x1f\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\x96\x1f\x01(\x00\x9e\xa8\xf0\xe9\x0f\x9d\x1f\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\x9d\x1f\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x9d\x1f\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\x9d\x1f\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\x9d\x1f\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\x9d\x1fQfor developers, refreshing and completely resetting from database sucks right now\x87\x9e\xa8\xf0\xe9\x0f\x96\x1f\x06(\x00\x9e\xa8\xf0\xe9\x0f\xf4\x1f\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xf4\x1f\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xf4\x1f\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xf4\x1f\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xf4\x1f\x07__value\x01}2(\x00\x9e\xa8\xf0\xe9\x0f\xf4\x1f\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xf4\x1f\x01(\x00\x9e\xa8\xf0\xe9\x0f\xfb\x1f\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xfb\x1f\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xfb\x1f\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xfb\x1f\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xfb\x1f\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xfb\x1f=ability to track last time someone unidled/refreshed the page\x87\x9e\xa8\xf0\xe9\x0f\xf4\x1f\x06(\x00\x9e\xa8\xf0\xe9\x0f\xbe \x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xbe \x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xbe \x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xbe \x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xbe \x07__value\x01}3(\x00\x9e\xa8\xf0\xe9\x0f\xbe \t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xbe \x01(\x00\x9e\xa8\xf0\xe9\x0f\xc5 \x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xc5 \x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xc5 \x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xc5 \x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xc5 \x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xc5 ,triple backticks not working except in local\x87\x9e\xa8\xf0\xe9\x0f\xbe \x06(\x00\x9e\xa8\xf0\xe9\x0f\xf7 \x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xf7 \x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xf7 \x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xf7 \x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xf7 \x07__value\x01}4(\x00\x9e\xa8\xf0\xe9\x0f\xf7 \t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xf7 \x01(\x00\x9e\xa8\xf0\xe9\x0f\xfe \x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xfe \x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xfe \x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xfe \x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xfe \x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xfe Qimprove error messages for operations with bad types so we can actually read them\x87\x9e\xa8\xf0\xe9\x0f\xf7 \x06(\x00\x9e\xa8\xf0\xe9\x0f\xd5!\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xd5!\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xd5!\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xd5!\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xd5!\x07__value\x01}5(\x00\x9e\xa8\xf0\xe9\x0f\xd5!\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xd5!\x06(\x00\x9e\xa8\xf0\xe9\x0f\xdc!\x06__type\x01w\x04list(\x00\x9e\xa8\xf0\xe9\x0f\xdc!\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xdc!\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xdc!\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xdc!\n__listType\x01w\x05check(\x00\x9e\xa8\xf0\xe9\x0f\xdc!\x05__tag\x01w\x02ul(\x00\x9e\xa8\xf0\xe9\x0f\xdc!\x07__start\x01}\x01\x07\x00\x9e\xa8\xf0\xe9\x0f\xdc!\x06(\x00\x9e\xa8\xf0\xe9\x0f\xe4!\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xe4!\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xe4!\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xe4!\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xe4!\x07__value\x01}\x01(\x00\x9e\xa8\xf0\xe9\x0f\xe4!\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xe4!\x06(\x00\x9e\xa8\xf0\xe9\x0f\xeb!\x06__type\x01w\x04link(\x00\x9e\xa8\xf0\xe9\x0f\xeb!\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xeb!\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xeb!\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xeb!\x05__url\x01w-https://its-dart.sentry.io/issues/5211420024/(\x00\x9e\xa8\xf0\xe9\x0f\xeb!\x08__target\x01~(\x00\x9e\xa8\xf0\xe9\x0f\xeb!\x05__rel\x01~(\x00\x9e\xa8\xf0\xe9\x0f\xeb!\x07__title\x01~\x07\x00\x9e\xa8\xf0\xe9\x0f\xeb!\x01(\x00\x9e\xa8\xf0\xe9\x0f\xf4!\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xf4!\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xf4!\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xf4!\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xf4!\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xf4!-https://its-dart.sentry.io/issues/5211420024/\x87\x9e\xa8\xf0\xe9\x0f\xe4!\x06(\x00\x9e\xa8\xf0\xe9\x0f\xa7\"\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xa7\"\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xa7\"\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xa7\"\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xa7\"\x07__value\x01}\x02(\x00\x9e\xa8\xf0\xe9\x0f\xa7\"\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xa7\"\x06(\x00\x9e\xa8\xf0\xe9\x0f\xae\"\x06__type\x01w\x04link(\x00\x9e\xa8\xf0\xe9\x0f\xae\"\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xae\"\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xae\"\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xae\"\x05__url\x01w-https://its-dart.sentry.io/issues/5211417694/(\x00\x9e\xa8\xf0\xe9\x0f\xae\"\x08__target\x01~(\x00\x9e\xa8\xf0\xe9\x0f\xae\"\x05__rel\x01~(\x00\x9e\xa8\xf0\xe9\x0f\xae\"\x07__title\x01~\x07\x00\x9e\xa8\xf0\xe9\x0f\xae\"\x01(\x00\x9e\xa8\xf0\xe9\x0f\xb7\"\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xb7\"\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb7\"\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb7\"\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xb7\"\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xb7\"-https://its-dart.sentry.io/issues/5211417694/\x87\x9e\xa8\xf0\xe9\x0f\xd5!\x06(\x00\x9e\xa8\xf0\xe9\x0f\xea\"\x06__type\x01w\x08listitem(\x00\x9e\xa8\xf0\xe9\x0f\xea\"\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xea\"\x08__indent\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xea\"\x05__dir\x01w\x03ltr(\x00\x9e\xa8\xf0\xe9\x0f\xea\"\x07__value\x01}5(\x00\x9e\xa8\xf0\xe9\x0f\xea\"\t__checked\x01y\x07\x00\x9e\xa8\xf0\xe9\x0f\xea\"\x01(\x00\x9e\xa8\xf0\xe9\x0f\xf1\"\x06__type\x01w\x04text(\x00\x9e\xa8\xf0\xe9\x0f\xf1\"\x08__format\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xf1\"\x07__style\x01w\x00(\x00\x9e\xa8\xf0\xe9\x0f\xf1\"\x06__mode\x01}\x00(\x00\x9e\xa8\xf0\xe9\x0f\xf1\"\x08__detail\x01}\x00\x84\x9e\xa8\xf0\xe9\x0f\xf1\">really long due date in card overflows vertically in a bad way\x00".to_vec();
        let expected_json: Value = json!({
            "__dir": "ltr",
            "children": [
                {
                "__type": "list",
                "__format": 0,
                "__indent": 0,
                "__dir": "ltr",
                "__listType": "check",
                "__tag": "ul",
                "__start": 1,
                "children": [
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 1,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "color change failed for newly created tag"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 2,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "convert local storage event listener to usestorage"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 3,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "remove sorts and filters from the list headers and rework those a bit to be less complicated"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 4,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "title of tab still says \"set up Dart\""
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 5,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "recent tasks doesn't seem to be ordered by most recent"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 6,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "sync new tailwind names with stuff defined in ~/constants/styles"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 7,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "it'd be nice to get a notification or something when deployment is actually done"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 8,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "right click column header"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 9,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "should have option to hide status for sharable views at least"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 10,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "shouldn't have option to hide dartboard column if it's shown"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 11,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "when you first join a lot of other tools, they put you in a personal space"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 12,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "move most of the local storage stuff to BE"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 13,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "there are a lot of tasks with deleted dartboards: "
                        },
                        {
                        "__type": "text",
                        "__format": 16,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "Task.hidden_manager.filter(dartboard__deleted=True)"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 14,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "limit image size"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 15,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "getting a bit of a collapse when making a new modal in the SEM, probably from the button at the bottom"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 16,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "dartboard is hard-on in list for view, should be disableable or at least shown and locked. whatever it is, same in RM. then make sure for RM it doesn't flow through to public view"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 17,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "when dragging the LB for example, need to move the tooltips"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 18,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "doc titles can overflow in folder view"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 19,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "really need to make RB and LB pixel-based"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 20,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "more RB title editing performance in board"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 21,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "bad lexical "
                        },
                        {
                        "__type": "link",
                        "__format": 0,
                        "__indent": 0,
                        "__dir": "ltr",
                        "__url": "https://its-dart.sentry.io/issues/5312404137/",
                        "__target": null,
                        "__rel": null,
                        "__title": null,
                        "children": [
                            {
                            "__type": "text",
                            "__format": 0,
                            "__style": "",
                            "__mode": 0,
                            "__detail": 0,
                            "text": "https://its-dart.sentry.io/issues/5312404137/"
                            }
                        ]
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 22,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "locally, sign up in same account or different one with two buttons directly from start page, remove hardcoded emails for testing"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 23,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "RM empty state centered and faded"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 24,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "anywhere you can drag something, editing text on it you can't highlight and drag"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 25,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "list",
                        "__format": 0,
                        "__indent": 0,
                        "__dir": "ltr",
                        "__listType": "check",
                        "__tag": "ul",
                        "__start": 1,
                        "children": [
                            {
                            "__type": "listitem",
                            "__format": 0,
                            "__indent": 0,
                            "__dir": "ltr",
                            "__value": 1,
                            "__checked": false,
                            "children": [
                                {
                                "__type": "text",
                                "__format": 0,
                                "__style": "",
                                "__mode": 0,
                                "__detail": 0,
                                "text": "click-dragging in titles to highlight text"
                                }
                            ]
                            }
                        ]
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 25,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "TCM bounces first time each dropdown is opened"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 26,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "first log in with new account causes full page refresh"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 27,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "race condition on new form field means that it tries to update the default right after it is created"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 28,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "we are getting forced logout errors "
                        },
                        {
                        "__type": "link",
                        "__format": 0,
                        "__indent": 0,
                        "__dir": "ltr",
                        "__url": "https://its-dart.sentry.io/issues/5026011253/",
                        "__target": null,
                        "__rel": null,
                        "__title": null,
                        "children": [
                            {
                            "__type": "text",
                            "__format": 0,
                            "__style": "",
                            "__mode": 0,
                            "__detail": 0,
                            "text": "https://its-dart.sentry.io/issues/5026011253/"
                            }
                        ]
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 29,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "don't log out on basic failures"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 30,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "enter to make new task should copy last task assignee"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 31,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "vertical bouncing every time you switch between list views"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 32,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "generated or normal subtasks in TCM sometimes don't get cleared when deleting the parent"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 33,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "this person couldn't log in "
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 34,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "limitless bad upload "
                        },
                        {
                        "__type": "link",
                        "__format": 0,
                        "__indent": 0,
                        "__dir": "ltr",
                        "__url": "https://its-dart.sentry.io/issues/4969936381/?referrer=alert_email&alert_type=email&alert_timestamp=1707762056818&alert_rule_id=10650917&notification_uuid=f8462053-5574-4116-88a7-80c92a8ca70b&environment=prod",
                        "__target": null,
                        "__rel": null,
                        "__title": null,
                        "children": [
                            {
                            "__type": "text",
                            "__format": 0,
                            "__style": "",
                            "__mode": 0,
                            "__detail": 0,
                            "text": "https://its-dart.sentry.io/issues/4969936381/?referrer=alert_email&alert_type=email&alert_timestamp=1707762056818&alert_rule_id=10650917&notification_uuid=f8462053-5574-4116-88a7-80c92a8ca70b&environment=prod"
                            }
                        ]
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 35,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "animate onboarding modal closing"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 36,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "subtasks collapse in TCM when discarding"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 37,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "MM's trash in stag is bricked, can get in with login token and look around"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 38,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "list",
                        "__format": 0,
                        "__indent": 0,
                        "__dir": "ltr",
                        "__listType": "check",
                        "__tag": "ul",
                        "__start": 1,
                        "children": [
                            {
                            "__type": "listitem",
                            "__format": 0,
                            "__indent": 0,
                            "__dir": "ltr",
                            "__value": 1,
                            "__checked": false,
                            "children": [
                                {
                                "__type": "text",
                                "__format": 0,
                                "__style": "",
                                "__mode": 0,
                                "__detail": 0,
                                "text": "maybe export stag along with prod"
                                }
                            ]
                            }
                        ]
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 38,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "accidentally highlighting a lot of text in list view"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 39,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "reenable up and down to get out of quick add"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 40,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "sign in from landing page goes crazy with qparams"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 41,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "replicate task with attachment broken again"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 42,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "selecting more than just one link in the editor should show text toolbar rather than link toolbar"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 43,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "gap size in board for various chips"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 44,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "board with one line title changes height when you click into the title"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 45,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "discard draft modals in all three places should have buttons swapped and should be more like \"do you want to save this draft?\""
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 46,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "when you keep things in the discard/keep draft menu it should close them, make sure that this works everywhere"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 47,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "links really are opening in app"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 48,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "opening blocker menu caused weird page scrolling"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 49,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "for developers, refreshing and completely resetting from database sucks right now"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 50,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "ability to track last time someone unidled/refreshed the page"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 51,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "triple backticks not working except in local"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 52,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "improve error messages for operations with bad types so we can actually read them"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 53,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "list",
                        "__format": 0,
                        "__indent": 0,
                        "__dir": "ltr",
                        "__listType": "check",
                        "__tag": "ul",
                        "__start": 1,
                        "children": [
                            {
                            "__type": "listitem",
                            "__format": 0,
                            "__indent": 0,
                            "__dir": "ltr",
                            "__value": 1,
                            "__checked": false,
                            "children": [
                                {
                                "__type": "link",
                                "__format": 0,
                                "__indent": 0,
                                "__dir": "ltr",
                                "__url": "https://its-dart.sentry.io/issues/5211420024/",
                                "__target": null,
                                "__rel": null,
                                "__title": null,
                                "children": [
                                    {
                                    "__type": "text",
                                    "__format": 0,
                                    "__style": "",
                                    "__mode": 0,
                                    "__detail": 0,
                                    "text": "https://its-dart.sentry.io/issues/5211420024/"
                                    }
                                ]
                                }
                            ]
                            },
                            {
                            "__type": "listitem",
                            "__format": 0,
                            "__indent": 0,
                            "__dir": "ltr",
                            "__value": 2,
                            "__checked": false,
                            "children": [
                                {
                                "__type": "link",
                                "__format": 0,
                                "__indent": 0,
                                "__dir": "ltr",
                                "__url": "https://its-dart.sentry.io/issues/5211417694/",
                                "__target": null,
                                "__rel": null,
                                "__title": null,
                                "children": [
                                    {
                                    "__type": "text",
                                    "__format": 0,
                                    "__style": "",
                                    "__mode": 0,
                                    "__detail": 0,
                                    "text": "https://its-dart.sentry.io/issues/5211417694/"
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
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 53,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "really long due date in card overflows vertically in a bad way"
                        }
                    ]
                    }
                ]
                }
            ]
        });

        let result = process_xml_fragment(update_bytes);
        let mut result_buf = String::new();

        Any::Map(Box::new(result)).to_json(&mut result_buf);
        let result_json: Value = from_str(&result_buf).unwrap();

        println!("Result:\n{}", to_string_pretty(&result_json).unwrap());

        assert_json_eq!(result_json, expected_json);
    }

    #[test]
    fn parse_nested_xml_text_nodes_of_arbitrary_formatted_text() {
        let update_bytes: Vec<u8> = b"\x01\x9e\x05\xad\x83\x8c\xbd\r\x00(\x01\x04root\x05__dir\x01w\x03ltr\x07\x01\x04root\x06(\x00\xad\x83\x8c\xbd\r\x01\x06__type\x01w\x07heading(\x00\xad\x83\x8c\xbd\r\x01\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\x01\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\x01\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\x01\x05__tag\x01w\x02h1\x07\x00\xad\x83\x8c\xbd\r\x01\x01(\x00\xad\x83\x8c\xbd\r\x07\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\x07\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\x07\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\x07\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\x07\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\x07\x02H1\x87\xad\x83\x8c\xbd\r\x01\x06(\x00\xad\x83\x8c\xbd\r\x0f\x06__type\x01w\tparagraph(\x00\xad\x83\x8c\xbd\r\x0f\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\x0f\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\x0f\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\x0f\x0c__textFormat\x01}\x00\x07\x00\xad\x83\x8c\xbd\r\x0f\x01(\x00\xad\x83\x8c\xbd\r\x15\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\x15\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\x15\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\x15\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\x15\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\x15\x17underneath, a paragraph\x87\xad\x83\x8c\xbd\r\x0f\x06(\x00\xad\x83\x8c\xbd\r2\x06__type\x01w\x07heading(\x00\xad\x83\x8c\xbd\r2\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r2\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r2\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r2\x05__tag\x01w\x02h2\x07\x00\xad\x83\x8c\xbd\r2\x01(\x00\xad\x83\x8c\xbd\r8\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r8\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r8\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r8\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r8\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r8\x02H2\x87\xad\x83\x8c\xbd\r2\x06(\x00\xad\x83\x8c\xbd\r@\x06__type\x01w\x07heading(\x00\xad\x83\x8c\xbd\r@\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r@\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r@\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r@\x05__tag\x01w\x02h2\x07\x00\xad\x83\x8c\xbd\r@\x01(\x00\xad\x83\x8c\xbd\rF\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\rF\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\rF\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\rF\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\rF\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\rF\tSecond H2\x87\xad\x83\x8c\xbd\r@\x06(\x00\xad\x83\x8c\xbd\rU\x06__type\x01w\tparagraph(\x00\xad\x83\x8c\xbd\rU\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\rU\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\rU\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\rU\x0c__textFormat\x01}\x00\x07\x00\xad\x83\x8c\xbd\rU\x01(\x00\xad\x83\x8c\xbd\r[\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r[\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r[\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r[\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r[\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r[\x0csome content\x87\xad\x83\x8c\xbd\rU\x06(\x00\xad\x83\x8c\xbd\rm\x06__type\x01w\tparagraph(\x00\xad\x83\x8c\xbd\rm\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\rm\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\rm\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\rm\x0c__textFormat\x01}\x00\x07\x00\xad\x83\x8c\xbd\rm\x01(\x00\xad\x83\x8c\xbd\rs\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\rs\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\rs\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\rs\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\rs\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\rs\x08a toggle\x87\xad\x83\x8c\xbd\rm\x06(\x00\xad\x83\x8c\xbd\r\x81\x01\x06__type\x01w\tparagraph(\x00\xad\x83\x8c\xbd\r\x81\x01\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\x81\x01\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\x81\x01\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\x81\x01\x0c__textFormat\x01}\x00\x07\x00\xad\x83\x8c\xbd\r\x81\x01\x01(\x00\xad\x83\x8c\xbd\r\x87\x01\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\x87\x01\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\x87\x01\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\x87\x01\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\x87\x01\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\x87\x01\x0cwith content\x87\xad\x83\x8c\xbd\r\x81\x01\x06(\x00\xad\x83\x8c\xbd\r\x99\x01\x06__type\x01w\x07heading(\x00\xad\x83\x8c\xbd\r\x99\x01\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\x99\x01\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\x99\x01\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\x99\x01\x05__tag\x01w\x02h1\x07\x00\xad\x83\x8c\xbd\r\x99\x01\x01(\x00\xad\x83\x8c\xbd\r\x9f\x01\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\x9f\x01\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\x9f\x01\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\x9f\x01\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\x9f\x01\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\x9f\x01\tSecond h1\x87\xad\x83\x8c\xbd\r\x99\x01\x06(\x00\xad\x83\x8c\xbd\r\xae\x01\x06__type\x01w\x04list(\x00\xad\x83\x8c\xbd\r\xae\x01\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xae\x01\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xae\x01\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\xae\x01\n__listType\x01w\x06bullet(\x00\xad\x83\x8c\xbd\r\xae\x01\x05__tag\x01w\x02ul(\x00\xad\x83\x8c\xbd\r\xae\x01\x07__start\x01}\x01\x07\x00\xad\x83\x8c\xbd\r\xae\x01\x06(\x00\xad\x83\x8c\xbd\r\xb6\x01\x06__type\x01w\x08listitem(\x00\xad\x83\x8c\xbd\r\xb6\x01\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xb6\x01\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xb6\x01\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\xb6\x01\x07__value\x01}\x01\x07\x00\xad\x83\x8c\xbd\r\xb6\x01\x01(\x00\xad\x83\x8c\xbd\r\xbc\x01\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\xbc\x01\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xbc\x01\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\xbc\x01\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\xbc\x01\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\xbc\x01\rbulleted list\x87\xad\x83\x8c\xbd\r\xb6\x01\x06(\x00\xad\x83\x8c\xbd\r\xcf\x01\x06__type\x01w\x08listitem(\x00\xad\x83\x8c\xbd\r\xcf\x01\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xcf\x01\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xcf\x01\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\xcf\x01\x07__value\x01}\x02\x07\x00\xad\x83\x8c\xbd\r\xcf\x01\x06(\x00\xad\x83\x8c\xbd\r\xd5\x01\x06__type\x01w\x04list(\x00\xad\x83\x8c\xbd\r\xd5\x01\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xd5\x01\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xd5\x01\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\xd5\x01\n__listType\x01w\x06bullet(\x00\xad\x83\x8c\xbd\r\xd5\x01\x05__tag\x01w\x02ul(\x00\xad\x83\x8c\xbd\r\xd5\x01\x07__start\x01}\x01\x07\x00\xad\x83\x8c\xbd\r\xd5\x01\x06(\x00\xad\x83\x8c\xbd\r\xdd\x01\x06__type\x01w\x08listitem(\x00\xad\x83\x8c\xbd\r\xdd\x01\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xdd\x01\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xdd\x01\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\xdd\x01\x07__value\x01}\x01\x07\x00\xad\x83\x8c\xbd\r\xdd\x01\x01(\x00\xad\x83\x8c\xbd\r\xe3\x01\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\xe3\x01\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xe3\x01\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\xe3\x01\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\xe3\x01\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\xe3\x01\x08indented\x87\xad\x83\x8c\xbd\r\xdd\x01\x06(\x00\xad\x83\x8c\xbd\r\xf1\x01\x06__type\x01w\x08listitem(\x00\xad\x83\x8c\xbd\r\xf1\x01\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xf1\x01\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xf1\x01\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\xf1\x01\x07__value\x01}\x02\x07\x00\xad\x83\x8c\xbd\r\xf1\x01\x06(\x00\xad\x83\x8c\xbd\r\xf7\x01\x06__type\x01w\x04list(\x00\xad\x83\x8c\xbd\r\xf7\x01\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xf7\x01\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xf7\x01\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\xf7\x01\n__listType\x01w\x06bullet(\x00\xad\x83\x8c\xbd\r\xf7\x01\x05__tag\x01w\x02ul(\x00\xad\x83\x8c\xbd\r\xf7\x01\x07__start\x01}\x01\x07\x00\xad\x83\x8c\xbd\r\xf7\x01\x06(\x00\xad\x83\x8c\xbd\r\xff\x01\x06__type\x01w\x08listitem(\x00\xad\x83\x8c\xbd\r\xff\x01\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xff\x01\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xff\x01\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\xff\x01\x07__value\x01}\x01\x07\x00\xad\x83\x8c\xbd\r\xff\x01\x01(\x00\xad\x83\x8c\xbd\r\x85\x02\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\x85\x02\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\x85\x02\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\x85\x02\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\x85\x02\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\x85\x02\x06deeply\x87\xad\x83\x8c\xbd\r\xcf\x01\x06(\x00\xad\x83\x8c\xbd\r\x91\x02\x06__type\x01w\x08listitem(\x00\xad\x83\x8c\xbd\r\x91\x02\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\x91\x02\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\x91\x02\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\x91\x02\x07__value\x01}\x02\x07\x00\xad\x83\x8c\xbd\r\x91\x02\x01(\x00\xad\x83\x8c\xbd\r\x97\x02\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\x97\x02\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\x97\x02\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\x97\x02\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\x97\x02\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\x97\x02\x0canother item\x87\xad\x83\x8c\xbd\r\xae\x01\x06(\x00\xad\x83\x8c\xbd\r\xa9\x02\x06__type\x01w\x07heading(\x00\xad\x83\x8c\xbd\r\xa9\x02\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xa9\x02\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xa9\x02\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\xa9\x02\x05__tag\x01w\x02h2\x07\x00\xad\x83\x8c\xbd\r\xa9\x02\x01(\x00\xad\x83\x8c\xbd\r\xaf\x02\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\xaf\x02\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xaf\x02\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\xaf\x02\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\xaf\x02\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\xaf\x02\x02H2\x87\xad\x83\x8c\xbd\r\xa9\x02\x06(\x00\xad\x83\x8c\xbd\r\xb7\x02\x06__type\x01w\x07heading(\x00\xad\x83\x8c\xbd\r\xb7\x02\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xb7\x02\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xb7\x02\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\xb7\x02\x05__tag\x01w\x02h3\x07\x00\xad\x83\x8c\xbd\r\xb7\x02\x01(\x00\xad\x83\x8c\xbd\r\xbd\x02\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\xbd\x02\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xbd\x02\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\xbd\x02\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\xbd\x02\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\xbd\x02\x02H3\x87\xad\x83\x8c\xbd\r\xb7\x02\x06(\x00\xad\x83\x8c\xbd\r\xc5\x02\x06__type\x01w\x04list(\x00\xad\x83\x8c\xbd\r\xc5\x02\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xc5\x02\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xc5\x02\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\xc5\x02\n__listType\x01w\x06number(\x00\xad\x83\x8c\xbd\r\xc5\x02\x05__tag\x01w\x02ol(\x00\xad\x83\x8c\xbd\r\xc5\x02\x07__start\x01}\x01\x07\x00\xad\x83\x8c\xbd\r\xc5\x02\x06(\x00\xad\x83\x8c\xbd\r\xcd\x02\x06__type\x01w\x08listitem(\x00\xad\x83\x8c\xbd\r\xcd\x02\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xcd\x02\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xcd\x02\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\xcd\x02\x07__value\x01}\x01\x07\x00\xad\x83\x8c\xbd\r\xcd\x02\x01(\x00\xad\x83\x8c\xbd\r\xd3\x02\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\xd3\x02\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xd3\x02\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\xd3\x02\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\xd3\x02\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\xd3\x02\rnumbered list\x87\xad\x83\x8c\xbd\r\xcd\x02\x06(\x00\xad\x83\x8c\xbd\r\xe6\x02\x06__type\x01w\x08listitem(\x00\xad\x83\x8c\xbd\r\xe6\x02\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xe6\x02\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xe6\x02\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\xe6\x02\x07__value\x01}\x02\x07\x00\xad\x83\x8c\xbd\r\xe6\x02\x06(\x00\xad\x83\x8c\xbd\r\xec\x02\x06__type\x01w\x04list(\x00\xad\x83\x8c\xbd\r\xec\x02\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xec\x02\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xec\x02\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\xec\x02\n__listType\x01w\x06number(\x00\xad\x83\x8c\xbd\r\xec\x02\x05__tag\x01w\x02ol(\x00\xad\x83\x8c\xbd\r\xec\x02\x07__start\x01}\x01\x07\x00\xad\x83\x8c\xbd\r\xec\x02\x06(\x00\xad\x83\x8c\xbd\r\xf4\x02\x06__type\x01w\x08listitem(\x00\xad\x83\x8c\xbd\r\xf4\x02\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xf4\x02\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xf4\x02\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\xf4\x02\x07__value\x01}\x01\x07\x00\xad\x83\x8c\xbd\r\xf4\x02\x01(\x00\xad\x83\x8c\xbd\r\xfa\x02\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\xfa\x02\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xfa\x02\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\xfa\x02\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\xfa\x02\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\xfa\x02\x08indented\x87\xad\x83\x8c\xbd\r\xf4\x02\x06(\x00\xad\x83\x8c\xbd\r\x88\x03\x06__type\x01w\x08listitem(\x00\xad\x83\x8c\xbd\r\x88\x03\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\x88\x03\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\x88\x03\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\x88\x03\x07__value\x01}\x02\x07\x00\xad\x83\x8c\xbd\r\x88\x03\x06(\x00\xad\x83\x8c\xbd\r\x8e\x03\x06__type\x01w\x04list(\x00\xad\x83\x8c\xbd\r\x8e\x03\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\x8e\x03\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\x8e\x03\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\x8e\x03\n__listType\x01w\x06number(\x00\xad\x83\x8c\xbd\r\x8e\x03\x05__tag\x01w\x02ol(\x00\xad\x83\x8c\xbd\r\x8e\x03\x07__start\x01}\x01\x07\x00\xad\x83\x8c\xbd\r\x8e\x03\x06(\x00\xad\x83\x8c\xbd\r\x96\x03\x06__type\x01w\x08listitem(\x00\xad\x83\x8c\xbd\r\x96\x03\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\x96\x03\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\x96\x03\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\x96\x03\x07__value\x01}\x01\x07\x00\xad\x83\x8c\xbd\r\x96\x03\x01(\x00\xad\x83\x8c\xbd\r\x9c\x03\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\x9c\x03\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\x9c\x03\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\x9c\x03\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\x9c\x03\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\x9c\x03\x06deeply\x87\xad\x83\x8c\xbd\r\xe6\x02\x06(\x00\xad\x83\x8c\xbd\r\xa8\x03\x06__type\x01w\x08listitem(\x00\xad\x83\x8c\xbd\r\xa8\x03\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xa8\x03\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xa8\x03\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\xa8\x03\x07__value\x01}\x02\x07\x00\xad\x83\x8c\xbd\r\xa8\x03\x01(\x00\xad\x83\x8c\xbd\r\xae\x03\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\xae\x03\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xae\x03\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\xae\x03\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\xae\x03\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\xae\x03\x0canother item\x87\xad\x83\x8c\xbd\r\xc5\x02\x06(\x00\xad\x83\x8c\xbd\r\xc0\x03\x06__type\x01w\tparagraph(\x00\xad\x83\x8c\xbd\r\xc0\x03\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xc0\x03\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xc0\x03\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\xc0\x03\x0c__textFormat\x01}\x00\x07\x00\xad\x83\x8c\xbd\r\xc0\x03\x01(\x00\xad\x83\x8c\xbd\r\xc6\x03\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\xc6\x03\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xc6\x03\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\xc6\x03\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\xc6\x03\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\xc6\x03\x10and a checklist:\x87\xad\x83\x8c\xbd\r\xc0\x03\x06(\x00\xad\x83\x8c\xbd\r\xdc\x03\x06__type\x01w\x04list(\x00\xad\x83\x8c\xbd\r\xdc\x03\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xdc\x03\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xdc\x03\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\xdc\x03\n__listType\x01w\x05check(\x00\xad\x83\x8c\xbd\r\xdc\x03\x05__tag\x01w\x02ul(\x00\xad\x83\x8c\xbd\r\xdc\x03\x07__start\x01}\x01\x07\x00\xad\x83\x8c\xbd\r\xdc\x03\x06(\x00\xad\x83\x8c\xbd\r\xe4\x03\x06__type\x01w\x08listitem(\x00\xad\x83\x8c\xbd\r\xe4\x03\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xe4\x03\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xe4\x03\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\xe4\x03\x07__value\x01}\x01(\x00\xad\x83\x8c\xbd\r\xe4\x03\t__checked\x01y\x07\x00\xad\x83\x8c\xbd\r\xe4\x03\x01(\x00\xad\x83\x8c\xbd\r\xeb\x03\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\xeb\x03\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xeb\x03\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\xeb\x03\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\xeb\x03\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\xeb\x03\x04list\x87\xad\x83\x8c\xbd\r\xe4\x03\x06(\x00\xad\x83\x8c\xbd\r\xf5\x03\x06__type\x01w\x08listitem(\x00\xad\x83\x8c\xbd\r\xf5\x03\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xf5\x03\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xf5\x03\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\xf5\x03\x07__value\x01}\x02(\x00\xad\x83\x8c\xbd\r\xf5\x03\t__checked\x01y\x07\x00\xad\x83\x8c\xbd\r\xf5\x03\x06(\x00\xad\x83\x8c\xbd\r\xfc\x03\x06__type\x01w\x04list(\x00\xad\x83\x8c\xbd\r\xfc\x03\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xfc\x03\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xfc\x03\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\xfc\x03\n__listType\x01w\x05check(\x00\xad\x83\x8c\xbd\r\xfc\x03\x05__tag\x01w\x02ul(\x00\xad\x83\x8c\xbd\r\xfc\x03\x07__start\x01}\x01\x07\x00\xad\x83\x8c\xbd\r\xfc\x03\x06(\x00\xad\x83\x8c\xbd\r\x84\x04\x06__type\x01w\x08listitem(\x00\xad\x83\x8c\xbd\r\x84\x04\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\x84\x04\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\x84\x04\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\x84\x04\x07__value\x01}\x01(\x00\xad\x83\x8c\xbd\r\x84\x04\t__checked\x01y\x07\x00\xad\x83\x8c\xbd\r\x84\x04\x01(\x00\xad\x83\x8c\xbd\r\x8b\x04\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\x8b\x04\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\x8b\x04\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\x8b\x04\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\x8b\x04\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\x8b\x04\x08indented\x87\xad\x83\x8c\xbd\r\x84\x04\x06(\x00\xad\x83\x8c\xbd\r\x99\x04\x06__type\x01w\x08listitem(\x00\xad\x83\x8c\xbd\r\x99\x04\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\x99\x04\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\x99\x04\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\x99\x04\x07__value\x01}\x02(\x00\xad\x83\x8c\xbd\r\x99\x04\t__checked\x01y\x07\x00\xad\x83\x8c\xbd\r\x99\x04\x06(\x00\xad\x83\x8c\xbd\r\xa0\x04\x06__type\x01w\x04list(\x00\xad\x83\x8c\xbd\r\xa0\x04\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xa0\x04\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xa0\x04\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\xa0\x04\n__listType\x01w\x05check(\x00\xad\x83\x8c\xbd\r\xa0\x04\x05__tag\x01w\x02ul(\x00\xad\x83\x8c\xbd\r\xa0\x04\x07__start\x01}\x01\x07\x00\xad\x83\x8c\xbd\r\xa0\x04\x06(\x00\xad\x83\x8c\xbd\r\xa8\x04\x06__type\x01w\x08listitem(\x00\xad\x83\x8c\xbd\r\xa8\x04\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xa8\x04\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xa8\x04\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\xa8\x04\x07__value\x01}\x01(\x00\xad\x83\x8c\xbd\r\xa8\x04\t__checked\x01y\x07\x00\xad\x83\x8c\xbd\r\xa8\x04\x01(\x00\xad\x83\x8c\xbd\r\xaf\x04\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\xaf\x04\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xaf\x04\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\xaf\x04\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\xaf\x04\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\xaf\x04\x06deeply\x87\xad\x83\x8c\xbd\r\xf5\x03\x06(\x00\xad\x83\x8c\xbd\r\xbb\x04\x06__type\x01w\x08listitem(\x00\xad\x83\x8c\xbd\r\xbb\x04\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xbb\x04\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xbb\x04\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\xbb\x04\x07__value\x01}\x02(\x00\xad\x83\x8c\xbd\r\xbb\x04\t__checked\x01y\x07\x00\xad\x83\x8c\xbd\r\xbb\x04\x01(\x00\xad\x83\x8c\xbd\r\xc2\x04\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\xc2\x04\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xc2\x04\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\xc2\x04\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\xc2\x04\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\xc2\x04\x0canother item\x87\xad\x83\x8c\xbd\r\xdc\x03\x06(\x00\xad\x83\x8c\xbd\r\xd4\x04\x06__type\x01w\x05quote(\x00\xad\x83\x8c\xbd\r\xd4\x04\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xd4\x04\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xd4\x04\x05__dir\x01w\x03ltr\x07\x00\xad\x83\x8c\xbd\r\xd4\x04\x01(\x00\xad\x83\x8c\xbd\r\xd9\x04\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\xd9\x04\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xd9\x04\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\xd9\x04\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\xd9\x04\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\xd9\x04\x05quote\x87\xad\x83\x8c\xbd\r\xd4\x04\x06(\x00\xad\x83\x8c\xbd\r\xe4\x04\x06__type\x01w\x04code(\x00\xad\x83\x8c\xbd\r\xe4\x04\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xe4\x04\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xe4\x04\x05__dir\x01w\x03ltr!\x00\xad\x83\x8c\xbd\r\xe4\x04\n__language\x01\x01\x00\xad\x83\x8c\xbd\r\xe4\x04\x01\x00\x06\x81\xad\x83\x8c\xbd\r\xea\x04\x04\x00\x05\x81\xad\x83\x8c\xbd\r\xf4\x04\x02\x00\x06\x81\xad\x83\x8c\xbd\r\xfb\x04\x02\x00\x06\x81\xad\x83\x8c\xbd\r\x83\x05\x02\x00\x06\x81\xad\x83\x8c\xbd\r\x8b\x05\x02\x00\x06\x81\xad\x83\x8c\xbd\r\x93\x05\x02\x00\x01\x81\xad\x83\x8c\xbd\r\x9b\x05\x01\x00\x05\x81\xad\x83\x8c\xbd\r\x9d\x05\x05\x00\x06\x81\xad\x83\x8c\xbd\r\xa7\x05\x05\x87\xad\x83\x8c\xbd\r\xb2\x05\x01(\x00\xad\x83\x8c\xbd\r\xb3\x05\x06__type\x01w\x0ecode-highlight(\x00\xad\x83\x8c\xbd\r\xb3\x05\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xb3\x05\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\xb3\x05\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\xb3\x05\x08__detail\x01}\x00(\x00\xad\x83\x8c\xbd\r\xb3\x05\x0f__highlightType\x01w\x0bpunctuation\x84\xad\x83\x8c\xbd\r\xb3\x05\x01(\x87\xad\x83\x8c\xbd\r\xba\x05\x01(\x00\xad\x83\x8c\xbd\r\xbb\x05\x06__type\x01w\x0ecode-highlight(\x00\xad\x83\x8c\xbd\r\xbb\x05\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xbb\x05\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\xbb\x05\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\xbb\x05\x08__detail\x01}\x00(\x00\xad\x83\x8c\xbd\r\xbb\x05\x0f__highlightType\x01w\x06string\x84\xad\x83\x8c\xbd\r\xbb\x05\x04\"hi\"\x87\xad\x83\x8c\xbd\r\xc5\x05\x01(\x00\xad\x83\x8c\xbd\r\xc6\x05\x06__type\x01w\x0ecode-highlight(\x00\xad\x83\x8c\xbd\r\xc6\x05\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xc6\x05\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\xc6\x05\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\xc6\x05\x08__detail\x01}\x00(\x00\xad\x83\x8c\xbd\r\xc6\x05\x0f__highlightType\x01w\x0bpunctuation\x84\xad\x83\x8c\xbd\r\xc6\x05\x01)\x87\xad\x83\x8c\xbd\r\xe4\x04\x06(\x00\xad\x83\x8c\xbd\r\xce\x05\x06__type\x01w\x07heading(\x00\xad\x83\x8c\xbd\r\xce\x05\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xce\x05\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xce\x05\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\xce\x05\x05__tag\x01w\x02h1\x07\x00\xad\x83\x8c\xbd\r\xce\x05\x01(\x00\xad\x83\x8c\xbd\r\xd4\x05\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\xd4\x05\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xd4\x05\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\xd4\x05\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\xd4\x05\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\xd4\x05\x0bFinal notes\x87\xad\x83\x8c\xbd\r\xce\x05\x06(\x00\xad\x83\x8c\xbd\r\xe5\x05\x06__type\x01w\x04list(\x00\xad\x83\x8c\xbd\r\xe5\x05\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xe5\x05\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xe5\x05\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\xe5\x05\n__listType\x01w\x06bullet(\x00\xad\x83\x8c\xbd\r\xe5\x05\x05__tag\x01w\x02ul(\x00\xad\x83\x8c\xbd\r\xe5\x05\x07__start\x01}\x01\x07\x00\xad\x83\x8c\xbd\r\xe5\x05\x06(\x00\xad\x83\x8c\xbd\r\xed\x05\x06__type\x01w\x08listitem(\x00\xad\x83\x8c\xbd\r\xed\x05\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xed\x05\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xed\x05\x05__dir\x01~(\x00\xad\x83\x8c\xbd\r\xed\x05\x07__value\x01}\x01\x07\x00\xad\x83\x8c\xbd\r\xed\x05\x01(\x00\xad\x83\x8c\xbd\r\xf3\x05\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\xf3\x05\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xf3\x05\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\xf3\x05\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\xf3\x05\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\xf3\x05\x01 \x87\xad\x83\x8c\xbd\r\xed\x05\x06(\x00\xad\x83\x8c\xbd\r\xfa\x05\x06__type\x01w\x08listitem(\x00\xad\x83\x8c\xbd\r\xfa\x05\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xfa\x05\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xfa\x05\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\xfa\x05\x07__value\x01}\x02\x07\x00\xad\x83\x8c\xbd\r\xfa\x05\x01(\x00\xad\x83\x8c\xbd\r\x80\x06\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\x80\x06\x08__format\x01}\x01(\x00\xad\x83\x8c\xbd\r\x80\x06\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\x80\x06\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\x80\x06\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\x80\x06\x04BOLD\x87\xad\x83\x8c\xbd\r\x89\x06\x01(\x00\xad\x83\x8c\xbd\r\x8a\x06\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\x8a\x06\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\x8a\x06\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\x8a\x06\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\x8a\x06\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\x8a\x06\x01 \x87\xad\x83\x8c\xbd\r\x90\x06\x01(\x00\xad\x83\x8c\xbd\r\x91\x06\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\x91\x06\x08__format\x01}\x02(\x00\xad\x83\x8c\xbd\r\x91\x06\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\x91\x06\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\x91\x06\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\x91\x06\x06italic\x87\xad\x83\x8c\xbd\r\x9c\x06\x01(\x00\xad\x83\x8c\xbd\r\x9d\x06\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\x9d\x06\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\x9d\x06\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\x9d\x06\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\x9d\x06\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\x9d\x06\x01 \x87\xad\x83\x8c\xbd\r\xa3\x06\x01(\x00\xad\x83\x8c\xbd\r\xa4\x06\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\xa4\x06\x08__format\x01}\x04(\x00\xad\x83\x8c\xbd\r\xa4\x06\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\xa4\x06\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\xa4\x06\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\xa4\x06\x06struck\x87\xad\x83\x8c\xbd\r\xaf\x06\x01(\x00\xad\x83\x8c\xbd\r\xb0\x06\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\xb0\x06\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xb0\x06\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\xb0\x06\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\xb0\x06\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\xb0\x06\x01 \x87\xad\x83\x8c\xbd\r\xb6\x06\x01(\x00\xad\x83\x8c\xbd\r\xb7\x06\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\xb7\x06\x08__format\x01}\x08(\x00\xad\x83\x8c\xbd\r\xb7\x06\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\xb7\x06\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\xb7\x06\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\xb7\x06\nunderlined\x87\xad\x83\x8c\xbd\r\xc6\x06\x01(\x00\xad\x83\x8c\xbd\r\xc7\x06\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\xc7\x06\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xc7\x06\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\xc7\x06\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\xc7\x06\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\xc7\x06\x01 \x87\xad\x83\x8c\xbd\r\xcd\x06\x01(\x00\xad\x83\x8c\xbd\r\xce\x06\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\xce\x06\x08__format\x01}\x07(\x00\xad\x83\x8c\xbd\r\xce\x06\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\xce\x06\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\xce\x06\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\xce\x06\x08multiple\x87\xad\x83\x8c\xbd\r\xfa\x05\x06(\x00\xad\x83\x8c\xbd\r\xdc\x06\x06__type\x01w\x08listitem(\x00\xad\x83\x8c\xbd\r\xdc\x06\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xdc\x06\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xdc\x06\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\xdc\x06\x07__value\x01}\x03\x07\x00\xad\x83\x8c\xbd\r\xdc\x06\x01(\x00\xad\x83\x8c\xbd\r\xe2\x06\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\xe2\x06\x08__format\x01}\x10(\x00\xad\x83\x8c\xbd\r\xe2\x06\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\xe2\x06\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\xe2\x06\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\xe2\x06\x07snippet\x87\xad\x83\x8c\xbd\r\xdc\x06\x06(\x00\xad\x83\x8c\xbd\r\xef\x06\x06__type\x01w\x08listitem(\x00\xad\x83\x8c\xbd\r\xef\x06\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xef\x06\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xef\x06\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\xef\x06\x07__value\x01}\x04\x07\x00\xad\x83\x8c\xbd\r\xef\x06\x06(\x00\xad\x83\x8c\xbd\r\xf5\x06\x06__type\x01w\x04link(\x00\xad\x83\x8c\xbd\r\xf5\x06\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xf5\x06\x08__indent\x01}\x00(\x00\xad\x83\x8c\xbd\r\xf5\x06\x05__dir\x01w\x03ltr(\x00\xad\x83\x8c\xbd\r\xf5\x06\x05__url\x01w\x17https://www.google.com/(\x00\xad\x83\x8c\xbd\r\xf5\x06\x08__target\x01~(\x00\xad\x83\x8c\xbd\r\xf5\x06\x05__rel\x01w\nnoreferrer(\x00\xad\x83\x8c\xbd\r\xf5\x06\x07__title\x01~\x07\x00\xad\x83\x8c\xbd\r\xf5\x06\x01(\x00\xad\x83\x8c\xbd\r\xfe\x06\x06__type\x01w\x04text(\x00\xad\x83\x8c\xbd\r\xfe\x06\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xfe\x06\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\xfe\x06\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\xfe\x06\x08__detail\x01}\x00\x84\xad\x83\x8c\xbd\r\xfe\x06\x0bgoogle link\xa8\xad\x83\x8c\xbd\r\xe9\x04\x01w\njavascript\xc7\xad\x83\x8c\xbd\r\xb2\x05\xad\x83\x8c\xbd\r\xb3\x05\x01(\x00\xad\x83\x8c\xbd\r\x90\x07\x06__type\x01w\x0ecode-highlight(\x00\xad\x83\x8c\xbd\r\x90\x07\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\x90\x07\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\x90\x07\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\x90\x07\x08__detail\x01}\x00\xc4\xad\x83\x8c\xbd\r\x90\x07\xad\x83\x8c\xbd\r\xb3\x05\x04def \xc7\xad\x83\x8c\xbd\r\x99\x07\xad\x83\x8c\xbd\r\xb3\x05\x01(\x00\xad\x83\x8c\xbd\r\x9a\x07\x06__type\x01w\x0ecode-highlight(\x00\xad\x83\x8c\xbd\r\x9a\x07\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\x9a\x07\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\x9a\x07\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\x9a\x07\x08__detail\x01}\x00(\x00\xad\x83\x8c\xbd\r\x9a\x07\x0f__highlightType\x01w\x08function\xc4\xad\x83\x8c\xbd\r\x9a\x07\xad\x83\x8c\xbd\r\xb3\x05\x01f\xc7\xad\x83\x8c\xbd\r\xa1\x07\xad\x83\x8c\xbd\r\xb3\x05\x01(\x00\xad\x83\x8c\xbd\r\xa2\x07\x06__type\x01w\x0ecode-highlight(\x00\xad\x83\x8c\xbd\r\xa2\x07\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xa2\x07\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\xa2\x07\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\xa2\x07\x08__detail\x01}\x00(\x00\xad\x83\x8c\xbd\r\xa2\x07\x0f__highlightType\x01w\x0bpunctuation\xc4\xad\x83\x8c\xbd\r\xa2\x07\xad\x83\x8c\xbd\r\xb3\x05\x01(\xc7\xad\x83\x8c\xbd\r\xa9\x07\xad\x83\x8c\xbd\r\xb3\x05\x01(\x00\xad\x83\x8c\xbd\r\xaa\x07\x06__type\x01w\x0ecode-highlight(\x00\xad\x83\x8c\xbd\r\xaa\x07\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xaa\x07\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\xaa\x07\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\xaa\x07\x08__detail\x01}\x00(\x00\xad\x83\x8c\xbd\r\xaa\x07\x0f__highlightType\x01w\x0bpunctuation\xc4\xad\x83\x8c\xbd\r\xaa\x07\xad\x83\x8c\xbd\r\xb3\x05\x01)\xc7\xad\x83\x8c\xbd\r\xb1\x07\xad\x83\x8c\xbd\r\xb3\x05\x01(\x00\xad\x83\x8c\xbd\r\xb2\x07\x06__type\x01w\x0ecode-highlight(\x00\xad\x83\x8c\xbd\r\xb2\x07\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xb2\x07\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\xb2\x07\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\xb2\x07\x08__detail\x01}\x00(\x00\xad\x83\x8c\xbd\r\xb2\x07\x0f__highlightType\x01w\x08operator\xc4\xad\x83\x8c\xbd\r\xb2\x07\xad\x83\x8c\xbd\r\xb3\x05\x01:\xc7\xad\x83\x8c\xbd\r\xb9\x07\xad\x83\x8c\xbd\r\xb3\x05\x01(\x00\xad\x83\x8c\xbd\r\xba\x07\x06__type\x01w\tlinebreak\xc7\xad\x83\x8c\xbd\r\xba\x07\xad\x83\x8c\xbd\r\xb3\x05\x01(\x00\xad\x83\x8c\xbd\r\xbc\x07\x06__type\x01w\x0ecode-highlight(\x00\xad\x83\x8c\xbd\r\xbc\x07\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xbc\x07\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\xbc\x07\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\xbc\x07\x08__detail\x01}\x00\xc4\xad\x83\x8c\xbd\r\xbc\x07\xad\x83\x8c\xbd\r\xb3\x05\x04    \xc7\xad\x83\x8c\xbd\r\xc5\x07\xad\x83\x8c\xbd\r\xb3\x05\x01(\x00\xad\x83\x8c\xbd\r\xc6\x07\x06__type\x01w\x0ecode-highlight(\x00\xad\x83\x8c\xbd\r\xc6\x07\x08__format\x01}\x00(\x00\xad\x83\x8c\xbd\r\xc6\x07\x07__style\x01w\x00(\x00\xad\x83\x8c\xbd\r\xc6\x07\x06__mode\x01}\x00(\x00\xad\x83\x8c\xbd\r\xc6\x07\x08__detail\x01}\x00(\x00\xad\x83\x8c\xbd\r\xc6\x07\x0f__highlightType\x01w\x08function\xc4\xad\x83\x8c\xbd\r\xc6\x07\xad\x83\x8c\xbd\r\xb3\x05\x05print\x01\xad\x83\x8c\xbd\r\x01\xe9\x04J".to_vec();
        let expected_json: Value = json!({
            "__dir": "ltr",
            "children": [
                {
                "__type": "heading",
                "__format": 0,
                "__indent": 0,
                "__dir": "ltr",
                "__tag": "h1",
                "children": [
                    {
                    "__type": "text",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "text": "H1"
                    }
                ]
                },
                {
                "__type": "paragraph",
                "__format": 0,
                "__indent": 0,
                "__dir": "ltr",
                "__textFormat": 0,
                "children": [
                    {
                    "__type": "text",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "text": "underneath, a paragraph"
                    }
                ]
                },
                {
                "__type": "heading",
                "__format": 0,
                "__indent": 0,
                "__dir": "ltr",
                "__tag": "h2",
                "children": [
                    {
                    "__type": "text",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "text": "H2"
                    }
                ]
                },
                {
                "__type": "heading",
                "__format": 0,
                "__indent": 0,
                "__dir": "ltr",
                "__tag": "h2",
                "children": [
                    {
                    "__type": "text",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "text": "Second H2"
                    }
                ]
                },
                {
                "__type": "paragraph",
                "__format": 0,
                "__indent": 0,
                "__dir": "ltr",
                "__textFormat": 0,
                "children": [
                    {
                    "__type": "text",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "text": "some content"
                    }
                ]
                },
                {
                "__type": "paragraph",
                "__format": 0,
                "__indent": 0,
                "__dir": "ltr",
                "__textFormat": 0,
                "children": [
                    {
                    "__type": "text",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "text": "a toggle"
                    }
                ]
                },
                {
                "__type": "paragraph",
                "__format": 0,
                "__indent": 0,
                "__dir": "ltr",
                "__textFormat": 0,
                "children": [
                    {
                    "__type": "text",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "text": "with content"
                    }
                ]
                },
                {
                "__type": "heading",
                "__format": 0,
                "__indent": 0,
                "__dir": "ltr",
                "__tag": "h1",
                "children": [
                    {
                    "__type": "text",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "text": "Second h1"
                    }
                ]
                },
                {
                "__type": "list",
                "__format": 0,
                "__indent": 0,
                "__dir": "ltr",
                "__listType": "bullet",
                "__tag": "ul",
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
                        "text": "bulleted list"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 2,
                    "children": [
                        {
                        "__type": "list",
                        "__format": 0,
                        "__indent": 0,
                        "__dir": "ltr",
                        "__listType": "bullet",
                        "__tag": "ul",
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
                                "text": "indented"
                                }
                            ]
                            },
                            {
                            "__type": "listitem",
                            "__format": 0,
                            "__indent": 0,
                            "__dir": "ltr",
                            "__value": 2,
                            "children": [
                                {
                                "__type": "list",
                                "__format": 0,
                                "__indent": 0,
                                "__dir": "ltr",
                                "__listType": "bullet",
                                "__tag": "ul",
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
                                        "text": "deeply"
                                        }
                                    ]
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
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 2,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "another item"
                        }
                    ]
                    }
                ]
                },
                {
                "__type": "heading",
                "__format": 0,
                "__indent": 0,
                "__dir": "ltr",
                "__tag": "h2",
                "children": [
                    {
                    "__type": "text",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "text": "H2"
                    }
                ]
                },
                {
                "__type": "heading",
                "__format": 0,
                "__indent": 0,
                "__dir": "ltr",
                "__tag": "h3",
                "children": [
                    {
                    "__type": "text",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "text": "H3"
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
                        "text": "numbered list"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
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
                                "text": "indented"
                                }
                            ]
                            },
                            {
                            "__type": "listitem",
                            "__format": 0,
                            "__indent": 0,
                            "__dir": "ltr",
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
                                        "text": "deeply"
                                        }
                                    ]
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
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 2,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "another item"
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
                "__textFormat": 0,
                "children": [
                    {
                    "__type": "text",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "text": "and a checklist:"
                    }
                ]
                },
                {
                "__type": "list",
                "__format": 0,
                "__indent": 0,
                "__dir": "ltr",
                "__listType": "check",
                "__tag": "ul",
                "__start": 1,
                "children": [
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 1,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "list"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 2,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "list",
                        "__format": 0,
                        "__indent": 0,
                        "__dir": "ltr",
                        "__listType": "check",
                        "__tag": "ul",
                        "__start": 1,
                        "children": [
                            {
                            "__type": "listitem",
                            "__format": 0,
                            "__indent": 0,
                            "__dir": "ltr",
                            "__value": 1,
                            "__checked": false,
                            "children": [
                                {
                                "__type": "text",
                                "__format": 0,
                                "__style": "",
                                "__mode": 0,
                                "__detail": 0,
                                "text": "indented"
                                }
                            ]
                            },
                            {
                            "__type": "listitem",
                            "__format": 0,
                            "__indent": 0,
                            "__dir": "ltr",
                            "__value": 2,
                            "__checked": false,
                            "children": [
                                {
                                "__type": "list",
                                "__format": 0,
                                "__indent": 0,
                                "__dir": "ltr",
                                "__listType": "check",
                                "__tag": "ul",
                                "__start": 1,
                                "children": [
                                    {
                                    "__type": "listitem",
                                    "__format": 0,
                                    "__indent": 0,
                                    "__dir": "ltr",
                                    "__value": 1,
                                    "__checked": false,
                                    "children": [
                                        {
                                        "__type": "text",
                                        "__format": 0,
                                        "__style": "",
                                        "__mode": 0,
                                        "__detail": 0,
                                        "text": "deeply"
                                        }
                                    ]
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
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 2,
                    "__checked": false,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "another item"
                        }
                    ]
                    }
                ]
                },
                {
                "__type": "quote",
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
                    "text": "quote"
                    }
                ]
                },
                {
                "__type": "code",
                "__format": 0,
                "__indent": 0,
                "__dir": "ltr",
                "__language": "javascript",
                "children": [
                    {
                    "__type": "code-highlight",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "text": "def "
                    },
                    {
                    "__type": "code-highlight",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "__highlightType": "function",
                    "text": "f"
                    },
                    {
                    "__type": "code-highlight",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "__highlightType": "punctuation",
                    "text": "("
                    },
                    {
                    "__type": "code-highlight",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "__highlightType": "punctuation",
                    "text": ")"
                    },
                    {
                    "__type": "code-highlight",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "__highlightType": "operator",
                    "text": ":"
                    },
                    {
                    "__type": "linebreak"
                    },
                    {
                    "__type": "code-highlight",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "text": "    "
                    },
                    {
                    "__type": "code-highlight",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "__highlightType": "function",
                    "text": "print"
                    },
                    {
                    "__type": "code-highlight",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "__highlightType": "punctuation",
                    "text": "("
                    },
                    {
                    "__type": "code-highlight",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "__highlightType": "string",
                    "text": "\"hi\""
                    },
                    {
                    "__type": "code-highlight",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "__highlightType": "punctuation",
                    "text": ")"
                    }
                ]
                },
                {
                "__type": "heading",
                "__format": 0,
                "__indent": 0,
                "__dir": "ltr",
                "__tag": "h1",
                "children": [
                    {
                    "__type": "text",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "text": "Final notes"
                    }
                ]
                },
                {
                "__type": "list",
                "__format": 0,
                "__indent": 0,
                "__dir": "ltr",
                "__listType": "bullet",
                "__tag": "ul",
                "__start": 1,
                "children": [
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": null,
                    "__value": 1,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": " "
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 2,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 1,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "BOLD"
                        },
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": " "
                        },
                        {
                        "__type": "text",
                        "__format": 2,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "italic"
                        },
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": " "
                        },
                        {
                        "__type": "text",
                        "__format": 4,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "struck"
                        },
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": " "
                        },
                        {
                        "__type": "text",
                        "__format": 8,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "underlined"
                        },
                        {
                        "__type": "text",
                        "__format": 0,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": " "
                        },
                        {
                        "__type": "text",
                        "__format": 7,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "multiple"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 3,
                    "children": [
                        {
                        "__type": "text",
                        "__format": 16,
                        "__style": "",
                        "__mode": 0,
                        "__detail": 0,
                        "text": "snippet"
                        }
                    ]
                    },
                    {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": "ltr",
                    "__value": 4,
                    "children": [
                        {
                        "__type": "link",
                        "__format": 0,
                        "__indent": 0,
                        "__dir": "ltr",
                        "__url": "https://www.google.com/",
                        "__target": null,
                        "__rel": "noreferrer",
                        "__title": null,
                        "children": [
                            {
                            "__type": "text",
                            "__format": 0,
                            "__style": "",
                            "__mode": 0,
                            "__detail": 0,
                            "text": "google link"
                            }
                        ]
                        }
                    ]
                    }
                ]
                }
            ]
        });

        let result = process_xml_fragment(update_bytes);
        let mut result_buf = String::new();

        Any::Map(Box::new(result)).to_json(&mut result_buf);
        let result_json: Value = from_str(&result_buf).unwrap();

        println!("Result:\n{}", to_string_pretty(&result_json).unwrap());

        assert_json_eq!(result_json, expected_json);
    }

    #[test]
    fn parse_nested_xml_text_nodes_of_long_text() {
        let update_bytes: Vec<u8> = b"\x01\x9d\x01\xd7\xed\xd8\xa4\r\x00(\x01\x04root\x05__dir\x01w\x03ltr\x07\x01\x04root\x06(\x00\xd7\xed\xd8\xa4\r\x01\x06__type\x01w\tparagraph(\x00\xd7\xed\xd8\xa4\r\x01\x08__format\x01}\x00(\x00\xd7\xed\xd8\xa4\r\x01\x08__indent\x01}\x00(\x00\xd7\xed\xd8\xa4\r\x01\x05__dir\x01w\x03ltr(\x00\xd7\xed\xd8\xa4\r\x01\x0c__textFormat\x01}\x00\x07\x00\xd7\xed\xd8\xa4\r\x01\x01(\x00\xd7\xed\xd8\xa4\r\x07\x06__type\x01w\x04text(\x00\xd7\xed\xd8\xa4\r\x07\x08__format\x01}\x00(\x00\xd7\xed\xd8\xa4\r\x07\x07__style\x01w\x00(\x00\xd7\xed\xd8\xa4\r\x07\x06__mode\x01}\x00(\x00\xd7\xed\xd8\xa4\r\x07\x08__detail\x01}\x00\x84\xd7\xed\xd8\xa4\r\x07\xf1\x02LoremipsumdolorsitametconsecteturadipiscingelitseddoeiusmodtemporincididuntutlaboreetdoloremagnaaliquaUtenimadminimveniamquisnostrudexercitationullamcolaborisnisiutaliquipexeacommodoconsequatDuisauteiruredolorinreprehenderitinvoluptatevelitessecillumdoloreeufugiatnullapariaturExcepteursintoccaecatcupidatatnonproidentsuntinculpaquiofficiadeseruntmollitanimidestlaborum\x87\xd7\xed\xd8\xa4\r\x01\x06(\x00\xd7\xed\xd8\xa4\r\xfe\x02\x06__type\x01w\tparagraph(\x00\xd7\xed\xd8\xa4\r\xfe\x02\x08__format\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xfe\x02\x08__indent\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xfe\x02\x05__dir\x01w\x03ltr(\x00\xd7\xed\xd8\xa4\r\xfe\x02\x0c__textFormat\x01}\x00\x07\x00\xd7\xed\xd8\xa4\r\xfe\x02\x01(\x00\xd7\xed\xd8\xa4\r\x84\x03\x06__type\x01w\x04text(\x00\xd7\xed\xd8\xa4\r\x84\x03\x08__format\x01}\x00(\x00\xd7\xed\xd8\xa4\r\x84\x03\x07__style\x01w\x00(\x00\xd7\xed\xd8\xa4\r\x84\x03\x06__mode\x01}\x00(\x00\xd7\xed\xd8\xa4\r\x84\x03\x08__detail\x01}\x00\x84\xd7\xed\xd8\xa4\r\x84\x03\xbd\x03Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.\x87\xd7\xed\xd8\xa4\r\xfe\x02\x06(\x00\xd7\xed\xd8\xa4\r\xc7\x06\x06__type\x01w\tparagraph(\x00\xd7\xed\xd8\xa4\r\xc7\x06\x08__format\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xc7\x06\x08__indent\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xc7\x06\x05__dir\x01w\x03ltr(\x00\xd7\xed\xd8\xa4\r\xc7\x06\x0c__textFormat\x01}\x00\x07\x00\xd7\xed\xd8\xa4\r\xc7\x06\x01(\x00\xd7\xed\xd8\xa4\r\xcd\x06\x06__type\x01w\x04text(\x00\xd7\xed\xd8\xa4\r\xcd\x06\x08__format\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xcd\x06\x07__style\x01w\x00(\x00\xd7\xed\xd8\xa4\r\xcd\x06\x06__mode\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xcd\x06\x08__detail\x01}\x00\x84\xd7\xed\xd8\xa4\r\xcd\x06\xf1\x02LoremipsumdolorsitametconsecteturadipiscingelitseddoeiusmodtemporincididuntutlaboreetdoloremagnaaliquaUtenimadminimveniamquisnostrudexercitationullamcolaborisnisiutaliquipexeacommodoconsequatDuisauteiruredolorinreprehenderitinvoluptatevelitessecillumdoloreeufugiatnullapariaturExcepteursintoccaecatcupidatatnonproidentsuntinculpaquiofficiadeseruntmollitanimidestlaborum\x87\xd7\xed\xd8\xa4\r\xc7\x06\x06(\x00\xd7\xed\xd8\xa4\r\xc4\t\x06__type\x01w\tparagraph(\x00\xd7\xed\xd8\xa4\r\xc4\t\x08__format\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xc4\t\x08__indent\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xc4\t\x05__dir\x01w\x03ltr(\x00\xd7\xed\xd8\xa4\r\xc4\t\x0c__textFormat\x01}\x00\x07\x00\xd7\xed\xd8\xa4\r\xc4\t\x01(\x00\xd7\xed\xd8\xa4\r\xca\t\x06__type\x01w\x04text(\x00\xd7\xed\xd8\xa4\r\xca\t\x08__format\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xca\t\x07__style\x01w\x00(\x00\xd7\xed\xd8\xa4\r\xca\t\x06__mode\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xca\t\x08__detail\x01}\x00\x84\xd7\xed\xd8\xa4\r\xca\t\xf1\x02LoremipsumdolorsitametconsecteturadipiscingelitseddoeiusmodtemporincididuntutlaboreetdoloremagnaaliquaUtenimadminimveniamquisnostrudexercitationullamcolaborisnisiutaliquipexeacommodoconsequatDuisauteiruredolorinreprehenderitinvoluptatevelitessecillumdoloreeufugiatnullapariaturExcepteursintoccaecatcupidatatnonproidentsuntinculpaquiofficiadeseruntmollitanimidestlaborum\x87\xd7\xed\xd8\xa4\r\xc4\t\x06(\x00\xd7\xed\xd8\xa4\r\xc1\x0c\x06__type\x01w\tparagraph(\x00\xd7\xed\xd8\xa4\r\xc1\x0c\x08__format\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xc1\x0c\x08__indent\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xc1\x0c\x05__dir\x01w\x03ltr(\x00\xd7\xed\xd8\xa4\r\xc1\x0c\x0c__textFormat\x01}\x00\x07\x00\xd7\xed\xd8\xa4\r\xc1\x0c\x01(\x00\xd7\xed\xd8\xa4\r\xc7\x0c\x06__type\x01w\x04text(\x00\xd7\xed\xd8\xa4\r\xc7\x0c\x08__format\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xc7\x0c\x07__style\x01w\x00(\x00\xd7\xed\xd8\xa4\r\xc7\x0c\x06__mode\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xc7\x0c\x08__detail\x01}\x00\x84\xd7\xed\xd8\xa4\r\xc7\x0c\xf1\x02LoremipsumdolorsitametconsecteturadipiscingelitseddoeiusmodtemporincididuntutlaboreetdoloremagnaaliquaUtenimadminimveniamquisnostrudexercitationullamcolaborisnisiutaliquipexeacommodoconsequatDuisauteiruredolorinreprehenderitinvoluptatevelitessecillumdoloreeufugiatnullapariaturExcepteursintoccaecatcupidatatnonproidentsuntinculpaquiofficiadeseruntmollitanimidestlaborum\x87\xd7\xed\xd8\xa4\r\xc1\x0c\x06(\x00\xd7\xed\xd8\xa4\r\xbe\x0f\x06__type\x01w\tparagraph(\x00\xd7\xed\xd8\xa4\r\xbe\x0f\x08__format\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xbe\x0f\x08__indent\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xbe\x0f\x05__dir\x01w\x03ltr(\x00\xd7\xed\xd8\xa4\r\xbe\x0f\x0c__textFormat\x01}\x00\x07\x00\xd7\xed\xd8\xa4\r\xbe\x0f\x01(\x00\xd7\xed\xd8\xa4\r\xc4\x0f\x06__type\x01w\x04text(\x00\xd7\xed\xd8\xa4\r\xc4\x0f\x08__format\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xc4\x0f\x07__style\x01w\x00(\x00\xd7\xed\xd8\xa4\r\xc4\x0f\x06__mode\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xc4\x0f\x08__detail\x01}\x00\x84\xd7\xed\xd8\xa4\r\xc4\x0f\xbd\x03Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.\x87\xd7\xed\xd8\xa4\r\xbe\x0f\x06(\x00\xd7\xed\xd8\xa4\r\x87\x13\x06__type\x01w\tparagraph(\x00\xd7\xed\xd8\xa4\r\x87\x13\x08__format\x01}\x00(\x00\xd7\xed\xd8\xa4\r\x87\x13\x08__indent\x01}\x00(\x00\xd7\xed\xd8\xa4\r\x87\x13\x05__dir\x01w\x03ltr(\x00\xd7\xed\xd8\xa4\r\x87\x13\x0c__textFormat\x01}\x00\x07\x00\xd7\xed\xd8\xa4\r\x87\x13\x01(\x00\xd7\xed\xd8\xa4\r\x8d\x13\x06__type\x01w\x04text(\x00\xd7\xed\xd8\xa4\r\x8d\x13\x08__format\x01}\x00(\x00\xd7\xed\xd8\xa4\r\x8d\x13\x07__style\x01w\x00(\x00\xd7\xed\xd8\xa4\r\x8d\x13\x06__mode\x01}\x00(\x00\xd7\xed\xd8\xa4\r\x8d\x13\x08__detail\x01}\x00\x84\xd7\xed\xd8\xa4\r\x8d\x13\xf1\x02LoremipsumdolorsitametconsecteturadipiscingelitseddoeiusmodtemporincididuntutlaboreetdoloremagnaaliquaUtenimadminimveniamquisnostrudexercitationullamcolaborisnisiutaliquipexeacommodoconsequatDuisauteiruredolorinreprehenderitinvoluptatevelitessecillumdoloreeufugiatnullapariaturExcepteursintoccaecatcupidatatnonproidentsuntinculpaquiofficiadeseruntmollitanimidestlaborum\x87\xd7\xed\xd8\xa4\r\x87\x13\x06(\x00\xd7\xed\xd8\xa4\r\x84\x16\x06__type\x01w\tparagraph(\x00\xd7\xed\xd8\xa4\r\x84\x16\x08__format\x01}\x00(\x00\xd7\xed\xd8\xa4\r\x84\x16\x08__indent\x01}\x00(\x00\xd7\xed\xd8\xa4\r\x84\x16\x05__dir\x01w\x03ltr(\x00\xd7\xed\xd8\xa4\r\x84\x16\x0c__textFormat\x01}\x00\x07\x00\xd7\xed\xd8\xa4\r\x84\x16\x01(\x00\xd7\xed\xd8\xa4\r\x8a\x16\x06__type\x01w\x04text(\x00\xd7\xed\xd8\xa4\r\x8a\x16\x08__format\x01}\x00(\x00\xd7\xed\xd8\xa4\r\x8a\x16\x07__style\x01w\x00(\x00\xd7\xed\xd8\xa4\r\x8a\x16\x06__mode\x01}\x00(\x00\xd7\xed\xd8\xa4\r\x8a\x16\x08__detail\x01}\x00\x84\xd7\xed\xd8\xa4\r\x8a\x16\xbd\x03Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.\x87\xd7\xed\xd8\xa4\r\x84\x16\x06(\x00\xd7\xed\xd8\xa4\r\xcd\x19\x06__type\x01w\tparagraph(\x00\xd7\xed\xd8\xa4\r\xcd\x19\x08__format\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xcd\x19\x08__indent\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xcd\x19\x05__dir\x01w\x03ltr(\x00\xd7\xed\xd8\xa4\r\xcd\x19\x0c__textFormat\x01}\x00\x07\x00\xd7\xed\xd8\xa4\r\xcd\x19\x01(\x00\xd7\xed\xd8\xa4\r\xd3\x19\x06__type\x01w\x04text(\x00\xd7\xed\xd8\xa4\r\xd3\x19\x08__format\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xd3\x19\x07__style\x01w\x00(\x00\xd7\xed\xd8\xa4\r\xd3\x19\x06__mode\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xd3\x19\x08__detail\x01}\x00\x84\xd7\xed\xd8\xa4\r\xd3\x19\xf1\x02LoremipsumdolorsitametconsecteturadipiscingelitseddoeiusmodtemporincididuntutlaboreetdoloremagnaaliquaUtenimadminimveniamquisnostrudexercitationullamcolaborisnisiutaliquipexeacommodoconsequatDuisauteiruredolorinreprehenderitinvoluptatevelitessecillumdoloreeufugiatnullapariaturExcepteursintoccaecatcupidatatnonproidentsuntinculpaquiofficiadeseruntmollitanimidestlaborum\x87\xd7\xed\xd8\xa4\r\xcd\x19\x06(\x00\xd7\xed\xd8\xa4\r\xca\x1c\x06__type\x01w\tparagraph(\x00\xd7\xed\xd8\xa4\r\xca\x1c\x08__format\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xca\x1c\x08__indent\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xca\x1c\x05__dir\x01w\x03ltr(\x00\xd7\xed\xd8\xa4\r\xca\x1c\x0c__textFormat\x01}\x00\x07\x00\xd7\xed\xd8\xa4\r\xca\x1c\x01(\x00\xd7\xed\xd8\xa4\r\xd0\x1c\x06__type\x01w\x04text(\x00\xd7\xed\xd8\xa4\r\xd0\x1c\x08__format\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xd0\x1c\x07__style\x01w\x00(\x00\xd7\xed\xd8\xa4\r\xd0\x1c\x06__mode\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xd0\x1c\x08__detail\x01}\x00\x84\xd7\xed\xd8\xa4\r\xd0\x1c\xf1\x02LoremipsumdolorsitametconsecteturadipiscingelitseddoeiusmodtemporincididuntutlaboreetdoloremagnaaliquaUtenimadminimveniamquisnostrudexercitationullamcolaborisnisiutaliquipexeacommodoconsequatDuisauteiruredolorinreprehenderitinvoluptatevelitessecillumdoloreeufugiatnullapariaturExcepteursintoccaecatcupidatatnonproidentsuntinculpaquiofficiadeseruntmollitanimidestlaborum\x87\xd7\xed\xd8\xa4\r\xca\x1c\x06(\x00\xd7\xed\xd8\xa4\r\xc7\x1f\x06__type\x01w\tparagraph(\x00\xd7\xed\xd8\xa4\r\xc7\x1f\x08__format\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xc7\x1f\x08__indent\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xc7\x1f\x05__dir\x01w\x03ltr(\x00\xd7\xed\xd8\xa4\r\xc7\x1f\x0c__textFormat\x01}\x00\x07\x00\xd7\xed\xd8\xa4\r\xc7\x1f\x01(\x00\xd7\xed\xd8\xa4\r\xcd\x1f\x06__type\x01w\x04text(\x00\xd7\xed\xd8\xa4\r\xcd\x1f\x08__format\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xcd\x1f\x07__style\x01w\x00(\x00\xd7\xed\xd8\xa4\r\xcd\x1f\x06__mode\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xcd\x1f\x08__detail\x01}\x00\x84\xd7\xed\xd8\xa4\r\xcd\x1f\xf1\x02LoremipsumdolorsitametconsecteturadipiscingelitseddoeiusmodtemporincididuntutlaboreetdoloremagnaaliquaUtenimadminimveniamquisnostrudexercitationullamcolaborisnisiutaliquipexeacommodoconsequatDuisauteiruredolorinreprehenderitinvoluptatevelitessecillumdoloreeufugiatnullapariaturExcepteursintoccaecatcupidatatnonproidentsuntinculpaquiofficiadeseruntmollitanimidestlaborum\x87\xd7\xed\xd8\xa4\r\xc7\x1f\x06(\x00\xd7\xed\xd8\xa4\r\xc4\"\x06__type\x01w\tparagraph(\x00\xd7\xed\xd8\xa4\r\xc4\"\x08__format\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xc4\"\x08__indent\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xc4\"\x05__dir\x01w\x03ltr(\x00\xd7\xed\xd8\xa4\r\xc4\"\x0c__textFormat\x01}\x00\x07\x00\xd7\xed\xd8\xa4\r\xc4\"\x01(\x00\xd7\xed\xd8\xa4\r\xca\"\x06__type\x01w\x04text(\x00\xd7\xed\xd8\xa4\r\xca\"\x08__format\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xca\"\x07__style\x01w\x00(\x00\xd7\xed\xd8\xa4\r\xca\"\x06__mode\x01}\x00(\x00\xd7\xed\xd8\xa4\r\xca\"\x08__detail\x01}\x00\x84\xd7\xed\xd8\xa4\r\xca\"\xbd\x03Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.\x00".to_vec();
        let expected_json: Value = json!({
            "__dir": "ltr",
            "children": [
                {
                "__type": "paragraph",
                "__format": 0,
                "__indent": 0,
                "__dir": "ltr",
                "__textFormat": 0,
                "children": [
                    {
                    "__type": "text",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "text": "LoremipsumdolorsitametconsecteturadipiscingelitseddoeiusmodtemporincididuntutlaboreetdoloremagnaaliquaUtenimadminimveniamquisnostrudexercitationullamcolaborisnisiutaliquipexeacommodoconsequatDuisauteiruredolorinreprehenderitinvoluptatevelitessecillumdoloreeufugiatnullapariaturExcepteursintoccaecatcupidatatnonproidentsuntinculpaquiofficiadeseruntmollitanimidestlaborum"
                    }
                ]
                },
                {
                "__type": "paragraph",
                "__format": 0,
                "__indent": 0,
                "__dir": "ltr",
                "__textFormat": 0,
                "children": [
                    {
                    "__type": "text",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "text": "Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum."
                    }
                ]
                },
                {
                "__type": "paragraph",
                "__format": 0,
                "__indent": 0,
                "__dir": "ltr",
                "__textFormat": 0,
                "children": [
                    {
                    "__type": "text",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "text": "LoremipsumdolorsitametconsecteturadipiscingelitseddoeiusmodtemporincididuntutlaboreetdoloremagnaaliquaUtenimadminimveniamquisnostrudexercitationullamcolaborisnisiutaliquipexeacommodoconsequatDuisauteiruredolorinreprehenderitinvoluptatevelitessecillumdoloreeufugiatnullapariaturExcepteursintoccaecatcupidatatnonproidentsuntinculpaquiofficiadeseruntmollitanimidestlaborum"
                    }
                ]
                },
                {
                "__type": "paragraph",
                "__format": 0,
                "__indent": 0,
                "__dir": "ltr",
                "__textFormat": 0,
                "children": [
                    {
                    "__type": "text",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "text": "LoremipsumdolorsitametconsecteturadipiscingelitseddoeiusmodtemporincididuntutlaboreetdoloremagnaaliquaUtenimadminimveniamquisnostrudexercitationullamcolaborisnisiutaliquipexeacommodoconsequatDuisauteiruredolorinreprehenderitinvoluptatevelitessecillumdoloreeufugiatnullapariaturExcepteursintoccaecatcupidatatnonproidentsuntinculpaquiofficiadeseruntmollitanimidestlaborum"
                    }
                ]
                },
                {
                "__type": "paragraph",
                "__format": 0,
                "__indent": 0,
                "__dir": "ltr",
                "__textFormat": 0,
                "children": [
                    {
                    "__type": "text",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "text": "LoremipsumdolorsitametconsecteturadipiscingelitseddoeiusmodtemporincididuntutlaboreetdoloremagnaaliquaUtenimadminimveniamquisnostrudexercitationullamcolaborisnisiutaliquipexeacommodoconsequatDuisauteiruredolorinreprehenderitinvoluptatevelitessecillumdoloreeufugiatnullapariaturExcepteursintoccaecatcupidatatnonproidentsuntinculpaquiofficiadeseruntmollitanimidestlaborum"
                    }
                ]
                },
                {
                "__type": "paragraph",
                "__format": 0,
                "__indent": 0,
                "__dir": "ltr",
                "__textFormat": 0,
                "children": [
                    {
                    "__type": "text",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "text": "Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum."
                    }
                ]
                },
                {
                "__type": "paragraph",
                "__format": 0,
                "__indent": 0,
                "__dir": "ltr",
                "__textFormat": 0,
                "children": [
                    {
                    "__type": "text",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "text": "LoremipsumdolorsitametconsecteturadipiscingelitseddoeiusmodtemporincididuntutlaboreetdoloremagnaaliquaUtenimadminimveniamquisnostrudexercitationullamcolaborisnisiutaliquipexeacommodoconsequatDuisauteiruredolorinreprehenderitinvoluptatevelitessecillumdoloreeufugiatnullapariaturExcepteursintoccaecatcupidatatnonproidentsuntinculpaquiofficiadeseruntmollitanimidestlaborum"
                    }
                ]
                },
                {
                "__type": "paragraph",
                "__format": 0,
                "__indent": 0,
                "__dir": "ltr",
                "__textFormat": 0,
                "children": [
                    {
                    "__type": "text",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "text": "Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum."
                    }
                ]
                },
                {
                "__type": "paragraph",
                "__format": 0,
                "__indent": 0,
                "__dir": "ltr",
                "__textFormat": 0,
                "children": [
                    {
                    "__type": "text",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "text": "LoremipsumdolorsitametconsecteturadipiscingelitseddoeiusmodtemporincididuntutlaboreetdoloremagnaaliquaUtenimadminimveniamquisnostrudexercitationullamcolaborisnisiutaliquipexeacommodoconsequatDuisauteiruredolorinreprehenderitinvoluptatevelitessecillumdoloreeufugiatnullapariaturExcepteursintoccaecatcupidatatnonproidentsuntinculpaquiofficiadeseruntmollitanimidestlaborum"
                    }
                ]
                },
                {
                "__type": "paragraph",
                "__format": 0,
                "__indent": 0,
                "__dir": "ltr",
                "__textFormat": 0,
                "children": [
                    {
                    "__type": "text",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "text": "LoremipsumdolorsitametconsecteturadipiscingelitseddoeiusmodtemporincididuntutlaboreetdoloremagnaaliquaUtenimadminimveniamquisnostrudexercitationullamcolaborisnisiutaliquipexeacommodoconsequatDuisauteiruredolorinreprehenderitinvoluptatevelitessecillumdoloreeufugiatnullapariaturExcepteursintoccaecatcupidatatnonproidentsuntinculpaquiofficiadeseruntmollitanimidestlaborum"
                    }
                ]
                },
                {
                "__type": "paragraph",
                "__format": 0,
                "__indent": 0,
                "__dir": "ltr",
                "__textFormat": 0,
                "children": [
                    {
                    "__type": "text",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "text": "LoremipsumdolorsitametconsecteturadipiscingelitseddoeiusmodtemporincididuntutlaboreetdoloremagnaaliquaUtenimadminimveniamquisnostrudexercitationullamcolaborisnisiutaliquipexeacommodoconsequatDuisauteiruredolorinreprehenderitinvoluptatevelitessecillumdoloreeufugiatnullapariaturExcepteursintoccaecatcupidatatnonproidentsuntinculpaquiofficiadeseruntmollitanimidestlaborum"
                    }
                ]
                },
                {
                "__type": "paragraph",
                "__format": 0,
                "__indent": 0,
                "__dir": "ltr",
                "__textFormat": 0,
                "children": [
                    {
                    "__type": "text",
                    "__format": 0,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "text": "Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum."
                    }
                ]
                }
            ]
        });

        let result = process_xml_fragment(update_bytes);
        let mut result_buf = String::new();

        Any::Map(Box::new(result)).to_json(&mut result_buf);
        let result_json: Value = from_str(&result_buf).unwrap();

        println!("Result:\n{}", to_string_pretty(&result_json).unwrap());

        assert_json_eq!(result_json, expected_json);
    }
}
