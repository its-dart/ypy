import y_py as Y

import pytest

# this variable is the markdown version of this data, just for reference--it is not used directly in the tests
MARKDOWN_FOR_REFERENCE = """
a *b*

1. c
   1. d

e
""".strip()

# this is the correctly parsed data
LEXICAL_DATA = {
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
                    "text": "a ",
                },
                {
                    "__type": "text",
                    "__format": 1,
                    "__style": "",
                    "__mode": 0,
                    "__detail": 0,
                    "text": "b",
                },
            ],
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
                            "text": "c",
                        }
                    ],
                },
                {
                    "__type": "listitem",
                    "__format": 0,
                    "__indent": 0,
                    "__dir": None,
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
                                            "text": "d",
                                        }
                                    ],
                                }
                            ],
                        }
                    ],
                },
            ],
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
                    "text": "e",
                }
            ],
        },
    ],
}

# this is the Y update representation of the same data
RAW_LEXICAL_STATE_AS_UPDATE = b'\x01a\x9c\xb5\xe4\xcf\x0e\x00(\x01\x04root\x05__dir\x01w\x03ltr\x07\x01\x04root\x06(\x00\x9c\xb5\xe4\xcf\x0e\x01\x06__type\x01w\tparagraph(\x00\x9c\xb5\xe4\xcf\x0e\x01\x08__format\x01}\x00(\x00\x9c\xb5\xe4\xcf\x0e\x01\x08__indent\x01}\x00(\x00\x9c\xb5\xe4\xcf\x0e\x01\x05__dir\x01w\x03ltr\x07\x00\x9c\xb5\xe4\xcf\x0e\x01\x01(\x00\x9c\xb5\xe4\xcf\x0e\x06\x06__type\x01w\x04text(\x00\x9c\xb5\xe4\xcf\x0e\x06\x08__format\x01}\x00(\x00\x9c\xb5\xe4\xcf\x0e\x06\x07__style\x01w\x00(\x00\x9c\xb5\xe4\xcf\x0e\x06\x06__mode\x01}\x00(\x00\x9c\xb5\xe4\xcf\x0e\x06\x08__detail\x01}\x00\x84\x9c\xb5\xe4\xcf\x0e\x06\x01a\x87\x9c\xb5\xe4\xcf\x0e\x01\x06(\x00\x9c\xb5\xe4\xcf\x0e\r\x06__type\x01w\x04list(\x00\x9c\xb5\xe4\xcf\x0e\r\x08__format\x01}\x00(\x00\x9c\xb5\xe4\xcf\x0e\r\x08__indent\x01}\x00!\x00\x9c\xb5\xe4\xcf\x0e\r\x05__dir\x01(\x00\x9c\xb5\xe4\xcf\x0e\r\n__listType\x01w\x06number(\x00\x9c\xb5\xe4\xcf\x0e\r\x05__tag\x01w\x02ol(\x00\x9c\xb5\xe4\xcf\x0e\r\x07__start\x01}\x01\x07\x00\x9c\xb5\xe4\xcf\x0e\r\x06(\x00\x9c\xb5\xe4\xcf\x0e\x15\x06__type\x01w\x08listitem(\x00\x9c\xb5\xe4\xcf\x0e\x15\x08__format\x01}\x00(\x00\x9c\xb5\xe4\xcf\x0e\x15\x08__indent\x01}\x00!\x00\x9c\xb5\xe4\xcf\x0e\x15\x05__dir\x01(\x00\x9c\xb5\xe4\xcf\x0e\x15\x07__value\x01}\x01\x01\x00\x9c\xb5\xe4\xcf\x0e\x15\x01\x00\x05\x81\x9c\xb5\xe4\xcf\x0e\x1b\x01\x84\x9c\xb5\xe4\xcf\x0e\x0c\x01 \x87\x9c\xb5\xe4\xcf\x0e"\x01(\x00\x9c\xb5\xe4\xcf\x0e#\x06__type\x01w\x04text(\x00\x9c\xb5\xe4\xcf\x0e#\x08__format\x01}\x01(\x00\x9c\xb5\xe4\xcf\x0e#\x07__style\x01w\x00(\x00\x9c\xb5\xe4\xcf\x0e#\x06__mode\x01}\x00(\x00\x9c\xb5\xe4\xcf\x0e#\x08__detail\x01}\x00\x84\x9c\xb5\xe4\xcf\x0e#\x01b\xa1\x9c\xb5\xe4\xcf\x0e\x11\x01\xa1\x9c\xb5\xe4\xcf\x0e\x19\x01\xa8\x9c\xb5\xe4\xcf\x0e*\x01w\x03ltr\xa8\x9c\xb5\xe4\xcf\x0e+\x01w\x03ltr\x87\x9c\xb5\xe4\xcf\x0e!\x01(\x00\x9c\xb5\xe4\xcf\x0e.\x06__type\x01w\x04text(\x00\x9c\xb5\xe4\xcf\x0e.\x08__format\x01}\x00(\x00\x9c\xb5\xe4\xcf\x0e.\x07__style\x01w\x00(\x00\x9c\xb5\xe4\xcf\x0e.\x06__mode\x01}\x00(\x00\x9c\xb5\xe4\xcf\x0e.\x08__detail\x01}\x00\x84\x9c\xb5\xe4\xcf\x0e.\x01c\x81\x9c\xb5\xe4\xcf\x0e\x15\x01\x00\x05\x87\x9c\xb5\xe4\xcf\x0e5\x06(\x00\x9c\xb5\xe4\xcf\x0e;\x06__type\x01w\x08listitem(\x00\x9c\xb5\xe4\xcf\x0e;\x08__format\x01}\x00(\x00\x9c\xb5\xe4\xcf\x0e;\x08__indent\x01}\x00!\x00\x9c\xb5\xe4\xcf\x0e;\x05__dir\x01(\x00\x9c\xb5\xe4\xcf\x0e;\x07__value\x01}\x02\x07\x00\x9c\xb5\xe4\xcf\x0e;\x06(\x00\x9c\xb5\xe4\xcf\x0eA\x06__type\x01w\x04list(\x00\x9c\xb5\xe4\xcf\x0eA\x08__format\x01}\x00(\x00\x9c\xb5\xe4\xcf\x0eA\x08__indent\x01}\x00(\x00\x9c\xb5\xe4\xcf\x0eA\x05__dir\x01w\x03ltr(\x00\x9c\xb5\xe4\xcf\x0eA\n__listType\x01w\x06number(\x00\x9c\xb5\xe4\xcf\x0eA\x05__tag\x01w\x02ol(\x00\x9c\xb5\xe4\xcf\x0eA\x07__start\x01}\x01\x07\x00\x9c\xb5\xe4\xcf\x0eA\x06(\x00\x9c\xb5\xe4\xcf\x0eI\x06__type\x01w\x08listitem(\x00\x9c\xb5\xe4\xcf\x0eI\x08__format\x01}\x00(\x00\x9c\xb5\xe4\xcf\x0eI\x08__indent\x01}\x00!\x00\x9c\xb5\xe4\xcf\x0eI\x05__dir\x01(\x00\x9c\xb5\xe4\xcf\x0eI\x07__value\x01}\x01\xa8\x9c\xb5\xe4\xcf\x0eM\x01w\x03ltr\x07\x00\x9c\xb5\xe4\xcf\x0eI\x01(\x00\x9c\xb5\xe4\xcf\x0eP\x06__type\x01w\x04text(\x00\x9c\xb5\xe4\xcf\x0eP\x08__format\x01}\x00(\x00\x9c\xb5\xe4\xcf\x0eP\x07__style\x01w\x00(\x00\x9c\xb5\xe4\xcf\x0eP\x06__mode\x01}\x00(\x00\x9c\xb5\xe4\xcf\x0eP\x08__detail\x01}\x00\x84\x9c\xb5\xe4\xcf\x0eP\x01d\x81\x9c\xb5\xe4\xcf\x0eI\x01\x00\x05\x81\x9c\xb5\xe4\xcf\x0e;\x01\x00\x05\xa8\x9c\xb5\xe4\xcf\x0e?\x01~\x87\x9c\xb5\xe4\xcf\x0e\r\x06(\x00\x9c\xb5\xe4\xcf\x0ed\x06__type\x01w\tparagraph(\x00\x9c\xb5\xe4\xcf\x0ed\x08__format\x01}\x00(\x00\x9c\xb5\xe4\xcf\x0ed\x08__indent\x01}\x00!\x00\x9c\xb5\xe4\xcf\x0ed\x05__dir\x01\xa8\x9c\xb5\xe4\xcf\x0eh\x01w\x03ltr\x07\x00\x9c\xb5\xe4\xcf\x0ed\x01(\x00\x9c\xb5\xe4\xcf\x0ej\x06__type\x01w\x04text(\x00\x9c\xb5\xe4\xcf\x0ej\x08__format\x01}\x00(\x00\x9c\xb5\xe4\xcf\x0ej\x07__style\x01w\x00(\x00\x9c\xb5\xe4\xcf\x0ej\x06__mode\x01}\x00(\x00\x9c\xb5\xe4\xcf\x0ej\x08__detail\x01}\x00\x84\x9c\xb5\xe4\xcf\x0ej\x01e\x01\x9c\xb5\xe4\xcf\x0e\t\x11\x01\x19\x01\x1b\x07*\x025\x06?\x01M\x01W\x0ch\x01'


def parse_node_recursive(elem):
    """Try to parse the tree using the yet unimplemented `to_delta` method, which is the only way to get it to work in JS.
    This test could be fixed by implementing `to_delta`."""
    result = dict(elem.attributes())

    if hasattr(elem, "first_child"):
        children = []
        current_child = elem.first_child
        while current_child:
            children.append(parse_node_recursive(current_child))
            current_child = current_child.next_sibling
        result["children"] = children

    if hasattr(elem, "to_delta"):
        children = []
        for item in elem.to_delta():
            insert = item.insert
            if not insert:
                continue

            if isinstance(insert, str):
                children[-1]["text"] = insert
                continue

            children.append(parse_node_recursive(insert))
        result["children"] = children

    return result


@pytest.mark.skip("not working yet")
def test_lexical_parse():
    """This is the main test, and the only one that really needs to pass. It tests fully converting the Y format to JSON."""
    doc = Y.YDoc()
    Y.apply_update(doc, RAW_LEXICAL_STATE_AS_UPDATE)
    root = doc.get_xml_element("root")

    assert LEXICAL_DATA == parse_node_recursive(root)
