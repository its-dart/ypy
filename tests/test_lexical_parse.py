import json
from copy import deepcopy

import y_py as Y

# This is the original Lexical data
EXPECTED_JSON = json.loads('{"root": {"__dir": "ltr", "children": [{"__type": "paragraph", "__format": 0, "__indent": 0, "__dir": "ltr", "children": [{"__type": "text", "__format": 0, "__style": "", "__mode": 0, "__detail": 0, "text": "a "}, {"__type": "text", "__format": 1, "__style": "", "__mode": 0, "__detail": 0, "text": "b"}]}, {"__type": "list", "__format": 0, "__indent": 0, "__dir": "ltr", "__listType": "number", "__tag": "ol", "__start": 1, "children": [{"__type": "listitem", "__format": 0, "__indent": 0, "__dir": "ltr", "__value": 1, "children": [{"__type": "text", "__format": 0, "__style": "", "__mode": 0, "__detail": 0, "text": "c"}]}, {"__type": "listitem", "__format": 0, "__indent": 0, "__dir": null, "__value": 2, "children": [{"__type": "list", "__format": 0, "__indent": 0, "__dir": "ltr", "__listType": "number", "__tag": "ol", "__start": 1, "children": [{"__type": "listitem", "__format": 0, "__indent": 0, "__dir": "ltr", "__value": 1, "children": [{"__type": "text", "__format": 0, "__style": "", "__mode": 0, "__detail": 0, "text": "d"}]}]}]}]}, {"__type": "paragraph", "__format": 0, "__indent": 0, "__dir": "ltr", "children": [{"__type": "text", "__format": 0, "__style": "", "__mode": 0, "__detail": 0, "text": "e"}]}]}}')

# This is the Y update representation of the Lexical data
#
# YDoc loaded from Lexical data is represented internally as a tree of YXmlElement, YXmlText, YMap and SplittableString elements. All leaf nodes are always built with using YMap and SplittableString that are used to represent node attributes and text content respectively:
# YXmlElement
#     YXmlText
#         YMap             |___ Text leaf node
#         SplittableString |
#         YMap             |___ Text leaf node
#         SplittableString |
#     YXmlText
#         YXmlText
#             YMap             |___ Text leaf node
#             SplittableString |
#         YXmlText
#             YXmlText
#                 YXmlText
#                     YMap             |___ Text leaf node
#                     SplittableString |
#     YXmlText
#         YMap             |___ Text leaf node
#         SplittableString |

UPDATE_STR = '\x01a\x9cµäÏ\x0e\x00(\x01\x04root\x05__dir\x01w\x03ltr\x07\x01\x04root\x06(\x00\x9cµäÏ\x0e\x01\x06__type\x01w\tparagraph(\x00\x9cµäÏ\x0e\x01\x08__format\x01}\x00(\x00\x9cµäÏ\x0e\x01\x08__indent\x01}\x00(\x00\x9cµäÏ\x0e\x01\x05__dir\x01w\x03ltr\x07\x00\x9cµäÏ\x0e\x01\x01(\x00\x9cµäÏ\x0e\x06\x06__type\x01w\x04text(\x00\x9cµäÏ\x0e\x06\x08__format\x01}\x00(\x00\x9cµäÏ\x0e\x06\x07__style\x01w\x00(\x00\x9cµäÏ\x0e\x06\x06__mode\x01}\x00(\x00\x9cµäÏ\x0e\x06\x08__detail\x01}\x00\x84\x9cµäÏ\x0e\x06\x01a\x87\x9cµäÏ\x0e\x01\x06(\x00\x9cµäÏ\x0e\r\x06__type\x01w\x04list(\x00\x9cµäÏ\x0e\r\x08__format\x01}\x00(\x00\x9cµäÏ\x0e\r\x08__indent\x01}\x00!\x00\x9cµäÏ\x0e\r\x05__dir\x01(\x00\x9cµäÏ\x0e\r\n__listType\x01w\x06number(\x00\x9cµäÏ\x0e\r\x05__tag\x01w\x02ol(\x00\x9cµäÏ\x0e\r\x07__start\x01}\x01\x07\x00\x9cµäÏ\x0e\r\x06(\x00\x9cµäÏ\x0e\x15\x06__type\x01w\x08listitem(\x00\x9cµäÏ\x0e\x15\x08__format\x01}\x00(\x00\x9cµäÏ\x0e\x15\x08__indent\x01}\x00!\x00\x9cµäÏ\x0e\x15\x05__dir\x01(\x00\x9cµäÏ\x0e\x15\x07__value\x01}\x01\x01\x00\x9cµäÏ\x0e\x15\x01\x00\x05\x81\x9cµäÏ\x0e\x1b\x01\x84\x9cµäÏ\x0e\x0c\x01 \x87\x9cµäÏ\x0e"\x01(\x00\x9cµäÏ\x0e#\x06__type\x01w\x04text(\x00\x9cµäÏ\x0e#\x08__format\x01}\x01(\x00\x9cµäÏ\x0e#\x07__style\x01w\x00(\x00\x9cµäÏ\x0e#\x06__mode\x01}\x00(\x00\x9cµäÏ\x0e#\x08__detail\x01}\x00\x84\x9cµäÏ\x0e#\x01b¡\x9cµäÏ\x0e\x11\x01¡\x9cµäÏ\x0e\x19\x01¨\x9cµäÏ\x0e*\x01w\x03ltr¨\x9cµäÏ\x0e+\x01w\x03ltr\x87\x9cµäÏ\x0e!\x01(\x00\x9cµäÏ\x0e.\x06__type\x01w\x04text(\x00\x9cµäÏ\x0e.\x08__format\x01}\x00(\x00\x9cµäÏ\x0e.\x07__style\x01w\x00(\x00\x9cµäÏ\x0e.\x06__mode\x01}\x00(\x00\x9cµäÏ\x0e.\x08__detail\x01}\x00\x84\x9cµäÏ\x0e.\x01c\x81\x9cµäÏ\x0e\x15\x01\x00\x05\x87\x9cµäÏ\x0e5\x06(\x00\x9cµäÏ\x0e;\x06__type\x01w\x08listitem(\x00\x9cµäÏ\x0e;\x08__format\x01}\x00(\x00\x9cµäÏ\x0e;\x08__indent\x01}\x00!\x00\x9cµäÏ\x0e;\x05__dir\x01(\x00\x9cµäÏ\x0e;\x07__value\x01}\x02\x07\x00\x9cµäÏ\x0e;\x06(\x00\x9cµäÏ\x0eA\x06__type\x01w\x04list(\x00\x9cµäÏ\x0eA\x08__format\x01}\x00(\x00\x9cµäÏ\x0eA\x08__indent\x01}\x00(\x00\x9cµäÏ\x0eA\x05__dir\x01w\x03ltr(\x00\x9cµäÏ\x0eA\n__listType\x01w\x06number(\x00\x9cµäÏ\x0eA\x05__tag\x01w\x02ol(\x00\x9cµäÏ\x0eA\x07__start\x01}\x01\x07\x00\x9cµäÏ\x0eA\x06(\x00\x9cµäÏ\x0eI\x06__type\x01w\x08listitem(\x00\x9cµäÏ\x0eI\x08__format\x01}\x00(\x00\x9cµäÏ\x0eI\x08__indent\x01}\x00!\x00\x9cµäÏ\x0eI\x05__dir\x01(\x00\x9cµäÏ\x0eI\x07__value\x01}\x01¨\x9cµäÏ\x0eM\x01w\x03ltr\x07\x00\x9cµäÏ\x0eI\x01(\x00\x9cµäÏ\x0eP\x06__type\x01w\x04text(\x00\x9cµäÏ\x0eP\x08__format\x01}\x00(\x00\x9cµäÏ\x0eP\x07__style\x01w\x00(\x00\x9cµäÏ\x0eP\x06__mode\x01}\x00(\x00\x9cµäÏ\x0eP\x08__detail\x01}\x00\x84\x9cµäÏ\x0eP\x01d\x81\x9cµäÏ\x0eI\x01\x00\x05\x81\x9cµäÏ\x0e;\x01\x00\x05¨\x9cµäÏ\x0e?\x01~\x87\x9cµäÏ\x0e\r\x06(\x00\x9cµäÏ\x0ed\x06__type\x01w\tparagraph(\x00\x9cµäÏ\x0ed\x08__format\x01}\x00(\x00\x9cµäÏ\x0ed\x08__indent\x01}\x00!\x00\x9cµäÏ\x0ed\x05__dir\x01¨\x9cµäÏ\x0eh\x01w\x03ltr\x07\x00\x9cµäÏ\x0ed\x01(\x00\x9cµäÏ\x0ej\x06__type\x01w\x04text(\x00\x9cµäÏ\x0ej\x08__format\x01}\x00(\x00\x9cµäÏ\x0ej\x07__style\x01w\x00(\x00\x9cµäÏ\x0ej\x06__mode\x01}\x00(\x00\x9cµäÏ\x0ej\x08__detail\x01}\x00\x84\x9cµäÏ\x0ej\x01e\x01\x9cµäÏ\x0e\t\x11\x01\x19\x01\x1b\x07*\x025\x06?\x01M\x01W\x0ch\x01'
UPDATE_BYTES = [ord(e) for e in UPDATE_STR]

def test_lexical_parse_in_forward_direction():
    """This tests fully converting the Y format to JSON."""
    ydoc = Y.YDoc()
    Y.apply_update(ydoc, UPDATE_BYTES)
    yroot = ydoc.get_xml_fragment("root")
    root_json = yroot.to_dict()

    print(f"{json.dumps(root_json, indent=4)}")

    assert EXPECTED_JSON == {"root": root_json}


def test_lexical_parse_in_reverse_direction():
    """This tests fully converting the Y format to JSON."""
    ydoc = Y.YDoc()
    yroot = ydoc.get_xml_element("root")

    with ydoc.begin_transaction() as txn:
        nodes: list[tuple[Y.YXmlElement | Y.YXmlText | dict, dict]] = [(yroot, deepcopy(EXPECTED_JSON["root"]))]
        while nodes:
            ynode, node_json = nodes.pop(0)
            for key, value in node_json.items():
                if key == "children" and isinstance(value, list):
                    for child in value:
                        if "text" in child:
                            text = child["text"]
                            del child["text"]
                            ynode.push_attributes(txn, child)
                            ynode.push(txn, text)
                        else:
                            ychild = ynode.push_xml_text(txn)
                            nodes.append((ychild, child))
                else:
                    ynode.set_attribute(txn, key, value)

    root_json = yroot.to_dict()

    print(f"{json.dumps(root_json, indent=4)}")

    assert EXPECTED_JSON == {"root": root_json}
