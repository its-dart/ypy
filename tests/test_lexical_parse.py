import json
from copy import deepcopy

import y_py as Y

# This is the original Lexical data
EXPECTED_JSON = json.loads(
    '{"root": {"__dir": "ltr", "__format": "", "__indent": 0, "__type": "root", "__version": 1, "children": [{"__type": "recommendation-wrapper", "__format": 0, "__indent": 0, "__dir": "ltr", "__kind": "write", "children": [{"__type": "paragraph", "__format": 0, "__indent": 0, "__dir": "ltr", "__textFormat": 0, "children": [{"__type": "text", "__format": 0, "__style": "", "__mode": 0, "__detail": 0, "text": "A"}]}, {"__type": "recommendation-buttons", "__kind": "write", "__recommendationDuid": "asdf1234asdf"}]}]}}'
)

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

UPDATE_STR = "\x04\x02Æ\x9fÓ\x95\x0b\x00\x81«Íû´\x01\x0e\x01\x00\x0c\"\x91ÞûÕ\x08\x00¡«Íû´\x01\x17\x01\x00\x08¡\x91ÞûÕ\x08\x00\x01\x00\x02¡\x91ÞûÕ\x08\t\x01\x87Æ\x9fÓ\x95\x0b\x00\x06(\x00\x91ÞûÕ\x08\r\x06__type\x01w\x16recommendation-wrapper(\x00\x91ÞûÕ\x08\r\x08__format\x01}\x00(\x00\x91ÞûÕ\x08\r\x08__indent\x01}\x00!\x00\x91ÞûÕ\x08\r\x05__dir\x01(\x00\x91ÞûÕ\x08\r\x06__kind\x01w\x05write\x01\x00\x91ÞûÕ\x08\r\x01\x00\x02¨\x91ÞûÕ\x08\x0c\x01w\x03ltr¨\x91ÞûÕ\x08\x11\x01w\x03ltr\x81\x91ÞûÕ\x08\x13\x01\x00\x0e\x87\x91ÞûÕ\x08\x18\x06(\x00\x91ÞûÕ\x08'\x06__type\x01w\tparagraph(\x00\x91ÞûÕ\x08'\x08__format\x01}\x00(\x00\x91ÞûÕ\x08'\x08__indent\x01}\x00(\x00\x91ÞûÕ\x08'\x05__dir\x01w\x03ltr(\x00\x91ÞûÕ\x08'\x0c__textFormat\x01}\x00\x07\x00\x91ÞûÕ\x08'\x01(\x00\x91ÞûÕ\x08-\x06__type\x01w\x04text(\x00\x91ÞûÕ\x08-\x08__format\x01}\x00(\x00\x91ÞûÕ\x08-\x07__style\x01w\x00(\x00\x91ÞûÕ\x08-\x06__mode\x01}\x00(\x00\x91ÞûÕ\x08-\x08__detail\x01}\x00\x84\x91ÞûÕ\x08-\x01A\x87\x91ÞûÕ\x08'\x03\tUNDEFINED(\x00\x91ÞûÕ\x084\x06__type\x01w\x16recommendation-buttons(\x00\x91ÞûÕ\x084\x06__kind\x01w\x05write(\x00\x91ÞûÕ\x084\x14__recommendationDuid\x01w\x0casdf1234asdf\x07Á§\xadü\x04\x00!\x01\x04root\x05__dir\x01(\x01\x04root\x08__format\x01w\x00(\x01\x04root\x08__indent\x01}\x00(\x01\x04root\x06__type\x01w\x04root(\x01\x04root\t__version\x01}\x01\x01\x01\x04root\x01\x00\x06\x06«Íû´\x01\x00\x00\r¡Á§\xadü\x04\x00\x01\x81Á§\xadü\x04\x05\x01\x00\x08¡«Íû´\x01\r\x01\x00!\x04Á§\xadü\x04\x02\x00\x01\x05\x07\x91ÞûÕ\x08\x04\x00\r\x11\x01\x13\x03\x18\x0f«Íû´\x01\x01\x009Æ\x9fÓ\x95\x0b\x01\x00\r"
UPDATE_BYTES = [ord(e) for e in UPDATE_STR]


def test_lexical_parse_in_forward_direction():
    """This tests fully converting the Y format to JSON."""
    ydoc = Y.YDoc()
    Y.apply_update(ydoc, UPDATE_BYTES)
    yroot = ydoc.get_xml_fragment("root")

    result_json = {"root": yroot.to_dict()}

    print(f"{json.dumps(result_json, indent=4)}")

    assert EXPECTED_JSON == result_json


def test_lexical_parse_in_reverse_direction():
    """This tests fully converting the Y format to JSON."""
    ydoc = Y.YDoc()
    yroot = ydoc.get_xml_element("root")

    with ydoc.begin_transaction() as txn:
        nodes: list[tuple[Y.YXmlElement | Y.YXmlText | dict, dict]] = [
            (yroot, deepcopy(EXPECTED_JSON["root"]))
        ]
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

    result_json = {"root": yroot.to_dict()}

    print(f"{json.dumps(result_json, indent=4)}")

    assert EXPECTED_JSON == result_json
