#!/usr/bin/env python3
"""
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

Ordinary Solidity storage contracts for exact-byte preservation certificates.
"""
import copy
import json
from check_compiler_functions import SETTINGS
import compiler_contract_corpus as corpus


def function(name, body, parameters=(), *, mutability="", checked=True, visibility="external"):
    if not checked:
        body = "unchecked { " + body + " }"
    return "function " + name + "(" + ",".join("uint256 " + p for p in parameters) + \
        ") " + visibility + " " + mutability + " returns(uint256) { " + body + " }"


def request(storage, functions):
    content = "// SPDX-License-Identifier: GPL-3.0\npragma solidity ^0.8.0; contract C { " + \
        " ".join("uint256 private " + name + ";" for name in storage) + " " + " ".join(functions) + " }\n"
    return source_request(content)


def source_request(content):
    return {"language": "Solidity", "sources": {"Function.sol": {"content": content}}, "settings": copy.deepcopy(SETTINGS)}


def cases():
    get = function("get", "return cell;", mutability="view")
    source, _ = corpus.load(corpus.RECEIVER_PATH)
    return [
        ("cell", request(["cell"], [function("set", "cell = value; return cell;", ("value",)), get])),
        ("pair", request(["first", "second"], [function("setPair", "first = x; second = y; return first + second;",
            ("x", "y"), checked=False), function("getFirst", "return first;", mutability="view"),
            function("getSecond", "return second;", mutability="view")])),
        ("checked_update", request(["cell"], [function("add", "cell = cell + x; return cell;", ("x",)), get])),
        ("rollback", request(["first", "second"], [function("setPair", "first = x; second = first + y; return second;", ("x", "y")),
            function("getFirst", "return first;", mutability="view"), function("getSecond", "return second;", mutability="view")])),
        ("checked_read", request(["first", "second"], [function("sum", "return first + second;", mutability="view")])),
        ("overwrite", request(["cell"], [function("set", "cell = x; cell = y; return cell;", ("x", "y")), get])),
        ("clear", request(["cell"], [function("clear", "cell = uint256(0); return cell;"), get])),
        ("unused_storage", request(["cell"], [function("identity", "return x;", ("x",), mutability="pure")])),
        ("boundaries", request([f"slot{i}" for i in range(8)], [function("setAll",
            " ".join(f"slot{i} = v{i};" for i in range(8)) + " return slot7;", tuple(f"v{i}" for i in range(8))),
            function("getLast", "return slot7;", mutability="view")])),
        ("branch_return", request(["cell"], [function("choose",
            "if (x < y) { return x; } else { return y; }", ("x", "y"), mutability="pure")])),
        ("branch_join", request(["cell"], [function("set",
            "if (x == uint256(0)) { cell = y; } else { cell = x; } return cell;", ("x", "y")), get])),
        ("early_return", request(["cell"], [function("set",
            "if (x != uint256(0)) { return cell; } cell = y; return cell;", ("x", "y")), get])),
        ("nested_branch", request(["cell"], [function("choose",
            "if (x > y) { if (x >= z) { return x; } else { return z; } } else { return y; }",
            ("x", "y", "z"), mutability="pure")])),
        ("branch_rollback", request(["cell"], [function("set",
            "cell = x; if (y <= x) { return cell + y; } else { return cell; }", ("x", "y")), get])),
        ("condition_panic", request(["cell"], [function("set",
            "cell = x; if (x + y < z) { return x; } else { return z; }", ("x", "y", "z")), get])),
        ("sequential_branch", request(["cell"], [function("set",
            "if (x < y) { cell = x; } else { cell = y; } if (cell == uint256(0)) { return z; } return cell;",
            ("x", "y", "z")), get])),
        ("unchecked_branch", request(["cell"], [function("set",
            "if (x < y) { cell = x + y; } else { cell = x - y; } return cell;",
            ("x", "y"), checked=False), get])),
        ("branch_bound", request(["cell"], [function("choose",
            " ".join(f"if (x == uint256({i})) {{ return uint256({i}); }}" for i in range(4)) +
            " return uint256(4);", ("x",), mutability="pure")])),
        ("init_literal", request(["cell = uint256(7)"], [get])),
        ("init_zero", request(["cell = uint256(0)", "unused"], [get])),
        ("init_dependency", request(["first = uint256(7)", "second = first * uint256(3)"],
            [function("get", "return second;", mutability="view")])),
        ("init_forward", request(["first = second + uint256(1)", "second = uint256(9)"],
            [function("getFirst", "return first;", mutability="view"),
             function("getSecond", "return second;", mutability="view")])),
        ("init_self", request(["cell = cell + uint256(1)"], [get])),
        ("init_shift", request(["first = uint256(1) << uint256(255)", "second = first >> uint256(255)"],
            [function("get", "return second;", mutability="view")])),
        ("init_panic", request(["first = second - uint256(1)", "second"],
            [function("get", "return first;", mutability="view")])),
        ("init_bound", request([f"slot{i} = " + ("uint256(1)" if i == 0 else f"slot{i-1} + uint256(1)")
            for i in range(8)], [function("get", "return slot7;", mutability="view")])),
        ("constructor_literal", request(["cell"], ["constructor() { cell = uint256(7); }", get])),
        ("constructor_dependency", request(["first = uint256(7)", "second"],
            ["constructor() { second = first + uint256(1); first = second; }",
             function("get", "return second;", mutability="view")])),
        ("constructor_branch", request(["cell = uint256(7)"],
            ["constructor() { if (cell == uint256(7)) { cell = uint256(8); } else { cell = uint256(9); } }", get])),
        ("constructor_return", request(["cell = uint256(7)"],
            ["constructor() { if (cell == uint256(7)) { return; } cell = uint256(9); }", get])),
        ("constructor_panic", request(["first", "second"],
            ["constructor() { first = uint256(7); second = second - uint256(1); }",
             function("get", "return first;", mutability="view")])),
        ("constructor_unchecked", request(["cell"],
            ["constructor() { unchecked { cell = cell - uint256(1); } }", get])),
        ("constructor_payable", request(["cell"], [get, "constructor() payable { cell = uint256(7); }"])),
        ("constructor_payable_panic", request(["cell"],
            ["constructor() payable { cell = cell - uint256(1); }", get])),
        ("constructor_initializer_panic", request(["cell = uint256(0) - uint256(1)"],
            ["constructor() { unchecked { cell = uint256(7); } }", get])),
        ("boolean_and", request(["cell"], [function("set",
            "cell = x; if (x == uint256(0) && y + z > y) { cell = z; } return cell;", ("x", "y", "z")), get])),
        ("boolean_or", request(["cell"], [function("set",
            "cell = x; if (x == uint256(0) || y + z > y) { cell = z; } return cell;", ("x", "y", "z")), get])),
        ("boolean_precedence", request(["cell"], [function("choose",
            "if (!(x < y) || y < z && x == uint256(0)) { return x; } else { return y; }",
            ("x", "y", "z"), mutability="pure")])),
        ("boolean_parentheses", request(["cell"], [function("set",
            "if ((x == uint256(0) || y == uint256(0)) && z != uint256(0)) { cell = z; } return cell;",
            ("x", "y", "z")), get])),
        ("boolean_unchecked", request(["cell"], [function("set",
            "if (x == uint256(0) || y + z > y) { cell = z; } return cell;",
            ("x", "y", "z"), checked=False), get])),
        ("constructor_boolean_skip", request(["cell"],
            ["constructor() { if (true || cell - uint256(1) == uint256(0)) { cell = uint256(7); } }", get])),
        ("constructor_boolean_panic", request(["cell"],
            ["constructor() { if (false || cell - uint256(1) == uint256(0)) { cell = uint256(7); } }", get])),
        ("public_maximum", request(["cell = type(uint256).max"],
            [function("get", "return cell;", mutability="view", visibility="public")])),
        (corpus.RECEIVER_CASE, source_request(source)),
        ("packed_flags", source_request("""// SPDX-License-Identifier: GPL-3.0
pragma solidity *; contract C {
            bool private left; bool private right;
            function set(bool value) external { right = value; }
            function get() external view returns(uint256) {
                if (left) { return uint256(1); } return uint256(0);
            }
        }""")),
        ("mixed_storage", source_request("""// SPDX-License-Identifier: GPL-3.0
pragma solidity *; contract C {
            bool private left; uint256 private word; bool private right;
            function set(bool flag, uint256 value) external payable { right = flag; word = value; return; }
            function get() external view returns(uint256) { return word; }
        }""")),
        ("receive_only", source_request("""// SPDX-License-Identifier: GPL-3.0
pragma solidity *; contract C {
            bool private gate;
            constructor() { gate = true; }
            receive() external payable { if (gate) { return; } revert(); }
        }""")),
        ("boolean_returns", source_request("""// SPDX-License-Identifier: GPL-3.0
pragma solidity *; contract C {
            bool private gate;
            function fail(bool value) external { if (value) { revert(); } gate = value; }
            function early(bool value) external { if (value) { return; } gate = value; }
        }""")),
        ("constructor_revert", source_request("""// SPDX-License-Identifier: GPL-3.0
pragma solidity *; contract C {
            bool private gate;
            constructor() { gate = true; revert(); }
            receive() external payable { if (!gate) { revert(); } }
        }""")),
    ]


def rejection_cases():
    # The current source model distinguishes a static SSTORE fault from the
    # empty revert emitted after dead-store elimination. Keep the actual native
    # compilation rejected until that observation boundary is separately reviewed.
    return [("static_store_before_revert", source_request("""// SPDX-License-Identifier: GPL-3.0
pragma solidity *; contract C {
        bool private gate;
        function fail(bool value) external { gate = value; revert(); }
    }"""))]


def write_cases(output):
    output.mkdir(parents=True, exist_ok=False)
    records = []
    for name, data in cases():
        filename = name + ".json"
        (output / filename).write_text(json.dumps(data, sort_keys=True, separators=(",", ":")) + "\n")
        records.append({"case": name, "request": filename})
    (output / "manifest.json").write_text(json.dumps({"cases": records}, indent=2) + "\n")
    return [output / record["request"] for record in records]
