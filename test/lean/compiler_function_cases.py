#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Ordinary Solidity source fixtures for universal exact-runtime certificates.
"""
import copy
import json
from check_compiler_functions import SETTINGS


def request(expression, parameters=("x", "y"), *, checked=False):
    body = "return " + expression + ";"
    if not checked:
        body = "unchecked { " + body + " }"
    source = "// SPDX-License-Identifier: GPL-3.0\npragma solidity ^0.8.0; contract C { function f(" + ",".join(
        "uint256 " + p for p in parameters) + ") external pure returns (uint256) { " + body + " } }\n"
    return {"language": "Solidity", "sources": {"Function.sol": {"content": source}}, "settings": copy.deepcopy(SETTINGS)}


def cases():
    result = [("identity", request("x", ("x",))), ("constant", request("uint256(42)", ())),
              ("zero", request("uint256(0)", ())), ("not", request("~x", ("x",)))]
    for name, op in (("add", "+"), ("sub", "-"), ("mul", "*"), ("and", "&"), ("or", "|"),
                     ("xor", "^"), ("shl", "<<"), ("shr", ">>")):
        result.append((name, request("x " + op + " y")))
    for name, expr in (("self_sub", "x - x"), ("self_xor", "x ^ x"), ("self_and", "x & x"),
                       ("self_or", "x | x"), ("add_zero", "x + uint256(0)"), ("mul_one", "x * uint256(1)"),
                       ("mul_zero", "x * uint256(0)"), ("double_not", "~~x"),
                       ("shl_256", "x << uint256(256)"), ("shr_max", "x >> uint256(" + str(2**256-1) + ")"),
                       ("wrap", "uint256(" + str(2**256-1) + ") + uint256(1)")):
        result.append((name, request(expr, ("x",))))
    result.append(("nested", request("(x + y) ^ (y - x)")))
    result.append(("last_parameter", request("h", tuple("abcdefgh"))))
    result.append(("cancel_add", request("(x + y) - y")))
    checked_names = {"add", "sub", "mul", "self_sub", "add_zero", "mul_one", "mul_zero",
                     "not", "shl_256", "shr_max", "wrap", "nested", "last_parameter", "cancel_add"}
    for name, data in list(result):
        if name in checked_names:
            checked = copy.deepcopy(data)
            content = checked["sources"]["Function.sol"]["content"]
            checked["sources"]["Function.sol"]["content"] = content.replace("unchecked { return", "return").replace("; } } }", "; } }")
            result.append(("checked_" + name, checked))
    for name, expr in (("cancel_sub", "(x - y) + y"), ("nested_mul", "(x + y) * y"),
                       ("underflow", "uint256(0) - x"), ("multiply_boundary", "x * uint256(2)"),
                       ("not_add", "(~x) + y"), ("bitwise_add", "(x & y) + y"),
                       ("shift_add", "(x << y) + y")):
        result.append(("checked_" + name, request(expr, checked=True)))
    result.extend([
        ("integer_return_zero", request("0", (), checked=True)),
        ("integer_return_maximum", request(str(2**256 - 1), ())),
        ("integer_return_hexadecimal", request("0x1234", ("ignored",), checked=True)),
    ])
    return result


def write_cases(output):
    output.mkdir(parents=True, exist_ok=False)
    records = []
    for name, data in cases():
        filename = name + ".json"
        (output / filename).write_text(json.dumps(data, sort_keys=True, separators=(",", ":")) + "\n")
        records.append({"case": name, "request": filename})
    (output / "manifest.json").write_text(json.dumps({"cases": records}, indent=2) + "\n")
    return [output / r["request"] for r in records]
