#!/usr/bin/env python3
"""
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

Complete contract fixtures, including overloads and distinct/shared bodies.
"""
import copy
import json
import compiler_contract_corpus as corpus
from check_compiler_functions import SETTINGS


def function(name, expression, parameters=("x", "y"), *, checked=False, payable=False):
    body = "return " + expression + ";"
    if not checked:
        body = "unchecked { " + body + " }"
    return "function " + name + "(" + ",".join("uint256 " + p for p in parameters) + \
        ") external " + ("payable" if payable else "pure") + " returns(uint256) { " + body + " }"


def request(functions):
    content = "// SPDX-License-Identifier: GPL-3.0\npragma solidity ^0.8.0; contract C { " + " ".join(functions) + " }\n"
    return source_request(content)


def source_request(content, target=None):
    settings = copy.deepcopy(SETTINGS)
    if target is not None:
        settings["outputSelection"] = {"Function.sol": {target: settings["outputSelection"]["*"]["*"]}}
    return {"language": "Solidity", "sources": {"Function.sol": {"content": content}}, "settings": settings}


def address_function(name, value, parameters=()):
    return "function " + name + "(" + ",".join("uint256 " + p for p in parameters) + \
        ") external pure returns(address) { return address(" + str(value) + "); }"


def literal_function(name, return_type, expression, parameters=()):
    return "function " + name + "(" + ",".join("uint256 " + p for p in parameters) + \
        ") external pure returns(" + return_type + ") { return " + expression + "; }"


def selected_constants():
    return source_request("// Copyright (C) 2026 OKcontract Pte. Ltd.\n"
        "// SPDX-License-Identifier: GPL-3.0\npragma solidity ^0.8.0;\n"
        "contract A { " + address_function("implementation", 1) + " }\n"
        "contract B { " + address_function("implementation", 2) + " }\n", "A")


def with_metadata(req):
    from check_compiler_contracts import IPFS_METADATA
    result = copy.deepcopy(req)
    result["settings"]["metadata"] = copy.deepcopy(IPFS_METADATA)
    return result


def raw_return(name, value, parameters="", *, mutability="pure", result="uint256"):
    return (f"function {name}({parameters}) external {mutability} returns({result}) "
            f"{{ assembly {{ mstore(0, {value}) return(0, 32) }} }}")


def cases():
    return [
        ("single", request([function("f", "x", ("x",))])),
        ("pair", request([function("f", "x", ("x",)), function("g", "x + y")])),
        ("checked", request([function("add", "x + y", checked=True),
            function("sub", "x - y", checked=True), function("mul", "x * y", checked=True)])),
        ("overloaded", request([function("f", "uint256(42)", ()),
            function("f", "~x", ("x",)), function("f", "x ^ y")])),
        ("shared", request([function("f", "x + y"), function("g", "x + y"),
            function("h", "x & y")])),
        ("eight", request([function("a", "uint256(0)", ()), function("b", "x", ("x",)),
            function("c", "~x", ("x",)), function("d", "x & y"), function("e", "x | y"),
            function("f", "x ^ y"), function("g", "x << y"), function("h", "h", tuple("abcdefgh"))])),
        (corpus.CASE, source_request(corpus.load()[0])),
        (corpus.BEACON_CASE, source_request(corpus.load(corpus.BEACON_PATH)[0], corpus.BEACON_TARGET)),
        ("address-boundaries", request([address_function("zero", 0),
            address_function("maximum", 2**160 - 1, ("ignored",)), function("word", "x", ("x",))])),
        ("selected-constant", selected_constants()),
        (corpus.CLASHING_CASE, source_request(corpus.load(corpus.CLASHING_PATH)[0], corpus.CLASHING_TARGET)),
        ("boolean-literals", request([literal_function("yes", "bool", "true"),
            literal_function("no", "bool", "false", ("ignored",))])),
        ("bare-address-boundaries", request([literal_function("zero", "address", "0x" + "0" * 40),
            literal_function("numeric", "address", "0x" + "9" * 40)])),
        (corpus.CLASHING_CASE + "-metadata", with_metadata(source_request(
            corpus.load(corpus.CLASHING_PATH)[0], corpus.CLASHING_TARGET))),
        ("checked-metadata", with_metadata(request([function("add", "x + y", checked=True),
            function("sub", "x - y", checked=True), function("mul", "x * y", checked=True)]))),
        (corpus.PAYABLE_CASE, with_metadata(source_request(
            corpus.load(corpus.PAYABLE_PATH)[0], corpus.CLASHING_TARGET))),
        ("payable-checked", with_metadata(request([
            function("add", "x + y", checked=True, payable=True),
            function("sub", "x - y", payable=True), function("id", "x", ("x",))]))),
        ("payable-only", request([function("f", "x", ("x",), payable=True)])),
        ("empty", request([])),
        ("empty-metadata", with_metadata(request([]))),
        (corpus.EMPTY_BEACON_CASE, with_metadata(source_request(
            corpus.load(corpus.BEACON_PATH, corpus.EMPTY_BEACON_TARGET)[0], corpus.EMPTY_BEACON_TARGET))),
        (corpus.NO_RETURN_CASE, source_request(corpus.load(corpus.NO_RETURN_PATH)[0], corpus.NO_RETURN_TARGET)),
        (corpus.NO_RETURN_CASE + "-metadata", with_metadata(source_request(
            corpus.load(corpus.NO_RETURN_PATH)[0], corpus.NO_RETURN_TARGET))),
        ("mixed-empty-expression", with_metadata(request([
            "function ignore(bytes4 id, uint256 ignored) external view {}", function("word", "x", ("x",))]))),
        ("payable-empty-bytes", request([
            "function ignore(bytes4 first, bytes4 second) external payable {}",
            "function rejectValue() external pure {}"])),
        ("empty-word-bodies", request([
            "function ignore(uint256 ignored) public pure {}", "function noArguments() external view {}"])),
        (corpus.RAW_RETURN_CASE, source_request(corpus.load(corpus.RAW_RETURN_PATH)[0], corpus.RAW_RETURN_TARGET)),
        (corpus.RAW_RETURN_CASE + "-metadata", with_metadata(source_request(
            corpus.load(corpus.RAW_RETURN_PATH)[0], corpus.RAW_RETURN_TARGET))),
        ("mixed-raw-empty-expression", request([
            raw_return("raw", 2**256 - 1, "bytes4", result="bool"),
            "function ignore(bytes4) external view {}", function("word", "x", ("x",))])),
        ("raw-return-boundaries", with_metadata(request([
            raw_return("zero", 0), raw_return("wideAddress", 2**256 - 1, result="address"),
            raw_return("bytesInOrder", "0x" + bytes(range(32)).hex(), mutability="payable")]))),
        ("raw-return-argument-slots", request([
            raw_return("slots", 7, "bytes4,bytes4,uint256", mutability="view", result="bool")])),
        (corpus.BYTES32_CASE, source_request(corpus.load(corpus.BYTES32_PATH)[0])),
        (corpus.BYTES32_CASE + "-metadata", with_metadata(source_request(corpus.load(corpus.BYTES32_PATH)[0]))),
        ("bytes32-boundaries", request([
            literal_function("empty", "bytes32", 'bytes32("")'),
            literal_function("one", "bytes32", 'bytes32("!")', ("ignored",)),
            literal_function("full", "bytes32", 'bytes32("0123456789ABCDEFGHIJKLMNOPQRSTUV")')])),
        ("bytes32-payable-unchecked", with_metadata(request([
            'function f(uint256 ignored) external payable returns(bytes32) { unchecked { return bytes32("a /* b */ // c"); } }',
            function("word", "x", ("x",))]))),
        (corpus.INTEGER_CASE, source_request(corpus.load(corpus.INTEGER_PATH)[0])),
        (corpus.INTEGER_CASE + "-metadata", with_metadata(source_request(corpus.load(corpus.INTEGER_PATH)[0]))),
        ("integer-return-boundaries", request([
            function("zero", "0", (), checked=True),
            function("maximum", str(2**256 - 1), (), checked=True),
            function("hexadecimal", "0x1234", ("ignored",))])),
        ("integer-return-payable", with_metadata(request([
            function("f", "42", ("ignored",), payable=True), function("word", "x", ("x",))]))),
    ]


def write_cases(output):
    output.mkdir(parents=True, exist_ok=False)
    records = []
    for name, data in cases():
        filename = name + ".json"
        (output / filename).write_text(json.dumps(data, sort_keys=True, separators=(",", ":")) + "\n")
        record = {"case": name, "request": filename}
        selection = data["settings"]["outputSelection"].get("Function.sol")
        selected = next(iter(selection)) if selection is not None else None
        origin = corpus.matching_origin(data["sources"]["Function.sol"]["content"], selected)
        if origin is not None:
            record["corpusSource"] = origin
        records.append(record)
    (output / "manifest.json").write_text(json.dumps({"cases": records}, indent=2) + "\n")
    return [output / record["request"] for record in records]
