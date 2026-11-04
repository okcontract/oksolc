#!/usr/bin/env python3
"""Inventory constructor call sites; this is not source admission or a proof.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import hashlib
import json
from pathlib import Path

from extract_compiler import Unsupported
from extract_storage import LEXER, lex

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "docs/compiler-verification-rc-calls.json"
SOURCES = {
    "src/libevmasm/algebraic_rules.zig": None,
    "src/libevmasm/rule_list.zig": None,
    "src/libevmasm/expression_classes.zig": {"makeOperation", "makeConstant", "materializeConstant", "findDefault"},
}
METHODS = {"makeOperation": 3, "makeConstant": 2, "materializeConstant": 3, "findDefault": 2, "find": 4}
PAIRS = {"(": ")", "[": "]", "{": "}"}


def end(items, start):
    stack = []
    for position in range(start, len(items)):
        token = items[position]
        if token in PAIRS:
            stack.append(PAIRS[token])
        elif token in PAIRS.values():
            if not stack or stack.pop() != token:
                raise Unsupported("unbalanced constructor inventory span")
            if not stack:
                return position
    raise Unsupported("unterminated constructor inventory span")


def arguments(items):
    result, start, position = [], 0, 0
    while position < len(items):
        if items[position] in PAIRS:
            position = end(items, position)
        elif items[position] == ",":
            result.append(items[start:position])
            start = position + 1
        position += 1
    if start < len(items):
        result.append(items[start:])
    if any(not argument for argument in result):
        raise Unsupported("empty constructor inventory argument")
    return result


def sites(data, selected=None):
    text = data.decode("utf-8")
    # Reuse the reviewed extractor lexer, including its complete-token check.
    items = lex(text)
    positions = [match for match in LEXER.finditer(text)
                 if not match.group().isspace() and not match.group().startswith("//")]
    byte_offsets = [0]
    for character in text:
        byte_offsets.append(byte_offsets[-1] + len(character.encode("utf-8")))
    result, seen, position = [], set(), 0
    while position < len(items):
        if items[position] == "test":
            break  # Everything after this boundary is outside production scope.
        if items[position] != "fn":
            position += 1
            continue
        owner = items[position + 1]
        seen.add(owner)
        start = end(items, position + 2) + 1
        while start < len(items) and items[start] != "{":
            start += 1
        stop = end(items, start)
        if selected is None or owner in selected:
            for index in range(start + 1, stop):
                if items[index:index + 2] not in (["classes", "."], ["self", "."]):
                    continue
                method = items[index + 2]
                if method not in METHODS:
                    continue
                if items[index + 3] != "(":
                    raise Unsupported("constructor callback used without a direct call")
                finish = end(items, index + 3)
                args = arguments(items[index + 4:finish])
                if len(args) != METHODS[method]:
                    raise Unsupported("constructor inventory arity changed")
                storage, arity = "empty", 0
                if method in {"makeOperation", "findDefault", "find"}:
                    operand = args[1]
                    if operand[:3] == ["&", ".", "{"] and operand[-1] == "}":
                        arity = len(arguments(operand[3:-1]))
                        storage = "temporary" if arity else "empty"
                    elif operand == ["&", "operands"] and owner == "dropRepeatedNested":
                        storage, arity = "local-array", 2
                    elif operand in (["inner"], ["byte_args"], ["shifted"]):
                        storage, arity = "borrowed", None
                    elif operand == ["arguments"] and selected is not None:
                        storage, arity = "forwarded", None
                    else:
                        raise Unsupported("unclassified constructor argument storage in " + owner)
                begin_byte = byte_offsets[positions[index].start()]
                end_byte = byte_offsets[positions[finish].end()]
                result.append({"owner": owner, "callee": method,
                    "startByte": begin_byte, "endByte": end_byte,
                    "line": text.count("\n", 0, positions[index].start()) + 1,
                    "sha256": hashlib.sha256(data[begin_byte:end_byte]).hexdigest(),
                    "storage": storage, "arity": arity})
        position = stop + 1
    if selected is not None and not selected <= seen:
        raise Unsupported("constructor inventory root disappeared")
    for site in result:
        site["children"] = [index for index, child in enumerate(result)
                            if site["startByte"] < child["startByte"] < site["endByte"]]
    return result


def inventory(read=None):
    read = read or (lambda name: (ROOT / name).read_bytes())
    sources = []
    for name, selected in SOURCES.items():
        data = read(name)
        sources.append({"path": name, "sha256": hashlib.sha256(data).hexdigest(), "sites": sites(data, selected)})
    return {"schema": "oksolc.recursive-constructor-call-inventory.v1", "boundaryVersion": 2,
            "scope": "constructor wrappers and every constructor call in the extracted dispatcher/helper bodies; excludes test bodies and other graph entry points",
            "semanticAcceptance": False, "sources": sources}


def check():
    actual = inventory()
    if json.loads(OUTPUT.read_bytes()) != actual:
        raise ValueError("recursive constructor call inventory is stale; review every changed call site")
    return {"callSites": sum(len(source["sites"]) for source in actual["sources"]),
            "inventorySha256": hashlib.sha256(OUTPUT.read_bytes()).hexdigest(),
            "constructorGoalEstablished": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="refresh inventory after source review")
    args = parser.parse_args()
    if args.write:
        OUTPUT.write_text(json.dumps(inventory(), indent=2) + "\n")
    else:
        print(json.dumps(check(), sort_keys=True))


if __name__ == "__main__":
    main()
