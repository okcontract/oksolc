#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Generate requests exercising every exported production rule and graph boundaries.
The kernel validator is the oracle; this generator supplies no expected outputs.
"""
import argparse
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]


def binary(op, left, right):
    return {"binary": {"op": op, "left": left, "right": right}}


def request(nodes, root=None):
    return {"schema": "oksolc.compiler-graph-request.v1", "nodes": nodes,
            "root": len(nodes) - 1 if root is None else root}


def cases():
    exported = (ROOT / "lean/Compiler/Algebraic/Rules.lean").read_text()
    rules = re.findall(r"⟨\.([a-z]+), \.([a-z_]+), \.([a-z_]+)⟩", exported)
    if not rules or len(rules) != exported.count("⟨"):
        raise ValueError("cannot enumerate every production table entry")
    result = []
    constants = {"zero": 0, "one": 1, "max": 2**256 - 1}
    for i, (op, guard, _) in enumerate(rules):
        if guard == "equal":
            nodes = [{"input": "x"}, binary(op, 0, 0)]
        else:
            side, kind = guard.split("_")
            if side not in ("left", "right") or kind not in constants:
                raise ValueError("unsupported rule guard in corpus")
            nodes = [{"input": "x"}, {"input": "y"}]
            nodes[0 if side == "left" else 1] = {"literal": str(constants[kind])}
            nodes.append(binary(op, 0, 1))
        result.append((f"rule_{i:02}_{op}_{guard}", request(nodes)))
    for op in "add sub mul div mod and or xor shl shr lt gt eq".split():
        result.append(("constant_" + op, request([
            {"literal": str(2**256 - 1)}, {"literal": "2"}, binary(op, 0, 1)])))
    for op in "add mul and or xor eq".split():
        result.append(("commute_" + op, request([
            {"input": "a"}, {"input": "b"}, binary(op, 1, 0)])))
    for op in "add mul and or xor".split():
        result += [
            ("associate_" + op + "_fold", request([{"input": "x"}, {"literal": "3"},
                binary(op, 0, 1), {"literal": "5"}, binary(op, 2, 3)])),
            ("associate_" + op + "_left", request([{"input": "x"}, {"literal": "3"},
                binary(op, 0, 1), {"input": "y"}, binary(op, 2, 3)])),
            ("associate_" + op + "_right", request([{"input": "y"}, {"input": "x"},
                {"literal": "3"}, binary(op, 1, 2), binary(op, 0, 3)])),
            ("associate_" + op + "_both", request([{"input": "x"}, {"literal": "3"},
                binary(op, 0, 1), {"input": "y"}, {"literal": "5"},
                binary(op, 3, 4), binary(op, 2, 5)])),
        ]
    result += [
        ("nested", request([{"input": "x"}, {"literal": "0"}, binary("add", 0, 1),
                            {"literal": "1"}, binary("mul", 2, 3)])),
        ("double_not", request([{"input": "x"}, {"unary": {"op": "bitnot", "arg": 0}},
                                {"unary": {"op": "bitnot", "arg": 1}}])),
        ("div_zero", request([{"literal": "7"}, {"literal": "0"}, binary("div", 0, 1)])),
        ("mod_zero", request([{"literal": "7"}, {"literal": "0"}, binary("mod", 0, 1)])),
        ("wrap", request([{"literal": str(2**256 - 1)}, {"literal": "1"}, binary("add", 0, 1)])),
        ("duplicate_input", request([{"input": "x"}, {"input": "x"}, binary("sub", 0, 1)])),
        ("inventory_alias", request([{"input": "x"}, {"literal": "0"}, binary("add", 0, 1)], 0)),
        ("inventory_unused", request([{"input": "x"}, {"input": "y"}], 0)),
        ("inventory_cache_hit", request([{"input": "x"}, {"input": "y"},
            binary("add", 0, 1), binary("add", 1, 0)])),
    ]
    return result


def write_cases(output):
    output.mkdir(parents=True, exist_ok=False)
    records = []
    for name, data in cases():
        filename = name + ".json"
        (output / filename).write_text(json.dumps(data, sort_keys=True, separators=(",", ":")) + "\n")
        records.append({"case": name, "request": filename})
    (output / "manifest.json").write_text(json.dumps({"cases": records}, indent=2) + "\n")
    return [output / record["request"] for record in records]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    records = write_cases(args.output)
    print(json.dumps({"requests": len(records), "output": str(args.output)}))


if __name__ == "__main__":
    main()
