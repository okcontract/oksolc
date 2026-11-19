#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Source-word and exact-byte corpus; Lean supplies the preservation oracle.
"""
import json

from compiler_graph_cases import binary, cases as graph_cases


def request(nodes, root=None, parameters=None):
    if parameters is None:
        parameters = list(dict.fromkeys(n["input"] for n in nodes if "input" in n)) + ["frame"]
    return {"schema": "oksolc.compiler-word-request.v1", "arithmetic": "unchecked", "evmVersion": "cancun",
        "parameters": parameters, "nodes": nodes, "root": len(nodes) - 1 if root is None else root}


def cases():
    result = [("identity", request([{"input": "x"}])),
              ("equal_sub", request([{"input": "x"}, binary("sub", 0, 0)]))]
    for name, graph in graph_cases():
        nodes = graph["nodes"]
        if any("binary" in n and n["binary"]["op"] not in {"add", "sub", "mul", "and", "or", "xor", "shl", "shr"}
               for n in nodes):
            continue
        # Convert Yul-order fixture shifts to the corresponding Solidity syntax.
        nodes = json.loads(json.dumps(nodes))
        for n in nodes:
            if "binary" in n and n["binary"]["op"] in ("shl", "shr"):
                op = n["binary"]
                op["left"], op["right"] = op["right"], op["left"]
        result.append((name, request(nodes, graph["root"])))
    for op in ("add", "sub", "mul", "and", "or", "xor", "shl", "shr"):
        result.append(("variable_" + op, request([{"input": "x"}, {"input": "y"}, binary(op, 0, 1)])))
    for width in range(1, 33):
        result.append((f"push_{width}", request([{"literal": str(1 << (8 * (width - 1)))}], parameters=[])))
    result += [("push_zero", request([{"literal": "0"}], parameters=[])),
               ("dup16", request([{"input": "x"}], parameters=[f"unused_{i}" for i in range(15)] + ["x"]))]
    for op in ("shl", "shr"):
        for amount in (255, 256, 2**256 - 1):
            result.append((f"{op}_boundary_{amount}", request([
                {"input": "x"}, {"literal": str(amount)}, binary(op, 0, 1)])))
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
