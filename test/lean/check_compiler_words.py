#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Certify exact native EVM blocks against resolved unchecked Solidity uint256
expressions, preserving the named input stack under an explicit gas model.
"""
import copy
import json
import re
import sys

import compiler_artifacts as artifacts
import check_compiler_graphs as graphs
from common import decode_json

MODULE = "Compiler.Validation.WordArtifact"
BINARY_NAME = "compiler-word-export"
REPORT_SCHEMA = "oksolc.compiler-word-verification.v1"
AUDIT_SCHEMA = "oksolc.compiler-word-audit.v1"
PROOF_SCOPE = "emittedEvm"
EMITTED_EVM = True
REPORT_METADATA = {"sourceScope": "resolvedUncheckedUint256", "fork": "cancun",
    "gasModel": "constantOpcodeCostWithSufficientEntryGas", "wholeEvmRefinement": False,
    "sourceParserVerified": False, "observation": "resultAndEntireNamedInputStack"}
SOURCE_BINARY = {"add", "sub", "mul", "and", "or", "xor", "shl", "shr"}
MAX_CODE_BYTES = 4096


def admit_request(value):
    graphs.fields(value, ("schema", "arithmetic", "evmVersion", "parameters", "nodes", "root"))
    if value["schema"] != "oksolc.compiler-word-request.v1":
        raise ValueError("unsupported source-word schema")
    if value["arithmetic"] != "unchecked" or value["evmVersion"] != "cancun":
        raise ValueError("only unchecked uint256 and Cancun are admitted")
    graphs.graph(value["nodes"], value["root"])
    parameters = value["parameters"]
    if (not isinstance(parameters, list) or len(parameters) > 16 or
            any(not isinstance(p, str) or not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]{0,63}", p) for p in parameters)):
        raise ValueError("invalid stack parameter interface")
    if len(set(parameters)) != len(parameters):
        raise ValueError("duplicate stack parameter")
    for node in value["nodes"]:
        if "input" in node and node["input"] not in parameters:
            raise ValueError("source input has no stack parameter")
        if "unary" in node and node["unary"]["op"] != "bitnot":
            raise ValueError("unsupported Solidity unary operation")
        if "binary" in node and node["binary"]["op"] not in SOURCE_BINARY:
            raise ValueError("unsupported Solidity binary operation")
    return value


def request(data):
    return admit_request(decode_json(data.decode("utf-8")))


def bytecode(value):
    if (not isinstance(value, str) or not 2 <= len(value) <= 2 * MAX_CODE_BYTES or
            len(value) % 2 or not re.fullmatch(r"[0-9a-f]+", value)):
        raise ValueError("invalid or oversized canonical bytecode")
    return bytes.fromhex(value)


def admit_response(value):
    graphs.fields(value, ("schema", "requestSha256", "bytecode"))
    if value["schema"] != "oksolc.compiler-word-response.v1":
        raise ValueError("unsupported word-bytecode response schema")
    if not isinstance(value["requestSha256"], str) or not re.fullmatch(r"[0-9a-f]{64}", value["requestSha256"]):
        raise ValueError("invalid request digest")
    bytecode(value["bytecode"])
    return value


def response(data, request_bytes):
    value = admit_response(decode_json(data.decode("utf-8")))
    if value["requestSha256"] != artifacts.gate.digest(request_bytes):
        raise ValueError("stale or mismatched word-bytecode response")
    return value


def source_expression(nodes, root):
    node = nodes[root]
    if "input" in node:
        return "(.input " + json.dumps(node["input"]) + ")"
    if "literal" in node:
        return "(.literal " + node["literal"] + ")"
    if "unary" in node:
        return "(.bitnot " + source_expression(nodes, node["unary"]["arg"]) + ")"
    op = node["binary"]
    name = {"and": "bitand", "or": "bitor", "xor": "bitxor"}.get(op["op"], op["op"])
    return f"(.binary .{name} {source_expression(nodes, op['left'])} {source_expression(nodes, op['right'])})"


def proof_source(pairs, fuel):
    if not 1 <= len(pairs) <= 128 or type(fuel) is not int or not 0 <= fuel <= 16:
        raise ValueError("unsupported proof batch or fuel")
    lines = ["/-", "// SPDX-License-Identifier: GPL-3.0",
        "// Copyright (C) 2026 OKcontract Pte. Ltd.", "-/",
        "import Compiler.Validation.SolidityWord", "import Contract.Check.Declarations", "import Lean.Elab.Command",
        "namespace " + MODULE, "open Contract.Yul", ""]
    claims = []
    for i, (req, res) in enumerate(pairs):
        admit_request(req)
        admit_response(res)
        code = bytecode(res["bytecode"])
        lines += [f"def source_{i} : SolidityWord.Expr := " + source_expression(req["nodes"], req["root"]),
            f"def bytes_{i} : List UInt8 := [" + ", ".join(str(b) for b in code) + "]",
            f"def parameters_{i} : List String := [" + ", ".join(json.dumps(p) for p in req["parameters"]) + "]",
            f"theorem checked_{i} (locals : String → Word) :",
            f"    ∃ cost, WordBlock.execute bytes_{i} (parameters_{i}.map locals) =",
            f"        some (cost, source_{i}.eval locals :: parameters_{i}.map locals) ∧",
            f"      ∀ gas, cost ≤ gas → WordBlock.metered bytes_{i} (parameters_{i}.map locals) gas =",
            f"        some (gas - cost, source_{i}.eval locals :: parameters_{i}.map locals) :=",
            f"  SolidityWord.metered_bytecode_sound {fuel} bytes_{i} parameters_{i} source_{i} (by decide) locals", ""]
        claims.append(MODULE + f".checked_{i}")
    lines += artifacts.audit_source(MODULE, claims, AUDIT_SCHEMA)
    return "\n".join(lines).encode(), claims


def case_metadata(req, res):
    code = bytecode(res["bytecode"])
    return {"sourceNodes": len(req["nodes"]), "sourceRoot": req["root"], "parameters": req["parameters"],
            "bytecodeBytes": len(code), "bytecodeSha256": artifacts.gate.digest(code)}


def write_cases(output):
    from compiler_word_cases import write_cases as write
    return write(output)


def negative_pairs(pairs):
    # These controls start with actual production responses. Keep exact request
    # binding while corrupting bytes; host admission must still accept the data.
    identity = next(pair for pair in pairs if pair[0]["nodes"] == [{"input": "x"}])
    zero = next(pair for pair in pairs if pair[0]["nodes"] ==
        [{"input": "x"}, {"binary": {"op": "sub", "left": 0, "right": 0}}])
    result = []
    for name, pair, changed in (("wrong_value", identity, "5f"),
                                ("truncated_push", identity, "60"),
                                ("lost_input_frame", zero, "8018")):
        req, res = copy.deepcopy(pair)
        res["bytecode"] = changed
        result.append((name, [(req, res)]))
    return result


if __name__ == "__main__":
    sys.exit(artifacts.main(sys.modules[__name__]))
