#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Validate exact production expression-graph artifacts with fresh kernel proofs.
This admits pure word graphs only; it does not certify emitted EVM bytecode.
"""
import copy
import json
import re
import sys

import check_compiler as gate
from common import decode_json
import compiler_artifacts as artifacts
from compiler_artifacts import package_inputs
from compiler_graph_cases import write_cases

ROOT = gate.ROOT
MAX_BYTES = 1024 * 1024
MAX_NODES = 256
MAX_EXPANSION = 4096
BINARY = set("add sub mul div mod and or xor shl shr lt gt eq".split())
UNARY = {"bitnot", "iszero"}
MODULE = "Compiler.Validation.Artifact"
BINARY_NAME = "compiler-graph-export"
NEGATIVE_FORBIDDEN_DIAGNOSTICS = ("maximum", "deep recursion", "timed out", "timeout",
    "unknown identifier", "unknown constant", "unexpected token")
REPORT_SCHEMA = "oksolc.compiler-graph-verification.v2"
AUDIT_SCHEMA = "oksolc.compiler-graph-audit.v2"
PROOF_SCOPE = "pureExpressionGraph"
EMITTED_EVM = False
REPORT_METADATA = {"requiresAllSourceResults": True, "requiresCapturedCache": True,
    "cacheEntryLimit": 1024, "wholeEvmRefinement": False}
EXTRA_INPUTS = ("docs/compiler-verification-map.json", "docs/compiler-verification-boundary.md")


def fields(value, expected):
    if not isinstance(value, dict) or set(value) != set(expected):
        raise ValueError("unexpected artifact fields; expected " + ", ".join(expected))


def index(value, bound):
    if type(value) is not int or not 0 <= value < bound:
        raise ValueError("invalid graph reference or root")
    return value


def node_size(node, expansion):
    if not isinstance(node, dict) or len(node) != 1:
        raise ValueError("expected a single node constructor")
    tag, value = next(iter(node.items()))
    if tag == "input":
        if not isinstance(value, str) or not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]{0,63}", value):
            raise ValueError("invalid input name")
        size = 1
    elif tag == "literal":
        if (not isinstance(value, str) or len(value) > 78 or
                not re.fullmatch(r"0|[1-9][0-9]*", value) or int(value) >= 2**256):
            raise ValueError("literal outside uint256")
        size = 1
    elif tag == "unary":
        fields(value, ("op", "arg"))
        if not isinstance(value["op"], str) or value["op"] not in UNARY:
            raise ValueError("unsupported unary operation")
        size = 1 + expansion[index(value["arg"], len(expansion))]
    elif tag == "binary":
        fields(value, ("op", "left", "right"))
        if not isinstance(value["op"], str) or value["op"] not in BINARY:
            raise ValueError("unsupported binary operation")
        size = 1 + expansion[index(value["left"], len(expansion))] + expansion[index(value["right"], len(expansion))]
    else:
        raise ValueError("unsupported node constructor")
    if size > MAX_EXPANSION:
        raise ValueError("symbolic expansion limit exceeded")
    return size


def graph_sizes(nodes, root):
    if not isinstance(nodes, list) or not 1 <= len(nodes) <= MAX_NODES:
        raise ValueError("unsupported graph size")
    index(root, len(nodes))
    expansion = []
    for node in nodes:
        expansion.append(node_size(node, expansion))
    return expansion


def graph(nodes, root):
    graph_sizes(nodes, root)
    return nodes


def admit_request(value):
    fields(value, ("schema", "nodes", "root"))
    if value["schema"] != "oksolc.compiler-graph-request.v1":
        raise ValueError("unsupported request schema")
    graph(value["nodes"], value["root"])
    return value


def request(data):
    return admit_request(decode_json(data.decode("utf-8")))


def admit_response(value, before):
    fields(value, ("schema", "requestSha256", "nodes", "root", "resultIds", "cache"))
    if value["schema"] != "oksolc.compiler-graph-response.v2":
        raise ValueError("unsupported response schema")
    if not isinstance(value["requestSha256"], str) or not re.fullmatch(r"[0-9a-f]{64}", value["requestSha256"]):
        raise ValueError("invalid request digest")
    expansion = graph_sizes(value["nodes"], value["root"])
    ids = value["resultIds"]
    if not isinstance(ids, list) or len(ids) != len(before["nodes"]):
        raise ValueError("missing source result IDs")
    for id in ids:
        index(id, len(expansion))
    if ids[before["root"]] != value["root"]:
        raise ValueError("selected root differs from its returned ID")
    admit_cache(value["cache"], expansion)
    return value


def admit_cache(cache, expansion):
    if not isinstance(cache, list) or len(cache) > 1024:
        raise ValueError("unsupported cache size")
    keys = set()
    for binding in cache:
        fields(binding, ("key", "id"))
        node_size(binding["key"], expansion)
        index(binding["id"], len(expansion))
        key = json.dumps(binding["key"], sort_keys=True, separators=(",", ":"))
        if key in keys:
            raise ValueError("duplicate cache key")
        keys.add(key)


def response(data, request_bytes):
    value = admit_response(decode_json(data.decode("utf-8")), request(request_bytes))
    if value["requestSha256"] != gate.digest(request_bytes):
        raise ValueError("stale or mismatched native response")
    return value


def lean_node(node):
    tag, value = next(iter(node.items()))
    if tag == "input":
        return ".input " + json.dumps(value)
    if tag == "literal":
        return ".literal " + value
    if tag == "unary":
        return f".unary .{value['op']} {value['arg']}"
    return f".binary .{value['op']} {value['left']} {value['right']}"


def proof_source(pairs, fuel):
    if not 1 <= len(pairs) <= 128 or type(fuel) is not int or not 0 <= fuel <= 16:
        raise ValueError("unsupported proof batch or fuel")
    lines = ["/-", "// SPDX-License-Identifier: GPL-3.0",
        "// Copyright (C) 2026 OKcontract Pte. Ltd.", "-/",
        "import Compiler.Validation.GraphInventory", "import Contract.Check.Declarations", "import Lean.Elab.Command",
        "namespace " + MODULE, "open Contract.Yul", ""]
    claims = []
    for number, (before, after) in enumerate(pairs):
        admit_request(before)
        admit_response(after, before)
        for name, value in (("before", before), ("after", after)):
            lines.append(f"def {name}_{number} : List Node := [" +
                         ", ".join(lean_node(n) for n in value["nodes"]) + "]")
        lines.append(f"def ids_{number} : List Nat := " + str(after["resultIds"]))
        lines.append(f"def cache_{number} : List Inventory.Entry := [" + ", ".join(
            "⟨(" + lean_node(binding["key"]) + "), " + str(binding["id"]) + "⟩" for binding in after["cache"]) + "]")
        br, ar = before["root"], after["root"]
        name = f"checked_{number}"
        claims.append(MODULE + "." + name)
        lines += [f"theorem {name} (locals : String → Word) :",
            f"    Inventory.Preserves before_{number} after_{number} ids_{number} cache_{number} locals ∧",
            f"    ∃ value, evaluate before_{number} {br} locals = some value ∧",
            f"      evaluate after_{number} {ar} locals = some value :=",
            f"  Inventory.certify {fuel} before_{number} after_{number} ids_{number} cache_{number} {br} {ar} (by decide) (by decide) locals", ""]
    lines += artifacts.audit_source(MODULE, claims, AUDIT_SCHEMA)
    return "\n".join(lines).encode(), claims


def case_metadata(req, res):
    return {"beforeRoot": req["root"], "afterRoot": res["root"],
            "beforeNodes": len(req["nodes"]), "afterNodes": len(res["nodes"]),
            "resultIds": len(res["resultIds"]), "cacheEntries": len(res["cache"])}


def negative_pairs(pairs):
    from compiler_graph_cases import cases
    fixtures = dict(cases())
    alias = next(pair for pair in pairs if pair[0] == fixtures["inventory_alias"])
    unused = next(pair for pair in pairs if pair[0] == fixtures["inventory_unused"])
    result = []

    def retain(label, req, res):
        admit_response(res, req)
        result.append((label, [(req, res)]))

    # These six controls preserve the selected root. Kernel failure must come
    # from the stronger inventory relation, not malformed data.
    req, res = copy.deepcopy(alias)
    res["resultIds"][1] = res["resultIds"][0]
    retain("unused_result", req, res)
    req, res = copy.deepcopy(unused)
    res["nodes"][res["resultIds"][1]] = {"literal": "0"}
    retain("unused_representative", req, res)
    for label in ("cache_value", "cache_operand", "cache_operator"):
        req, res = copy.deepcopy(alias)
        binding = next(b for b in res["cache"] if b["key"].get("binary", {}).get("op") == "add")
        if label == "cache_value":
            binding["id"] = res["resultIds"][1]
        elif label == "cache_operand":
            binding["key"]["binary"]["right"] = binding["key"]["binary"]["left"]
        else:
            binding["key"]["binary"]["op"] = "mul"
        retain(label, req, res)
    req, res = copy.deepcopy(alias)
    res["cache"].append({"key": {"literal": "1"}, "id": res["resultIds"][0]})
    retain("unused_cache_poison", req, res)
    recursive = next(pair for pair in pairs if pair[0] == fixtures["associate_add_fold"])
    req, res = copy.deepcopy(recursive)
    folded = next(node for node in res["nodes"] if node == {"literal": "8"})
    folded["literal"] = "9"
    retain("associate_wrong_constant", req, res)
    req, res = copy.deepcopy(recursive)
    binding = next(b for b in res["cache"] if b["key"] == req["nodes"][4])
    binding["key"]["binary"]["op"] = "mul"
    retain("associate_wrong_cache_operator", req, res)
    return result


if __name__ == "__main__":
    sys.exit(artifacts.main(sys.modules[__name__]))
