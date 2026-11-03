#!/usr/bin/env python3
"""
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

Certify actual recursive optimizer graphs after every observed allocation cut.
OOM preserves a prefix and reached cache, never a successful compilation claim.
"""
import copy
import json
import re
import sys

import check_compiler_graphs as graph
import compiler_artifacts as artifacts
from common import decode_json

ROOT = graph.ROOT
gate = graph.gate
BINARY_NAME = graph.BINARY_NAME
EXTRA_INPUTS = graph.EXTRA_INPUTS
MODULE = "Compiler.Validation.Artifact"
REPORT_SCHEMA = "oksolc.compiler-graph-failure-verification.v1"
AUDIT_SCHEMA = "oksolc.compiler-graph-failure-audit.v1"
PROOF_SCOPE = "pureExpressionGraphFailurePrefix"
EMITTED_EVM = False
REPORT_METADATA = {"requiresEveryAllocationCut": True, "requiresCapturedCache": True,
    "resizePolicy": "always-fail", "nativeMemorySafetyProved": False,
    "failedCompilationIsSuccess": False, "wholeEvmRefinement": False}
NEGATIVE_FORBIDDEN_DIAGNOSTICS = graph.NEGATIVE_FORBIDDEN_DIAGNOSTICS
MAX_ALLOCATIONS = 128


def admit_request(value):
    graph.fields(value, ("schema", "nodes", "root"))
    if value["schema"] != "oksolc.compiler-graph-failure-request.v1":
        raise ValueError("unsupported failure request schema")
    graph.graph(value["nodes"], value["root"])
    return value


def request(data):
    return admit_request(decode_json(data.decode("utf-8")))


def admit_attempt(value, before):
    graph.fields(value, ("outcome", "nodes", "resultIds", "cache"))
    if value["outcome"] not in ("complete", "outOfMemory"):
        raise ValueError("unsupported compiler outcome")
    nodes, ids, cache = value["nodes"], value["resultIds"], value["cache"]
    if not isinstance(nodes, list) or len(nodes) > graph.MAX_NODES:
        raise ValueError("unsupported reached graph size")
    expansion = []
    for node in nodes:
        expansion.append(graph.node_size(node, expansion))
    if not isinstance(ids, list) or len(ids) > len(before["nodes"]):
        raise ValueError("invalid returned prefix")
    for id in ids:
        graph.index(id, len(nodes))
    # Progress and word equivalence are kernel-checked, including whether an
    # allegedly complete attempt really returned every source result.
    graph.admit_cache(cache, expansion)


def admit_response(value, before):
    graph.fields(value, ("schema", "requestSha256", "resizePolicy", "observations"))
    if value["schema"] != "oksolc.compiler-graph-failure-response.v1":
        raise ValueError("unsupported failure response schema")
    if not isinstance(value["requestSha256"], str) or not re.fullmatch(r"[0-9a-f]{64}", value["requestSha256"]):
        raise ValueError("invalid request digest")
    if value["resizePolicy"] != "always-fail":
        raise ValueError("unsupported resize schedule")
    observations = value["observations"]
    if not isinstance(observations, list) or not 2 <= len(observations) <= MAX_ALLOCATIONS + 1:
        raise ValueError("missing or oversized allocation sweep")
    count = len(observations) - 1
    for index, observation in enumerate(observations):
        graph.fields(observation, ("failureAt", "successfulAllocations", "inducedFailure", "attempt"))
        admit_attempt(observation["attempt"], before)
        cut, allocations, failed = (observation[key] for key in ("failureAt", "successfulAllocations", "inducedFailure"))
        if type(allocations) is not int or allocations != index:
            raise ValueError("incomplete or reordered allocation sweep")
        if index == count:
            if cut is not None or failed is not False or observation["attempt"]["outcome"] != "complete":
                raise ValueError("missing successful baseline")
        elif type(cut) is not int or cut != index or failed is not True or observation["attempt"]["outcome"] != "outOfMemory":
            raise ValueError("missing induced allocation failure")
    return value


def response(data, request_bytes):
    value = admit_response(decode_json(data.decode("utf-8")), request(request_bytes))
    if value["requestSha256"] != gate.digest(request_bytes):
        raise ValueError("stale or mismatched native response")
    return value


def lean_attempt(attempt):
    nodes = "[" + ", ".join(graph.lean_node(n) for n in attempt["nodes"]) + "]"
    cache = "[" + ", ".join("⟨(" + graph.lean_node(b["key"]) + "), " + str(b["id"]) + "⟩"
        for b in attempt["cache"]) + "]"
    return "⟨." + attempt["outcome"] + ", " + nodes + ", " + str(attempt["resultIds"]) + ", " + cache + "⟩"


def proof_source(pairs, fuel, offset=0):
    if not 1 <= len(pairs) <= 128 or type(fuel) is not int or not 0 <= fuel <= 16:
        raise ValueError("unsupported proof batch or fuel")
    lines = ["/-", "// Copyright (C) 2026 OKcontract Pte. Ltd.", "// SPDX-License-Identifier: GPL-3.0", "-/",
        "import Compiler.Validation.GraphFailure", "import Contract.Check.Declarations", "import Lean.Elab.Command",
        "namespace " + MODULE, "open Contract.Yul", ""]
    claims = []
    for number, (before, after) in enumerate(pairs, offset):
        admit_request(before)
        admit_response(after, before)
        lines.append(f"def before_{number} : List Node := [" + ", ".join(graph.lean_node(n) for n in before["nodes"]) + "]")
        lines.append(f"def attempts_{number} : List Failure.Attempt := [" + ", ".join(
            lean_attempt(o["attempt"]) for o in after["observations"]) + "]")
        name = f"checked_{number}"
        claims.append(MODULE + "." + name)
        lines += [f"theorem {name} (locals : String → Word) :",
            f"    attempts_{number} ≠ [] ∧ ∀ attempt ∈ attempts_{number}, Failure.Preserves before_{number} attempt locals :=",
            f"  Failure.certify {fuel} before_{number} attempts_{number} (by decide) locals", ""]
    lines += artifacts.audit_source(MODULE, claims, AUDIT_SCHEMA)
    return "\n".join(lines).encode(), claims


def proof_batches(pairs, fuel):
    return [proof_source([pair], fuel, index) for index, pair in enumerate(pairs)]


def case_metadata(req, res):
    observations = res["observations"]
    return {"inputNodes": len(req["nodes"]), "allocationCuts": len(observations) - 1,
        "completeAttempts": 1, "outOfMemoryAttempts": len(observations) - 1,
        "failedAttemptsWithMoreRepresentativesThanResults": sum(len(o["attempt"]["nodes"]) > len(o["attempt"]["resultIds"])
            for o in observations[:-1])}


def write_cases(output):
    from compiler_graph_cases import cases
    selected = ["associate_" + op + "_fold" for op in ("add", "mul", "and", "or", "xor")]
    selected += ["inventory_alias", "inventory_cache_hit"]
    fixtures = dict(cases())
    output.mkdir(parents=True, exist_ok=False)
    paths = []
    for name in selected:
        value = copy.deepcopy(fixtures[name])
        value["schema"] = "oksolc.compiler-graph-failure-request.v1"
        path = output / (name + ".json")
        path.write_text(json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n")
        paths.append(path)
    return paths


def negative_pairs(pairs):
    # Use a reached recursive constant, with earlier returned results present.
    pair = next(pair for pair in pairs if pair[0]["nodes"][-1].get("binary", {}).get("op") == "add"
        and len(pair[0]["nodes"]) == 5)
    index = next(index for index, o in enumerate(pair[1]["observations"][:-1])
        if o["attempt"]["resultIds"] == [0, 1, 2, 3] and {"literal": "8"} in o["attempt"]["nodes"])
    negatives = []
    for label in ("old_result", "partial_cache", "missing_prefix_result", "incomplete_baseline"):
        req, res = copy.deepcopy(pair)
        attempt = res["observations"][index]["attempt"]
        if label == "old_result":
            attempt["resultIds"][1] = 0
        elif label == "partial_cache":
            binding = next(b for b in attempt["cache"] if b["key"] == {"literal": "8"})
            binding["key"] = {"literal": "9"}
        elif label == "missing_prefix_result":
            attempt["resultIds"].pop(1)
        else:
            res["observations"][-1]["attempt"]["resultIds"].pop()
        admit_response(res, req)
        negatives.append((label, [(req, res)]))
    return negatives


if __name__ == "__main__":
    sys.exit(artifacts.main(sys.modules[__name__]))
