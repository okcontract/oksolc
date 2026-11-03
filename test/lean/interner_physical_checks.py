#!/usr/bin/env python3
"""Word and memory preservation for the same complete interner execution.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import json
import re

from check_argument_memory import ROOT, NS
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

MODULE = "Compiler.Extraction.InternerPhysicalTests"
SEMANTIC = NS + "Normalization.OwnedCall.Semantic."
FILES = ["InternerPhysical" + suffix + ".lean" for suffix in (
    "Meaning", "Owned", "Caller", "Production", "Fixtures", "Tests")]
CLAIMS = [SEMANTIC + name for name in (
    "Ensures.error", "Ensures.pure", "Ensures.extend", "insert_safe", "publish_safe", "publish_return_safe",
    "miss_safe", "owned_safe", "force_owned_safe", "find_body_safe", "force_body_safe", "invoke_safe",
    "Verified.closed", "find_verified", "force_verified", "production_verified")]
CLAIMS += [SEMANTIC + "Tests." + name for name in (
    "nested_graph", "ownership", "release_graph", "semantics", "graph_valid", "source_represented",
    "request_value", "force_value", "found_observation", "forced_observation", "miss_observation",
    "unequal_representative", "production_contract", "production_success", "production_force", "production_failure")]


def audit(output):
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    owned = NS + "Normalization.OwnedCall."
    normalization = NS + "Normalization."
    required = {
        SEMANTIC + "production_verified": {SEMANTIC + n for n in (
            "Verified", "Ensures", "Contracts", "GraphContracts", "invoke_safe", "find_body_safe", "force_body_safe")}
            | {owned + "Caller." + n for n in ("Verified", "invoke_verified", "initialize_verified", "initialize_graph")}
            | {normalization + n for n in ("caller_buffer", "normalized_projection", "take_refines", "deinit_refines")}
            | {"Compiler.Extraction.InsertionSort.normalize_word", "Compiler.Extraction.Interner.makeKey_sound",
               "Compiler.Extraction.Cache.key_stable"},
        SEMANTIC + "Tests.production_success": {SEMANTIC + n for n in (
            "production_verified", "Tests.ownership", "Tests.semantics", "Tests.found_observation")}
            | {owned + "nested_held"},
        SEMANTIC + "Tests.production_force": {SEMANTIC + n for n in (
            "production_verified", "Tests.force_value", "Tests.forced_observation")},
        SEMANTIC + "Tests.production_failure": {SEMANTIC + n for n in (
            "production_verified", "Tests.semantics", "Tests.miss_observation")},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError("physical caller word composition lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return {"checkedDependencies": sorted(required), "obligation": "normalization.recursiveBridge",
            "samePhysicalCallerWordPreservationVerified": True, "recursiveMemoryBridgeVerified": False,
            "pendingObligations": ["native graph callback ownership and semantic contracts", "native query/graph observation refinement",
                                   "physical recursive simplifier induction", "completed native recursive execution binding"]}


def controls(output, env, lean):
    imports = "import Compiler.Extraction.InternerCallerTests\n"
    parts = {name: without_imports((ROOT / "lean/Compiler/Extraction" / name).read_text()) for name in FILES}
    source = "\n".join(parts.values())
    records = [mutation_check(output, "interner-physical-unchanged", imports + source, True, env, lean)]
    for name, file, before, after in (
        ("insert-without-value", "Meaning", "(fun id after => after.read id = some value)\n  publish", "(fun _ _ => True)\n  publish"),
        ("simplify-without-value", "Meaning", "(fun found after => ∀ id, found = some id → after.read id = some value)", "(fun found _ => ∀ id, found = some id → True)"),
        ("drop-stability", "Meaning", "Interner.Stable before after ∧", "Interner.Stable before before ∧"),
        ("wrong-find-word", "Caller", "(fun id after => after.read id = some value)", "(fun id after => after.read id = some (value + 1))"),
        ("unequal-force-premise", "Caller", "(actual : before.graph.read id = some value)", "(actual : before.graph.read id = some (value + 1))"),
        ("inverted-value-check", "Fixtures", "if before.graph.read known = key.eval meaning before.graph.read", "if before.graph.read known ≠ key.eval meaning before.graph.read"),
        ("wrong-returned-id", "Fixtures", "then some known else none", "then some (known + 1) else none"),
        ("lost-nested-effects", "Fixtures", "then some known else none), after)", "then some known else none), before)"),
    ):
        model = parts["InternerPhysical" + file + ".lean"]
        if model.count(before) != 1:
            raise ValueError("ambiguous physical caller mutation: " + name)
        records.append(mutation_check(output, "interner-physical-" + name,
            imports + source.replace(model, model.replace(before, after), 1), False, env, lean))
    for record in records:
        diagnostic = (output / (record["name"] + ".stdout")).read_text()
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant", diagnostic, re.I):
            raise ValueError("physical caller control hit a resource or syntax failure: " + record["name"])
        if not record["expectedAcceptance"] and not re.search(
                r"error: (?:unsolved goals|Application type mismatch|Type mismatch|Tactic[^\n]*failed)", diagnostic):
            raise ValueError("physical caller control lacks a semantic proof failure: " + record["name"])
    return records
