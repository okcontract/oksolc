#!/usr/bin/env python3
"""Preparation ordering in the recursive resource model, not physical refinement.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import json
import re
from pathlib import Path

from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

ROOT = Path(__file__).resolve().parents[2]
SCOPE = "Compiler.Extraction.Interner.Scoped."
CLAIMS = [SCOPE + name for name in ("initialize_effects", "initialize_oom_effects")]
CLAIMS += [SCOPE + "PreparationTests." + name for name in (
    "scratch_prepares_before_duplicate", "allocated_prepares_after_allocation", "failed_allocation_skips_preparation",
    "borrowed_input_skips_preparation", "singleton_skips_preparation", "cleanup_observes_preparation",
    "recursive_take_fails_at_reached_cursor", "recursive_failure_closes_scope", "lookup_hit_releases_after_preparation")]


def audit(output):
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "closure-audit.json").read_bytes())["claims"]}
    for name in ("Compiler.Extraction.InsertionSort.detailed_verified", SCOPE + "initialize_effects",
                 SCOPE + "PreparationTests.recursive_take_fails_at_reached_cursor"):
        needed = {SCOPE + "Resources.prepare", SCOPE + "initScope"}
        if not needed <= claims[name]:
            raise ValueError("recursive proof lost preparation effects: " + name)
    return {"obligation": "normalization.recursiveBridge", "preparationResourceEffectsVerified": True,
            "normalizationMemoryResourceBridgeVerified": False,
            "boundary": "Successful preparation cursor projection only; actual memory executions and semantic faults still need the checked resource adapter."}


def controls(output, env, lean):
    directory = ROOT / "lean/Compiler/Extraction"
    imports = "import Compiler.Extraction.InternerProgram\nimport Compiler.Extraction.NormalizationEffects\nimport Compiler.Extraction.InsertionEffectTests\n"
    imports += "import Compiler.Extraction.InternerControl\n"
    model = without_imports((directory / "InternerScope.lean").read_text())
    clients = "\n".join(without_imports((directory / (name + ".lean")).read_text()) for name in (
        "InternerScopeProofs", "InternerScopeControl", "ScopedRecursive", "InternerScopeTests", "InternerPreparationTests"))
    source = imports + model + clients
    records = [mutation_check(output, "recursive-preparation-unchanged", source, True, env, lean)]
    selected = "if lookup.origin = .input then cursor else r.prepare request.arguments lookup cursor"
    for name, before, after in (
        ("omitted", selected, "cursor"),
        ("borrowed-input-prepared", selected, "r.prepare request.arguments lookup cursor"),
        ("stale-selection-effects", "r.prepare request.arguments lookup cursor", "r.prepare request.arguments lookup before.heap.allocationCursor"),
        ("repeated", "r.prepare request.arguments lookup cursor", "r.prepare request.arguments lookup (r.prepare request.arguments lookup cursor)"),
        ("lost-preparation-effects", "(.ok items, ⟨⟨some lookup, items, .lookup⟩, { heap with allocationCursor := cursor }⟩)",
         "(.ok items, ⟨⟨some lookup, items, .lookup⟩, heap⟩)"),
        ("prepares-after-oom", "| none => (.error .outOfMemory, { before with heap })",
         "| none => (.error .outOfMemory, { before with heap := { heap with allocationCursor := r.prepare request.arguments {} cursor } })"),
    ):
        if model.count(before) != 1:
            raise ValueError("ambiguous preparation control: " + name)
        records.append(mutation_check(output, "recursive-preparation-" + name,
            imports + model.replace(before, after) + clients, False, env, lean))
    for record in records:
        diagnostic = (output / (record["name"] + ".stdout")).read_text()
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant", diagnostic, re.I):
            raise ValueError("preparation control hit a resource or syntax failure: " + record["name"])
    return records
