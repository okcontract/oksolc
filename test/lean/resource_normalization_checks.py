#!/usr/bin/env python3
"""Physical normalization adapter for the source-bound ownership protocol.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import json
import re

from check_argument_memory import ROOT, NS
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

MODULE = "Compiler.Extraction.NormalizationResourcesTests"
NORMALIZATION = NS + "Normalization."
ADAPTER = NORMALIZATION + "ResourceAdapter."
FILES = ["NormalizationResources" + suffix + ".lean" for suffix in (
    "", "Lifetime", "Preparation", "Init", "Proofs", "Tests")]
CLAIMS = [ADAPTER + name for name in (
    "continued_eq", "prepared_token", "prepared_continuation_eq", "prepare_init", "init_spec", "init_eq", "run_eq", "run_checked", "production_verified")]
CLAIMS += [ADAPTER + "Tests." + name for name in (
    "observations", "allocated_transfer", "scratch_transfer", "borrowed_lookup", "empty_transfer", "temporary_oom",
    "duplicate_oom", "suspension", "semantic_stack_exhaustion", "cleanup_retains_scratch", "partial_copy_fault",
    "release_fault", "missing_descriptor_rejects", "production_add")]


def audit(output):
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    required = {
        ADAPTER + "run_eq": {ADAPTER + n for n in (
            "run", "primitives", "allocate", "prepare", "release", "observe", "continued_eq", "init_spec", "prepare_init", "prepared_token")}
            | {NORMALIZATION + n for n in ("run", "reserve", "prepare", "takeOwned", "free")}
            | {"Compiler.Extraction.Cache.NormalizationOwnership.Code.runPrepared", NS + "Duplication.run",
               "Compiler.Extraction.InsertionSort.Copied.run"},
        ADAPTER + "production_verified": {ADAPTER + "run_checked", ADAPTER + "run_eq",
            NORMALIZATION + "production_verified", NORMALIZATION + "Post", NORMALIZATION + "Admitted"},
        ADAPTER + "Tests.production_add": {ADAPTER + "production_verified", ADAPTER + "Tests.scratch_transfer",
            NORMALIZATION + "Tests.actual_caller_allocation", NORMALIZATION + "Tests.external_admitted"},
        ADAPTER + "Tests.partial_copy_fault": {ADAPTER + "run_eq", ADAPTER + "run"},
        ADAPTER + "Tests.release_fault": {ADAPTER + "continued_eq", ADAPTER + "continued"},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError("normalization resource adapter lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return {"checkedDependencies": sorted(required), "obligation": "normalization.recursiveBridge",
            "physicalOwnershipAdapterVerified": True, "recursiveMemoryBridgeVerified": False,
            "boundary": "Exact physical PreparedPrimitives interpretation for all states and budgets; Scoped.Resources cursor refinement and intervening graph effects remain open."}


def controls(output, env, lean):
    imports = "import Compiler.Extraction.NormalizationMemoryTests\nimport Compiler.Extraction.NormalizationPrepared\n"
    bodies = [without_imports((ROOT / "lean/Compiler/Extraction" / name).read_text()) for name in FILES]
    model, clients = bodies[0], "\n".join(bodies[1:])
    records = [mutation_check(output, "normalization-resource-unchanged", imports + model + "\n" + clients, True, env, lean)]
    for name, before, after in (
        ("fault-is-oom", "if failure = .outOfMemory then none else some (.memory failure)", "none"),
        ("lost-failure-state", "session := memory, rejected := if failure", "session := before.session, rejected := if failure"),
        ("lost-allocation-handle", "handle := ⟨view slice, values, some slice⟩", "handle := before.handle"),
        ("wrong-preparation-target", "source target values", "source source values"),
        ("lost-preparation-writes", "(.error failure, { before with session := memory })", "(.error failure, before)"),
        ("omitted-free", "Normalization.free external allocator slice before.session", "(Except.ok (), before.session)"),
        ("accepted-release-fault", "| .error failure => some (.memory failure)", "| .error _ => none"),
        ("lost-transferred-slice", "transferred := some slice", "transferred := none"),
    ):
        if model.count(before) != 1:
            raise ValueError("ambiguous resource adapter mutation: " + name)
        changed = imports + model.replace(before, after) + "\n" + clients
        records.append(mutation_check(output, "normalization-resource-" + name, changed, False, env, lean))
    for record in records:
        diagnostic = (output / (record["name"] + ".stdout")).read_text()
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant", diagnostic, re.I):
            raise ValueError("resource adapter control hit a resource or syntax failure: " + record["name"])
    return records
