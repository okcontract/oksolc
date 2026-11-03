#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Check the duplication contract needed by normalization's borrowed take path.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""
import json
import re

from check_argument_memory import ROOT, NS, MEMORY
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

MODULE = "Compiler.Extraction.ArgumentMemoryDuplicationTests"
DUPLICATION = NS + "Duplication."
CLAIMS = [DUPLICATION + n for n in (
    "run_length_rejected", "run_empty", "run_allocation_fault", "run_oom", "run_reached_effects", "run_preserves_valid",
    "copy_owned", "run_allocated_owned", "copy_registered", "empty_post", "run_of_allocation", "run_admitted", "run_total", "Post.release")]
CLAIMS += [DUPLICATION + "Tests." + n for n in (
    "complete", "exact_unsorted_contents", "source_and_other_preserved", "complete_post", "all_requests_classified",
    "counters_only_allocate", "independent_copy", "release_contract", "release_exact", "released_alias_dead", "released_source_retained",
    "borrowed_subslice", "empty_skips_invalid_heap_and_collision", "descriptor_mismatch_rejected", "oom_retains_effects",
    "invalid_region_is_fault", "collision_keeps_uninitialized_allocation", "incomplete_valid", "oom_precedes_source_reads",
    "copy_fault_retains_prefix", "copy_fault_valid", "copy_fault_owned", "copy_fault_not_published",
    "explicit_release_of_partial_copy", "all_responses_valid")]


def audit(output):
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_text())["claims"]}
    requirements = {
        DUPLICATION + "copy_registered": {MEMORY + "WordCopy.copy_refines", DUPLICATION + "copy_owned", NS + "related_publish"},
        DUPLICATION + "run_preserves_valid": {NS + "Allocation.reserve_preserves_valid", MEMORY + "WordCopy.copy_storage"},
        DUPLICATION + "run_allocated_owned": {NS + "Allocation.reserve_success", DUPLICATION + "copy_owned"},
        DUPLICATION + "run_of_allocation": {NS + "Allocation.reserve_success", DUPLICATION + "copy_registered", DUPLICATION + "Post"},
        DUPLICATION + "run_total": {DUPLICATION + n for n in ("run", "run_empty", "run_oom", "run_admitted", "empty_post", "Post")}
            | {NS + "Allocation.reserve_admitted", MEMORY + "WordCopy.copy_refines", MEMORY + "WordAllocation.Fits"},
        DUPLICATION + "Post.release": {NS + "release_refines", NS + "ReleasePost", DUPLICATION + "Post"},
        DUPLICATION + "Tests.complete_post": {DUPLICATION + "run_admitted"},
        DUPLICATION + "Tests.all_requests_classified": {DUPLICATION + "run_total"},
        DUPLICATION + "Tests.copy_fault_owned": {DUPLICATION + "run_allocated_owned"},
        DUPLICATION + "Tests.release_contract": {DUPLICATION + "Post.release"},
    }
    for name, needed in requirements.items():
        if not needed <= claims[name]:
            raise ValueError("duplication lost an allocation, copy, ownership or release dependency: " + name)
    return {"checkedDependencies": sorted(requirements), "obligation": "normalization.borrowedDuplicateContract",
            "productionPathConnected": False}


def controls(output, env, lean):
    source = "import Compiler.Extraction.ArgumentMemoryAllocationTests\n"
    source += "\n".join(without_imports((ROOT / "lean/Compiler/Extraction" / name).read_text()) for name in (
        "ArgumentMemoryDuplication.lean", "ArgumentMemoryDuplicationProofs.lean", "ArgumentMemoryDuplicationTests.lean"))
    records = [mutation_check(output, "duplication-unchanged", source, True, env, lean)]
    for name, before, after in (
        ("duplication-skips-copy", "let (copied, after) := WordCopy.copy allocated source (view destination)",
         "let (copied, after) := (Except.ok (), allocated)"),
        ("duplication-copies-uninitialized-target", "let (copied, after) := WordCopy.copy allocated source (view destination)",
         "let (copied, after) := WordCopy.copy allocated (view destination) (view destination)"),
        ("duplication-loses-copy-prefix", "| .error fault => ((.error (.memory fault), registered, after), reached)",
         "| .error fault => ((.error (.memory fault), registered, allocated), reached)"),
        ("duplication-fault-frees-buffer", "| .error fault => ((.error (.memory fault), registered, after), reached)",
         "| .error fault => ((.error (.memory fault), registered, erase after destination.address), reached)"),
        ("duplication-loses-fault-effects", "| .error fault => ((.error (.memory fault), registered, after), reached)",
         "| .error fault => ((.error (.memory fault), registered, after), effects)"),
        ("duplication-oom-is-semantic-fault", "| .ok none => ((.ok none, registered, allocated), reached)",
         "| .ok none => ((.error (.memory .outOfMemory), registered, allocated), reached)"),
        ("duplication-returns-borrow", "| .ok () => ((.ok (some destination), registered, after), reached)",
         "| .ok () => ((.ok (some ⟨source.allocation, items⟩), registered, after), reached)"),
        ("duplication-loses-registration", "| .ok () => ((.ok (some destination), registered, after), reached)",
         "| .ok () => ((.ok (some destination), heap, after), reached)"),
        ("duplication-ignores-descriptor", "if source.length ≠ items.length then", "if false then"),
    ):
        if source.count(before) != 1:
            raise ValueError("ambiguous duplication mutation: " + name)
        records.append(mutation_check(output, name, source.replace(before, after), False, env, lean))
    for record in records:
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant",
                     (output / (record["name"] + ".stdout")).read_text(), re.I):
            raise ValueError("duplication control hit a resource or syntax failure: " + record["name"])
    return records
