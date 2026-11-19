#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Audit checked persistent allocation feeding captured argument preparation.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""
import json
import re

from check_argument_memory import ROOT, NS, MEMORY
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

MODULE = "Compiler.Extraction.ArgumentMemoryAllocationTests"
WORD = MEMORY + "WordAllocation."
ALLOCATION = NS + "Allocation."
REGION = MEMORY + "RegionAllocation."
CLAIMS = [WORD + n for n in (
    "extend_valid", "extend_lookup", "next_id_fresh", "extend_load_other", "source_older", "source_preserved",
    "source_bytes_bound", "reserve_empty", "reserve_overflow", "reserve_failed", "reserve_admitted",
    "reserve_nonempty_success", "reserve_preserves_valid")]
CLAIMS += [ALLOCATION + n for n in (
    "extend_owned", "extend_others", "reserve_empty", "reserve_reached", "reserve_preserves_valid", "reserve_failed",
    "reserve_admitted", "reserve_success", "copied_refines")]
CLAIMS += [ALLOCATION + "Tests." + n for n in (
    "valid", "represented", "related", "fits", "admitted", "allocated_valid", "allocated_owned", "source_preserved",
    "provisional_uninitialized", "provisional_not_related", "fresh_lifetime_reused_region", "old_alias_dead",
    "cleanup_keeps_persistent", "high_water_retained", "empty_skips_external", "oom_retains_effects",
    "byte_overflow_skips_external", "invalid_length_rejected", "invalid_initial_heap_rejected", "null_region_rejected",
    "misaligned_region_rejected", "overlapping_region_rejected", "address_overflow_rejected", "collision_retains_allocation",
    "every_response_valid", "settles_from_allocation", "complete", "complete_values", "complete_related",
    "release_after_preparation", "release_retains_reached_counters", "released_alias_rejected")]

CLAIMS += [REGION + n for n in ("extend_valid", "extend_lookup", "extend_shape", "extend_load_other",
    "reserve_empty", "reserve_overflow", "reserve_failed", "reserve_admitted", "reserve_nonempty_success", "reserve_preserves_valid", "reserve_heap_other")]


def audit(output):
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_text())["claims"]}
    requirements = {
        REGION + "reserve_admitted": {REGION + "extend_valid", REGION + "Fits", REGION + "reserve"},
        WORD + "reserve_admitted": {REGION + "reserve", REGION + "extend_valid", WORD + "reserve", WORD + "extend_valid"},
        WORD + "extend_valid": {WORD + "Fits", WORD + "extend", MEMORY + "State.valid"},
        WORD + "source_bytes_bound": {MEMORY + "access_success_region", MEMORY + "WordArray.Represents"},
        ALLOCATION + "reserve_admitted": {WORD + "source_bytes_bound", WORD + "reserve_admitted", "Compiler.Extraction.Memory.allocate"},
        ALLOCATION + "reserve_success": {WORD + "reserve_nonempty_success", "Compiler.Extraction.Memory.allocate"},
        ALLOCATION + "reserve_preserves_valid": {ALLOCATION + "reserve_reached", WORD + "reserve_preserves_valid"},
        ALLOCATION + "copied_refines": {ALLOCATION + n for n in ("reserve_success", "extend_owned", "extend_others")}
            | {WORD + "source_older", WORD + "source_preserved", NS + "copied_refines", "Compiler.ZigAir.GeneratedMemory.fn_swap_u32"},
        ALLOCATION + "Tests.settles_from_allocation": {ALLOCATION + "copied_refines", ALLOCATION + "Tests.admitted"},
        ALLOCATION + "Tests.release_after_preparation": {NS + "release_refines", ALLOCATION + "Tests.complete_related"},
    }
    for name, needed in requirements.items():
        if not needed <= claims[name]:
            raise ValueError("allocation proof lost an external-contract, ownership or captured-call dependency: " + name)
    return {"checkedDependencies": sorted(requirements)}


def controls(output, env, lean):
    paths = [ROOT / "lean/Compiler/ZigAir" / n for n in ("MemoryRegionAllocation.lean",
        "MemoryRegionAllocationProofs.lean", "MemoryWordAllocation.lean", "MemoryWordAllocationProofs.lean")]
    paths += [ROOT / "lean/Compiler/Extraction" / n for n in (
        "ArgumentMemoryAllocation.lean", "ArgumentMemoryAllocationProofs.lean", "ArgumentMemoryAllocationTests.lean")]
    source = "import Compiler.Extraction.ArgumentMemoryPreparationTests\n"
    source += "\n".join(without_imports(path.read_text()) for path in paths)
    records = [mutation_check(output, "allocation-unchanged", source, True, env, lean)]
    for name, before, after in (
        ("allocation-stack-buffer", "⟨base, type, [], true, false⟩", "⟨base, type, [], true, true⟩"),
        ("allocation-readonly", "⟨base, type, [], true, false⟩", "⟨base, type, [], false, false⟩"),
        ("allocation-initializes-zero", "⟨base, type, [], true, false⟩",
         "⟨base, type, [(0, WordArray.number 0)], true, false⟩"),
        ("allocation-reuses-lifetime", ":: state.heap, state.nextId + 1,", ":: state.heap, state.nextId,"),
        ("allocation-rewinds-address", "max state.nextAddress (base + bytes)", "base + bytes"),
        ("allocation-ignores-region", "if after.valid then", "if true then"),
        ("allocation-forgets-failed-effects", "| none => ((.ok none, state), reached)", "| none => ((.ok none, state), effects)"),
        ("allocation-invalid-is-oom", "else ((.error .memoryValidity, state), reached)", "else ((.ok none, state), reached)"),
        ("allocation-zero-calls-external", "if length = 0 then ((.ok (some ⟨state.nextId, 0, 0⟩), state), effects) else",
         "if length = 0 then ((.ok (some ⟨state.nextId, 0, 0⟩), state), (allocate 0 effects).2) else"),
        ("allocation-overflow-is-fault", "if layout.bytes ≥ addressLimit then ((.ok none, state), effects) else",
         "if layout.bytes ≥ addressLimit then ((.error .malformed, state), effects) else"),
        ("allocation-forgets-alignment", "let (response, reached) := allocate layout.bytes layout.alignment effects",
         "let (response, reached) := allocate layout.bytes 4 effects"),
        ("allocation-wrong-allocator", "match Memory.allocate heap allocator target.allocation (.arguments items) true with",
         "match Memory.allocate heap 0 target.allocation (.arguments items) true with"),
        ("allocation-collision-rolls-back", "| .error fault => ((.error (.registry fault), heap, after), reached)",
         "| .error fault => ((.error (.registry fault), heap, state), reached)"),
        ("allocation-collision-is-oom", "| .error fault => ((.error (.registry fault), heap, after), reached)",
         "| .error _ => ((.ok none, heap, after), reached)"),
        ("allocation-registers-empty", "if items.isEmpty then ((.ok (some ⟨target.allocation, items⟩), heap, after), reached) else",
         "if false then ((.ok (some ⟨target.allocation, items⟩), heap, after), reached) else"),
    ):
        if source.count(before) != 1:
            raise ValueError("ambiguous allocation mutation: " + name)
        records.append(mutation_check(output, name, source.replace(before, after), False, env, lean))
    for record in records:
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant",
                     (output / (record["name"] + ".stdout")).read_text(), re.I):
            raise ValueError("allocation control hit a resource or syntax failure: " + record["name"])
    return records
