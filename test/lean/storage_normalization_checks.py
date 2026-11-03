#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Check captured preparation's storage metadata and logical ownership projection.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""
import json
import re

import check_argument_memory
from check_argument_memory import ROOT, NS, MEMORY
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

MODULE = "Compiler.Extraction.ArgumentMemoryPreparationTests"
CLAIMS = check_argument_memory.CLAIMS + ["Compiler.ZigAir.MemoryAir." + n for n in (
    "Program.runFuel_retains_shape", "WordPairProgram.retains_shape")]
CLAIMS += [MEMORY + "WordCopy." + n for n in ("copyFrom_storage", "copy_storage")]
CLAIMS += ["Compiler.Extraction.InsertionSort." + n for n in (
    "insertUsing_preserves", "passesUsing_preserves", "runUsing_preserves", "Captured.outcome_state",
    "Captured.exchange_storage", "Captured.run_storage", "Copied.run_storage")]
CLAIMS += [NS + n for n in ("owned_retained", "copied_owned", "updated_owner", "updated_length", "related_publish", "copied_refines", "copied_result")]
CLAIMS += [NS + "PreparationTests." + n for n in (
    "update_witness", "wrong_allocator_not_updated", "wrong_extent_not_updated", "valid", "owned", "source_represented",
    "others_related", "provisional_contents_uninitialized", "provisional_not_related", "all_budgets_owned", "all_budgets_valid",
    "complete", "complete_values", "settles_with_projection", "every_budget_classified", "complete_related", "release_after_preparation",
    "release_preserves_relation", "release_retains_reached_counters", "released_alias_rejected", "zero_budget_is_incomplete",
    "suspended_owned", "exhausted_valid", "exhaustion_is_fault", "exhaustion_keeps_owned", "failed_copy_keeps_owned")]


def audit(output):
    claims = {claim["theorem"]: set(claim["dependencies"]) for claim in json.loads((output / "audit.json").read_text())["claims"]}
    sort = "Compiler.Extraction.InsertionSort."
    requirements = {
        "Compiler.ZigAir.MemoryAir.Program.runFuel_retains_shape": {
            "Compiler.ZigAir.MemoryAir.machine_steps_retain_shape", MEMORY + "cleanup_retains_shape"},
        sort + "Captured.run_storage": {sort + n for n in ("runUsing_preserves", "Captured.exchange_storage")}
            | {"Compiler.ZigAir.MemoryAir.WordPairProgram.retains_shape", "Compiler.ZigAir.GeneratedMemory.fn_swap_u32"},
        sort + "Copied.run_storage": {sort + "Captured.run_storage", MEMORY + "WordCopy.copy_storage", sort + "copySortUsing"},
        NS + "copied_owned": {NS + "Owned", NS + "owned_retained", sort + "Copied.run_storage", MEMORY + "Allocation.SameShape"},
        NS + "copied_refines": {NS + n for n in ("Updated", "Related", "related_publish", "copied_owned")}
            | {sort + "Copied.run_refines", "Compiler.ZigAir.GeneratedMemory.fn_swap_u32"},
        NS + "copied_result": {NS + n for n in ("Updated", "Related", "related_publish", "copied_owned")}
            | {sort + "Copied.run_result", "Compiler.ZigAir.GeneratedMemory.fn_swap_u32"},
        NS + "PreparationTests.settles_with_projection": {NS + "copied_refines", NS + "PreparationTests.others_related"},
        NS + "PreparationTests.every_budget_classified": {NS + "copied_result"},
        NS + "PreparationTests.release_preserves_relation": {NS + "release_refines", NS + "PreparationTests.complete_related"},
    }
    for name, needed in requirements.items():
        if not needed <= claims[name]:
            raise ValueError("normalization storage lost a memory, ownership or captured-call dependency: " + name)
    return {"checkedDependencies": sorted(requirements)}


def controls(output, env, lean):
    # Retain the checked release boundary controls as clients of the new bridge.
    records = check_argument_memory.controls(output, env, lean)
    directory = ROOT / "lean/Compiler/Extraction"
    source = "import Compiler.Extraction.InsertionSortStorage\nimport Compiler.Extraction.ArgumentMemoryTests\n"
    source += "import Compiler.Extraction.NormalizationPreparedMemoryTests\nimport Compiler.Extraction.InsertionSortCopiedTests\n"
    source += "import Compiler.ZigAir.MemoryWordCopyTests\n"
    source += "\n".join(without_imports((directory / name).read_text()) for name in (
        "ArgumentMemoryPreparation.lean", "ArgumentMemoryPreparationTests.lean"))
    records.append(mutation_check(output, "ownership-projection-unchanged", source, True, env, lean))
    for name, before, after in (
        ("projection-wrong-allocator", "after = write before id (some ⟨allocator, .arguments values⟩)",
         "after = write before id (some ⟨allocator + 1, .arguments values⟩)"),
        ("projection-wrong-contents", "after = write before id (some ⟨allocator, .arguments values⟩)",
         "after = write before id (some ⟨allocator, .arguments values.reverse⟩)"),
        ("projection-grows-extent", "previous.length = values.length ∧ after =", "previous.length ≤ values.length ∧ after ="),
        ("projection-shrinks-extent", "previous.length = values.length ∧ after =", "values.length ≤ previous.length ∧ after ="),
    ):
        if source.count(before) != 1:
            raise ValueError("ambiguous projection mutation: " + name)
        records.append(mutation_check(output, name, source.replace(before, after), False, env, lean))
    for record in records:
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant",
                     (output / (record["name"] + ".stdout")).read_text(), re.I):
            raise ValueError("storage control hit a resource or syntax failure: " + record["name"])
    return records
