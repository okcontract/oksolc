#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Check normalization ownership across stateful copy/sort preparation.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""
import json
from pathlib import Path
import re

import extract_cache
from build_toolchain import digest
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

ROOT = Path(__file__).resolve().parents[2]
MODULE = "Compiler.Extraction.NormalizationPreparedMemoryTests"
NS = "Compiler.Extraction.Cache.NormalizationOwnership."
CLAIMS = [NS + n for n in ("run_safe", "run_with_projection", "run_with_safe", "init_with_ready", "take_with_success",
    "take_with_failure", "deinit_with_ready", "deinit_with_taken", "run_prepared_expand", "run_prepared_identity", "prepared_fault", "prepared_success",
    "finish_ready_safe", "finish_taken_safe", "finish_cleaned_safe", "continue_with_safe", "run_prepared_safe",
    "copied_ownership_safe", "copied_run_settles")]
CLAIMS += [NS + "EffectTests." + n for n in ("safe", "temporary_transfer", "repeated_failure", "lookup_cleanup", "caller_cleanup",
    "scratch_cleanup", "live_ready", "transferred_taken", "reuse_after_release")]
CLAIMS += [NS + "PreparedTests." + n for n in ("safe", "allocated_transfer", "allocated_lookup", "allocated_cleanup",
    "scratch_duplicates_after_prepare", "post_prepare_allocation_failure", "initial_projection_is_not_post_prepare_decision",
    "failed_initializer_skips_prepare", "allocated_fault_keeps_live_token", "fault_is_not_closed", "scratch_suspension_skips_transfer",
    "borrowed_skips_faulting_prepare", "singleton_skips_faulting_prepare", "empty_skips_faulting_prepare")]
CLAIMS += [NS + "PreparedMemoryTests." + n for n in ("before_valid", "target_writable", "source_represented",
    "initial_allocation_would_succeed", "original_projection_transfers", "prepared_allocation_failure", "prepared_counters",
    "prepared_values", "zero_budget_keeps_copy", "private_exhaustion_is_semantic_fault", "whole_scope_settles", "all_budgets_ownership_safe")]


def source_binding(output):
    paths = (extract_cache.SOURCE, extract_cache.SEMANTICS, extract_cache.ITEMS, extract_cache.OPCODES)
    generated = extract_cache.extract(*(p.read_bytes() for p in paths))
    (output / "CacheProgram.lean").write_bytes(generated)
    if generated != extract_cache.OUTPUT.read_bytes():
        raise ValueError("ownership decisions differ from fresh production extraction")
    return {"generatedSha256": digest(output / "CacheProgram.lean"),
            "sources": {str(p.relative_to(ROOT)): digest(p) for p in paths}}


def audit(output):
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_text())["claims"]}
    requirements = {
        NS + "run_prepared_safe": {NS + n for n in ("PreparedSafe", "Ready", "Safe", "Code.runPrepared", "Code.continueWith",
            "init_with_ready", "continue_with_safe", "take_with_success", "take_with_failure", "deinit_with_ready", "deinit_with_taken")},
        NS + "run_prepared_identity": {NS + "Code.runWith", NS + "Code.runPrepared", NS + "Code.continueWith"},
        NS + "copied_run_settles": {NS + n for n in ("copiedPrimitives", "prepared_success", "prepared_fault", "copied_ownership_safe")}
            | {"Compiler.Extraction.InsertionSort.Copied.run_refines", "Compiler.ZigAir.GeneratedMemory.fn_swap_u32"},
        NS + "PreparedMemoryTests.whole_scope_settles": {NS + "copied_run_settles"},
        NS + "PreparedMemoryTests.all_budgets_ownership_safe": {NS + "copied_ownership_safe"},
    }
    for name, needed in requirements.items():
        if not needed <= claims[name]:
            raise ValueError("prepared normalization lost a control, ownership or captured-call dependency: " + name)
    return {"checkedDependencies": sorted(requirements)}


def controls(output, env, lean):
    directory = ROOT / "lean/Compiler/Extraction"
    source = "import Compiler.Extraction.NormalizationEffectTests\n" + "".join(
        without_imports((directory / name).read_text()) for name in
        ("NormalizationPrepared.lean", "NormalizationPreparedProofs.lean", "NormalizationPreparedTests.lean"))
    source += '''
open Compiler.Extraction.Cache.NormalizationOwnership in
example : ¬PreparedSafe (.error (0, { invalid := true }) : PreparedResult Nat) := by simp [PreparedSafe, Ready]
open Compiler.Extraction.Cache.NormalizationOwnership in
example : ¬PreparedSafe (.ok (.lookup, {}) : PreparedResult Nat) := by simp [PreparedSafe, Safe]
'''
    records = [mutation_check(output, "preparation-unchanged", source, True, env, lean)]
    for name, before, after in (
        ("preparation-lost-state", "code.continueWith p.toPrimitives exit state prepared",
         "code.continueWith p.toPrimitives exit state effects"),
        ("preparation-wrong-branch", "if state.origin = .input then", "if state.origin ≠ .input then"),
        ("preparation-fault-loses-effects", "(.error (reason, state), prepared)", "(.error (reason, state), selected)"),
        ("preparation-fault-is-ordinary-oom", "| .error reason => (.error (reason, state), prepared)",
         "| .error _ => (.ok none, prepared)"),
        ("preparation-fault-closes-token", "(.error (reason, state), prepared)", "(.error (reason, { state with dead := true }), prepared)"),
        ("preparation-skipped", "else p.prepare state selected", "else (.ok (), selected)"),
        ("preparation-fault-predicate-weakened", "| .error (_, state) => Ready state", "| .error _ => True"),
        ("preparation-normal-predicate-weakened", "| .ok value => Safe value", "| .ok _ => True"),
    ):
        # Change execution definitions while retaining the compatibility equation
        # as an independent client. Predicate controls still target their owner.
        boundary = source.index("/-- Compatibility equation")
        implementation, clients = source[:boundary], source[boundary:]
        target = clients if "predicate" in name else implementation
        if target.count(before) != 1:
            raise ValueError("ambiguous preparation mutation: " + name)
        changed = (implementation + clients.replace(before, after) if "predicate" in name
                   else implementation.replace(before, after) + clients)
        records.append(mutation_check(output, name, changed, False, env, lean))
    # Recheck the old ownership-effect regression controls after sharing the
    # continuation, rather than assuming a definitional refactor preserves them.
    import check_compiler
    for name, (text, _) in check_compiler.NEGATIVES.items():
        if name.startswith("normalization_effect_"):
            records.append(mutation_check(output, "legacy-" + name, text, False, env, lean))
    for record in records:
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant",
                     (output / (record["name"] + ".stdout")).read_text(), re.I):
            raise ValueError("prepared control hit a resource or syntax failure: " + record["name"])
    return records
