#!/usr/bin/env python3
"""Audit native insertion control transport and its all-entry induction consumer.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import json
from pathlib import Path
import re

import check_item_preparation_erasure as preparation
from check_zig_air_memory_proofs import without_imports

native = preparation.native
MODULE = "Compiler.Extraction.InternerInsertionControlEffectsTests"
STORAGE = "Compiler.Extraction.Storage."
INSERT = preparation.INSERT
NS = INSERT + "Native."
RECURSION = preparation.entries.NS
TESTS = STORAGE + "ControlEffectTests."
CLAIMS = preparation.CLAIMS.copy()
for namespace, names in (
    (STORAGE + "Operations.Transport.", ["release_execute", "release_all", "cleanup_execute", "execute"]),
    (NS, ["callbacks_transport", "executionWithRoom_transport", "execution_transport", "checkedExecution_transport", "body_transport", "insert_transport"]),
    (RECURSION, ["base_native_transport", "unfold_native_erases"]),
    (TESTS, ["decorated_transport", "program_erases", "fixtures_erase", "success_preserves_history", "allocation_fault_stops",
        "cleanup_fault_stops", "publication_refusal_unwinds", "capacity_release_fault", "reached_continuation", "pure_command_skips_host"]),
    (STORAGE + "ExecutionTests.", ["deterministic_success", "nondeterministic_success", "capacity_cleanup", "duplicate_failure",
        "item_failure", "clone_failure", "append_failure", "publication_failure", "aliased_failure", "allocation_fault",
        "cleanup_fault", "cleanup_changes_later_allocation", "capacity_cleanup_fault", "semantic_execution", "success_words", "failures_restore"]),
    (NS + "CountTests.", ["native_boundary_reads", "capacity_boundary", "capacity_field_not_read", "mismatch_rejects",
        "unreadable_rejects", "only_normalized_cleanup"]),
):
    CLAIMS += [namespace + name for name in names]


def dependencies(output):
    checked = preparation.dependencies(output)
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    required = {
        STORAGE + "Operations.Transport.release_all": {STORAGE + "releaseAll", STORAGE + "Operations.Transport.release_execute"},
        STORAGE + "Operations.Transport.execute": {STORAGE + "Program.execute", STORAGE + "Operations.Transport.attempt",
            STORAGE + "Operations.Transport.cleanup_execute", STORAGE + "Operations.Transport.release_all"},
        NS + "callbacks_transport": {NS + "preparation_callback_transport", NS + "PendingTransport.arguments",
            NS + "PendingTransport.append", NS + "PendingTransport.publish", NS + "PendingTransport.release"},
        NS + "executionWithRoom_transport": {NS + "callbacks_transport", STORAGE + "Operations.Transport.execute",
            NS + "executionWithRoom", "Compiler.Extraction.Interner.InsertionExecution.project", INSERT + "cell"},
        NS + "checkedExecution_transport": {NS + "executionWithRoom_transport", NS + "checkedCount", NS + "checkedExecution"},
        NS + "body_transport": {NS + "checkedExecution_transport", NS + "body", INSERT + "projected", INSERT + "cell"},
        NS + "insert_transport": {NS + "body_transport", NS + "insert"},
        RECURSION + "base_native_transport": {NS + "insert_transport", NS + "callerPrimitives", RECURSION + "BaseTransport.mk"},
        RECURSION + "unfold_native_erases": {RECURSION + "base_native_transport", RECURSION + "unfold_erases", "Nat.rec"},
        TESTS + "program_erases": {STORAGE + "Operations.Transport.execute", TESTS + "decorated_transport"},
        TESTS + "fixtures_erase": {TESTS + "program_erases", STORAGE + "ExecutionTests.operations"},
        TESTS + "reached_continuation": {STORAGE + "ExecutionTests.continuationProgram", STORAGE + "ExecutionTests.dependentOperations",
            STORAGE + "Program.execute", TESTS + "tick"},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError("insertion control erasure lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return list(dict.fromkeys(checked + sorted(required)))


def source_parts():
    directory = native.ROOT / "lean/Compiler/Extraction"
    parts = [without_imports((directory / (name + ".lean")).read_text()) for name in (
        "StorageExecutionEffects", "InternerInsertionControlEffects", "InternerInsertionRecursionEffects", "InternerInsertionControlEffectsTests")]
    # Copy proof interfaces and the small fixture decorator, retaining the
    # imported production executor, native callbacks, count guard and routing.
    names = set(re.findall(r"^theorem (\w+)", "\n".join(parts[1:3]), re.M))
    for index, source in enumerate(parts):
        source = source.replace("Operations.Transport", "Operations.ControlTransport")
        source = source.replace("PendingTransport", "ControlPendingTransport").replace("CallbackObligations", "ControlCallbackObligations")
        source = source.replace("Storage.ControlEffectTests", "Storage.ControlEffectMutationTests")
        source = re.sub(r"\b(" + "|".join(sorted(names)) + r")\b", lambda m: m[0] + "_controlMutation", source)
        parts[index] = source
    return parts


def controls(output, env, lean):
    records = preparation.controls(output, env, lean)
    parts = source_parts()
    def program(parts):
        return "import " + MODULE + "\n" + "\n".join(parts)
    variants = []
    for name, index, before, after, occurrences in (
        ("attempt-before-append-only", 0, "attempt : ∀ site owner, Effect.Transport project",
            "attempt : ∀ site owner, owner.appended = false → Effect.Transport project", 1),
        ("release-before-append-only", 0, "release : ∀ action owner, Effect.Transport project",
            "release : ∀ action owner, owner.appended = false → Effect.Transport project", 1),
        ("rewound-release-sequence", 0, "project (releaseAll physical actions owner before).2", "project before", 1),
        ("different-branch-input", 0, "program.execute input original owner (project before)",
            "program.execute { input with deterministic := !input.deterministic } original owner (project before)", 1),
        ("item-for-clone", 1, "leftGrowth rightGrowth .clone (Or.inr rfl) owner",
            "leftGrowth rightGrowth .item (Or.inl rfl) owner", 1),
        ("zero-value-only", 1, "∀ cells value (leftGraph :", "∀ cells value, value = 0 → ∀ (leftGraph :", 1),
        ("different-count-container", 1, "checkedExecution right rightAllocate runtimeSafety allocator container source",
            "checkedExecution right rightAllocate runtimeSafety allocator (container + 1) source", 1),
        ("different-native-allocator", 2, "Insertion.Native.callerPrimitives right rightAllocate runtimeSafety allocator container",
            "Insertion.Native.callerPrimitives right rightAllocate runtimeSafety (allocator + 1) container", 2),
        ("lost-reached-effects", 3, "(result, (reached, before.2 + 1))", "(result, (before.1, before.2 + 1))", 1),
        ("lost-release-count", 3, "fun action owner => tick (calls.release action owner)",
            "fun action owner before => let (result, reached) := calls.release action owner before.1; (result, (reached, before.2))", 1),
    ):
        if parts[index].count(before) != occurrences:
            raise ValueError("ambiguous insertion control mutation: " + name)
        changed = parts.copy()
        changed[index] = changed[index].replace(before, after)
        variants.append((name, program(changed)))
    return records + native.check_controls(output, env, lean, program(parts), variants, prefix="insertion-control-")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--preflight", action="store_true")
    native.check(parser.parse_args(), module=MODULE, claims=CLAIMS, dependency_check=dependencies,
        control_check=controls, publication=True, native_dispatch=True, recursive_entries=True, item_preparation=True, insertion_control=True)
