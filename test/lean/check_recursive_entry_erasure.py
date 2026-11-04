#!/usr/bin/env python3
"""Audit actual constructor entries and all-depth native erasure induction.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import json
from pathlib import Path

import check_native_dispatch_erasure as dispatch
from check_zig_air_memory_proofs import without_imports

native = dispatch.native
MODULE = "Compiler.Extraction.InternerNativeRecursionEffectsTests"
OWNED = native.OWNED
ITEM = OWNED + "ConstructorItem."
NS = ITEM + "NativeRecursion."
CLAIMS = dispatch.CLAIMS.copy()
for namespace, names in (
    ("TemporaryArguments.EffectTransport.", ["orderedStores", "writePair", "prepare", "unwind"]),
    ("TemporaryUnary.EffectTransport.", ["writeOne", "prepare"]),
    ("TemporaryTernary.EffectTransport.", ["writeTriple", "prepare"]),
    ("LocalArguments.EffectTransport.", ["initPair", "copy", "overwrite", "zigLocal"]),
    ("ConstructorFrame.EffectTransport.", ["find"]),
    ("ConstructorItem.EffectTransport.", ["finish", "enter", "prepare", "invoke"]),
    ("ConstructorItem.Arguments.EffectTransport.", ["prepare", "returned", "operation"]),
    ("ConstructorItem.ViewInput.EffectTransport.", ["operation", "localOperation", "constant", "constructors"]),
):
    CLAIMS += [OWNED + namespace + name for name in names]
CLAIMS += [NS + name for name in ("context_erases", "step_erases", "unfold_erases")]
CLAIMS += [NS + "RecursionEffectTests." + name for name in (
    "base_erases", "all_depths_erase", "literal_entry_erases", "borrowed_entry_erases", "local_entry_erases",
    "constant_entry_erases", "materialize_entry_erases", "local_shape_guard", "aggregate_fault_erases",
    "exhausted_keeps_world", "proper_child_enters_frames", "reached_child_erases")]
CLAIMS += [OWNED + "LocalArguments.Tests." + name for name in (
    "copied_offset_words", "false_flag_skips_overwrite", "overwrite_first_slot", "overwrite_second_slot",
    "aggregate_rejection_has_no_prefix", "rejected_second_load_keeps_allocation", "missing_source_keeps_allocation",
    "length_guard_precedes_allocation", "invalid_overwrite_keeps_initialized_copy", "stack_limit_precedes_load",
    "older_stack_borrow_survives_copy", "ordinary_success_unwinds_local", "ordinary_oom_unwinds_local")]
CLAIMS += [OWNED + "TemporaryArguments.Tests.rejected_store_retains_prefix"]


def dependencies(output):
    checked = dispatch.dependencies(output)
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    required = {
        OWNED + "LocalArguments.EffectTransport.zigLocal": {OWNED + "LocalArguments.copy",
            OWNED + "LocalArguments.EffectTransport.copy", OWNED + "LocalArguments.EffectTransport.overwrite"},
        OWNED + "ConstructorFrame.EffectTransport.find": {OWNED + "Caller.EffectTransport.find", OWNED + "ConstructorFrame.find"},
        ITEM + "EffectTransport.invoke": {OWNED + "ConstructorFrame.EffectTransport.find", ITEM + "EffectTransport.prepare", ITEM + "invoke"},
        ITEM + "Arguments.EffectTransport.operation": {ITEM + "EffectTransport.invoke", ITEM + "Arguments.EffectTransport.prepare",
            ITEM + "Arguments.EffectTransport.returned", OWNED + "TemporaryTernary.EffectTransport.prepare"},
        ITEM + "ViewInput.EffectTransport.constructors": {ITEM + "Arguments.EffectTransport.operation",
            ITEM + "ViewInput.EffectTransport.constant", ITEM + "ViewInput.EffectTransport.localOperation",
            ITEM + "ViewInput.EffectTransport.operation", OWNED + "LocalArguments.EffectTransport.zigLocal"},
        NS + "context_erases": {NS + "dispatcher_erases", NS + "BaseTransport.publish", NS + "BaseTransport.insert"},
        NS + "step_erases": {NS + "context_erases", ITEM + "ViewInput.EffectTransport.constructors", NS + "step"},
        NS + "unfold_erases": {"Nat.rec", NS + "step_erases", NS + "exhausted_erases", NS + "unfold"},
        NS + "RecursionEffectTests.base_erases": {dispatch.publication.TRACE + "publish_erases", native.TRACE + "transport"},
        NS + "RecursionEffectTests.all_depths_erase": {NS + "unfold_erases", NS + "RecursionEffectTests.base_erases"},
        NS + "RecursionEffectTests.proper_child_enters_frames": {NS + "unfold", ITEM + "invoke", ITEM + "prepare", OWNED + "Caller.find"},
        NS + "RecursionEffectTests.reached_child_erases": {NS + "unfold_erases", NS + "RecursionEffectTests.literal_entry_erases"},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError("recursive entry erasure lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return list(dict.fromkeys(checked + sorted(required)))


def source_parts():
    directory = native.ROOT / "lean/Compiler/Extraction"
    parts = [without_imports((directory / (name + ".lean")).read_text()) for name in (
        "InternerArgumentEffects", "InternerConstructorEffects", "InternerNativeRecursionEffects", "InternerNativeRecursionEffectsTests")]
    for index, source in enumerate(parts):
        for namespace in ("TemporaryArguments", "TemporaryUnary", "TemporaryTernary", "LocalArguments",
                          "ConstructorFrame", "ConstructorItem", "Arguments", "ViewInput"):
            source = source.replace(namespace + ".EffectTransport", namespace + ".EntryErasureMutation")
        source = source.replace("ShiftInput.Context.Transport", "ShiftInput.Context.EntryErasureTransport")
        source = source.replace("mapped : left.Transport", "mapped : left.EntryErasureTransport")
        source = source.replace("children debug).Transport", "children debug).EntryErasureTransport")
        source = source.replace("left debug).Transport", "left debug).EntryErasureTransport")
        source = source.replace("ConstructorItem.NativeRecursion", "ConstructorItem.NativeEntryErasureMutation")
        source = source.replace("open Compiler.Algebraic", "open " + NS[:-1] + "\nopen Compiler.Algebraic")
        parts[index] = source
    return parts


def controls(output, env, lean):
    records = dispatch.controls(output, env, lean)
    parts = source_parts()
    def program(parts):
        return "import " + MODULE + "\n" + "\n".join(parts)
    variants = []
    for name, index, before, after in (
        ("publication-single-id", 2, "publish : ∀ source address native key owned id,",
            "publish : ∀ source address native key owned id, id = 0 →"),
        ("insertion-deterministic-only", 2, "insert : ∀ source address native key owned deterministic,",
            "insert : ∀ source address native key owned deterministic, deterministic = true →"),
        ("context-empty-source-only", 1, "primitives : ∀ source address native,",
            "primitives : ∀ source address native, source.length = 0 →"),
        ("child-operation-only", 2,
            "(children : (Recursive.erasing project).Constructors left right) (debug : AssemblyItem.Fields.Values)",
            "(children : ∀ opcode values debug, (Recursive.erasing project).related (left.operation opcode values debug) (right.operation opcode values debug)) (debug : AssemblyItem.Fields.Values)"),
        ("different-recursion-depth", 2, "(unfold rightBase owner usizeBits depth) := by",
            "(unfold rightBase owner usizeBits (depth + 1)) := by"),
        ("different-cleanup-mark", 1, "Arguments.returned values mark (ran.1, ran.2.mapEffects project) =",
            "Arguments.returned values (mark + 1) (ran.1, ran.2.mapEffects project) ="),
        ("rewound-caller-state", 1,
            "(ConstructorItem.invoke physical budget allocator left queries source request debug before).2.mapEffects project) := by",
            "State.mapEffects project ⟨before, { lookup := none }⟩) := by"),
    ):
        if parts[index].count(before) != 1:
            raise ValueError("ambiguous recursive entry mutation: " + name)
        changed = parts.copy()
        changed[index] = changed[index].replace(before, after)
        variants.append((name, program(changed)))
    return records + native.check_controls(output, env, lean, program(parts), variants, prefix="recursive-entry-")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--preflight", action="store_true")
    native.check(parser.parse_args(), module=MODULE, claims=CLAIMS, dependency_check=dependencies,
        control_check=controls, publication=True, native_dispatch=True, recursive_entries=True)
