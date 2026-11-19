"""Initialized item return and its actual finite constructor consumers.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import json
import re

import check_native_resource_trace as native
import protocol_effects_checks as protocol_effects
from check_zig_air_memory_proofs import without_imports

ITEM = native.OWNED + "ConstructorItem."
NS = ITEM + "ProtocolTrace."
RECURSIVE = ITEM + "NativeRecursion.ProtocolTrace."
CLAIMS = [NS + name for name in ("retire_outcome", "item_returned", "item_miss_traced", "Tests.cache_returned",
    "prepared_miss_map", "literal_miss_traced", "local_miss_traced", "Tests.local_unused_slot", "Tests.rejected_local_slot")]
CLAIMS += [RECURSIVE + name for name in ("borrowed_miss_projected", "constant_miss_projected", "materialize_miss_projected",
    "operation_miss_projected", "local_miss_projected")]
CLAIMS += [ITEM + "ViewInput.local_input_optional"]
CLAIMS += protocol_effects.CLAIMS


def dependencies(output):
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    required = {
        NS + "retire_outcome": {NS + "retire_scope", NS + "retire_metadata", NS + "outcome"},
        NS + "item_returned": {NS + "retire_outcome", ITEM + "invoke_after_scratch", NS + "item_erases",
            native.OWNED + "Caller.ProtocolTrace.find_erases"},
        NS + "item_miss_traced": {ITEM + "prepare_scratch", ITEM + "prepare_success", ITEM + "good_frame",
            native.OWNED + "Caller.ProtocolTrace.Native.initialized_miss_traced", NS + "item_returned", NS + "ItemMiss", NS + "PreparedMiss"},
        NS + "Tests.cache_returned": {NS + "item_returned", ITEM + "CacheTests.prefix_observed"},
        NS + "prepared_miss_map": {NS + "PreparedMiss", NS + "outcome"},
        NS + "literal_miss_traced": {ITEM + "Arguments.prepare_success", NS + "item_miss_traced", NS + "prepared_miss_map",
            NS + "retire_outcome", NS + "literal"},
        NS + "local_miss_traced": {ITEM + "ViewInput.local_input_optional", NS + "item_miss_traced", NS + "prepared_miss_map",
            NS + "retire_outcome", NS + "namedLocal"},
        ITEM + "ViewInput.local_input_optional": {ITEM + "ViewInput.local_input", native.OWNED + "LocalArguments.zigLocal"},
        NS + "Tests.local_unused_slot": {ITEM + "ViewInput.local_input_optional", native.OWNED + "LocalArguments.Tests.source_represented"},
        NS + "Tests.rejected_local_slot": {NS + "Tests.failed_local", native.OWNED + "LocalArguments.Tests.invalid_overwrite_keeps_initialized_copy"},
        RECURSIVE + "operation_miss_projected": {NS + "literal_miss_traced", NS + "PreparedMiss", RECURSIVE + "step", RECURSIVE + "children"},
        RECURSIVE + "local_miss_projected": {NS + "local_miss_traced", NS + "PreparedMiss", RECURSIVE + "step", RECURSIVE + "children"},
        RECURSIVE + "borrowed_miss_projected": {NS + "item_miss_traced", NS + "ItemMiss", RECURSIVE + "step",
            RECURSIVE + "children", RECURSIVE + "observe", RECURSIVE + "unfold"},
        RECURSIVE + "constant_miss_projected": {NS + "item_miss_traced", NS + "ItemMiss", RECURSIVE + "step",
            RECURSIVE + "children", RECURSIVE + "observe", RECURSIVE + "unfold"},
        RECURSIVE + "materialize_miss_projected": {RECURSIVE + "constant_miss_projected", NS + "ItemMiss", RECURSIVE + "step"},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError("constructor return lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return sorted(required) + protocol_effects.dependencies(output)


def controls(output, env, lean):
    directory = native.ROOT / "lean/Compiler/Extraction"
    parts = [without_imports((directory / (name + ".lean")).read_text()) for name in (
        "InternerConstructorProtocolReturn", "InternerConstructorProtocolMiss", "InternerConstructorPreparedMiss", "InternerRecursiveProtocolReturn")]
    inputs = (directory / "InternerViewInput.lean").read_text()
    start, end = "theorem local_input_optional", "\ntheorem local_prepared"
    if inputs.count(start) != 1 or inputs.count(end) != 1:
        raise ValueError("ambiguous optional local input theorem")
    optional = start + inputs.split(start)[1].split(end)[0]
    parts.append("namespace " + ITEM + "ViewInput\n"
        + "open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage\n"
        + "open Compiler.ZigAir.Memory.WordArray\n" + optional + "\nend " + ITEM + "ViewInput\n")
    for index in range(len(parts)):
        for name in ("outcome", "retire_outcome", "item_returned", "ItemMiss", "item_miss_traced",
                     "borrowed_miss_projected", "constant_miss_projected", "materialize_miss_projected", "PreparedMiss",
                     "prepared_miss_map", "literal_miss_traced", "local_miss_traced", "operation_miss_projected",
                     "local_miss_projected", "local_input_optional"):
            parts[index] = re.sub(r"\b" + name + r"\b", name + "Mutation", parts[index])

    def program(sources):
        return "import Compiler.Extraction.InternerConstructorProtocolTraceTests\n" + sources[4] + "\n".join(sources[:4])

    variants = []
    for name, index, before, after, count in (
        ("wrong-item-return-mark", 0,
         "world := returnWorld before.memory.memory.nextId constructed.memory.memory.nextId called.2.native.world",
         "world := returnWorld (before.memory.memory.nextId + 1) constructed.memory.memory.nextId called.2.native.world", 1),
        # A larger inner mark can be masked by outer cleanup; zero can retire live parent cells.
        ("wrong-scratch-return-mark", 0,
         "world := returnWorld before.memory.memory.nextId constructed.memory.memory.nextId called.2.native.world",
         "world := returnWorld before.memory.memory.nextId 0 called.2.native.world", 1),
        ("rejection-runs-retirement", 0, "if ordinary called.1 then", "if !ordinary called.1 then", 1),
        ("miss-loses-child-history", 1,
         "missLeading ++ middle ++ observed.body ++ observed.cleanup, false)",
         "missLeading ++ observed.body ++ observed.cleanup, false)", 1),
        ("miss-loses-cleanup-history", 1,
         "missLeading ++ middle ++ observed.body ++ observed.cleanup, false)",
         "missLeading ++ middle ++ observed.body, false)", 1),
        ("miss-incomplete", 1,
         "missLeading ++ middle ++ observed.body ++ observed.cleanup, false)",
         "missLeading ++ middle ++ observed.body ++ observed.cleanup, true)", 1),
        ("miss-wrong-entry-cursor", 1,
         "let logical := Interner.Scoped.findDetailed r logicalModel request { constructed.graph with allocationCursor := leading.length }",
         "let logical := Interner.Scoped.findDetailed r logicalModel request { constructed.graph with allocationCursor := 0 }", 1),
        ("miss-wrong-item-mark", 1,
         "actual = returned (retire before.memory.memory.nextId (retire constructed.memory.memory.nextId finished))",
         "actual = returned (retire (before.memory.memory.nextId + 1) (retire constructed.memory.memory.nextId finished))", 1),
        ("mapped-return-loses-outer-cleanup", 2,
         "wrapped (fun ran => after (returned ran)) := by", "wrapped returned := by", 1),
        ("mapped-return-loses-inner-return", 2,
         "wrapped (fun ran => after (returned ran)) := by", "wrapped after := by", 1),
        ("literal-wrong-argument-mark", 2,
         "(fun result => if values.isEmpty then result else retire before.memory.memory.nextId result) := by",
         "(fun result => if values.isEmpty then result else retire prepared.memory.memory.nextId result) := by", 1),
        ("empty-literal-retires-parent", 2,
         "(fun result => if values.isEmpty then result else retire before.memory.memory.nextId result) := by",
         "(fun result => if values.isEmpty then retire 0 result else retire before.memory.memory.nextId result) := by", 1),
        ("local-wrong-argument-mark", 2,
         "(retire before.memory.memory.nextId) := by", "(retire prepared.memory.memory.nextId) := by", 1),
        ("local-wrong-selected-slot", 2,
         "opcode source left right repeated selected first debug before)",
         "opcode source left right repeated (selected + 1) first debug before)", 1),
        ("literal-field-repeats-preparation", 3,
         "opcode values debug before)", "opcode values debug prepared)", 1),
        ("local-field-flips-overwrite", 3,
         "opcode source selected repeated first debug before)", "opcode source selected repeated (!first) debug before)", 1),
        ("local-bound-on-wrong-branch", 4,
         "repeatedIsFirst = true → selected < 2", "repeatedIsFirst = false → selected < 2", 1),
        ("borrowed-wrong-address", 3,
         "source.address opcode source.items debug) :=", "0 opcode source.items debug) :=", 1),
        ("constant-wrong-value", 3, ")).constant value debug) :=", ")).constant (value + 1) debug) :=", 1),
        ("materialize-wrong-value", 3, ")).materialize id value debug) :=", ")).materialize id (value + 1) debug) :=", 1),
        ("wrong-child-observation-depth", 3,
         "(ChildTrace.liftObservations (observe (unfold ops allocate safety owner meaning base growth usizeBits depth)))",
         "(ChildTrace.liftObservations (observe (unfold ops allocate safety owner meaning base growth usizeBits (depth + 1))))", 5),
    ):
        if parts[index].count(before) != count:
            raise ValueError("ambiguous constructor return mutation: " + name)
        changed = parts.copy()
        changed[index] = changed[index].replace(before, after)
        variants.append((name, program(changed)))
    records = native.check_controls(output, env, lean, program(parts), variants, prefix="constructor-return-")
    for record in records:
        if not record["expectedAcceptance"] and not re.search(
                r"error: (?:Not a definitional equality|Application type mismatch|Type mismatch|Tactic[^\n]*failed|unsolved goals)",
                (output / (record["name"] + ".stdout")).read_text()):
            raise ValueError("constructor return control lacks a semantic proof failure: " + record["name"])
    return records + protocol_effects.controls(output, env, lean)
