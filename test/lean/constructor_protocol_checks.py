"""Constructor wrapper and finite recursive protocol checks for the scoped gate.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import json
import re

import check_native_resource_trace as native
from check_zig_air_memory_proofs import without_imports

WRAPPER = native.OWNED + "ConstructorItem.ProtocolTrace."
RECURSIVE = native.OWNED + "ConstructorItem.NativeRecursion.ProtocolTrace."
CALLER = native.OWNED + "Caller.ProtocolTrace."
CLAIMS = [WRAPPER + name for name in (
    "retire_native", "retire_prefix", "retire_metadata", "retire_scope", "frame_erases", "frame_prefix", "item_erases", "item_prefix",
    "literal_erases", "literal_prefix", "local_erases", "local_prefix", "constructors_erases", "constructors_prefix")]
CLAIMS += [RECURSIVE + name for name in (
    "map_atDebug", "step_erases", "step_prefix", "unfold_erases", "unfold_prefix", "children_recorded", "children_erases", "initialized_children")]
CLAIMS += [WRAPPER + "Tests." + name for name in (
    "cache_events", "cache_scope", "cache_composed", "rejected_retirement", "failed_literal", "failed_local")]
CLAIMS += [RECURSIVE + "Tests." + name for name in ("recursive_oom", "recursive_prefix", "exhausted")]


def dependencies(output):
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    required = {
        WRAPPER + "retire_native": {WRAPPER + "retire", native.OWNED + "TemporaryArguments.unwind"},
        WRAPPER + "retire_metadata": {WRAPPER + "retire"},
        WRAPPER + "retire_scope": {WRAPPER + "retire", CALLER + "scopeView", native.OWNED + "TemporaryArguments.unwind"},
        WRAPPER + "Tests.cache_scope": {WRAPPER + "Tests.cache_returned", CALLER + "Tests.cache_scope"},
        WRAPPER + "frame_erases": {WRAPPER + "retire_native", CALLER + "find_erases", native.OWNED + "ConstructorFrame.find"},
        WRAPPER + "frame_prefix": {CALLER + "find_segment", WRAPPER + "frame"},
        WRAPPER + "item_erases": {WRAPPER + "frame_erases", WRAPPER + "retire_native", native.OWNED + "ConstructorItem.invoke"},
        WRAPPER + "item_prefix": {WRAPPER + "frame_prefix", WRAPPER + "retire_prefix"},
        WRAPPER + "literal_erases": {WRAPPER + "item_erases", native.OWNED + "ConstructorItem.Arguments.operation"},
        WRAPPER + "local_erases": {WRAPPER + "item_erases", native.OWNED + "ConstructorItem.ViewInput.localOperation"},
        WRAPPER + "constructors_erases": {WRAPPER + n for n in ("literal_erases", "item_erases", "local_erases", "constructors")},
        WRAPPER + "constructors_prefix": {WRAPPER + n for n in ("literal_prefix", "item_prefix", "local_prefix")},
        RECURSIVE + "step_erases": {WRAPPER + "constructors_erases", CALLER + "Native.graphObservations", RECURSIVE + "step"},
        RECURSIVE + "step_prefix": {WRAPPER + "constructors_prefix", RECURSIVE + "map_atDebug"},
        RECURSIVE + "unfold_erases": {RECURSIVE + "step_erases", RECURSIVE + "unfold", native.OWNED + "ConstructorItem.NativeRecursion.unfold"},
        RECURSIVE + "unfold_prefix": {RECURSIVE + "step_prefix", RECURSIVE + "unfold"},
        RECURSIVE + "children_recorded": {RECURSIVE + "unfold_erases", RECURSIVE + "observe", RECURSIVE + "children"},
        RECURSIVE + "children_erases": {native.OWNED + "ConstructorItem.NativeRecursion.ChildTrace.constructors_erase"},
        RECURSIVE + "initialized_children": {native.OWNED + "MissStream.initialized_recorded_children", RECURSIVE + "unfold", RECURSIVE + "observe"},
        WRAPPER + "Tests.cache_events": {WRAPPER + "Tests.cache_returned", CALLER + "Tests.cache_events"},
        WRAPPER + "Tests.cache_composed": {WRAPPER + "item_erases", WRAPPER + "Tests.cache_events", native.OWNED + "ConstructorItem.CacheTests.completed"},
        RECURSIVE + "Tests.recursive_oom": {RECURSIVE + "Tests.parent", RECURSIVE + "Tests.nestedFailure", RECURSIVE + "unfold"},
        RECURSIVE + "Tests.recursive_prefix": {RECURSIVE + "unfold_prefix"},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError("constructor protocol lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return sorted(required)


def controls(output, env, lean):
    directory = native.ROOT / "lean/Compiler/Extraction"
    parts = [without_imports((directory / (name + ".lean")).read_text())
        .replace("ConstructorItem.ProtocolTrace", "ConstructorItem.WrapperTraceMutation")
        .replace("NativeRecursion.ProtocolTrace", "NativeRecursion.RecursiveTraceMutation")
        for name in ("InternerConstructorProtocolTrace", "InternerConstructorProtocolReturn", "InternerRecursiveProtocolTrace", "InternerConstructorProtocolTraceTests")]

    def program(parts):
        return "import Compiler.Extraction.InternerConstructorProtocolTraceTests\n" + "\n".join(parts)

    variants = []
    for name, index, before, after, count in (
        ("lost-initial-history", 0, "⟨⟨before, { lookup := none }⟩, {}, leading⟩", "⟨⟨before, { lookup := none }⟩, {}, []⟩", 1),
        ("wrong-retirement-mark", 0, "TemporaryArguments.unwind mark (ran.1, ran.2.native)", "TemporaryArguments.unwind (mark + 1) (ran.1, ran.2.native)", 1),
        ("lost-retirement-events", 0, "{ ran.2 with native := { ran.2.native with world := returned.2 } }",
         "{ ran.2 with native := { ran.2.native with world := returned.2 }, events := [] }", 1),
        ("lost-retirement-token", 0, "{ ran.2 with native := { ran.2.native with world := returned.2 } }",
         "{ ran.2 with native := { ran.2.native with world := returned.2 }, tokens := {} }", 1),
        ("wrong-capacity-guard", 0, "if q.atCapacity before.graph then", "if !q.atCapacity before.graph then", 1),
        ("wrong-scratch-extent", 0, "Memory.allocate before.memory.memory (.array 2 word) with", "Memory.allocate before.memory.memory (.array 3 word) with", 3),
        ("wrong-scratch-view", 0, "ports source ⟨mark, 0, 2⟩ request", "ports source ⟨mark, 1, 2⟩ request", 1),
        ("lost-item-preparation", 0, "source request prepared leading)", "source request before leading)", 1),
        ("lost-literal-preparation", 0, "operationRequest opcode values) debug prepared leading", "operationRequest opcode values) debug before leading", 1),
        ("wrong-local-selection", 0, "LocalArguments.zigLocal source selected repeated first before with",
         "LocalArguments.zigLocal source 0 repeated first before with", 3),
        ("wrong-borrowed-address", 0, "item context ports ⟨address, 0, values.length⟩", "item context ports ⟨0, 0, values.length⟩", 1),
        ("wrong-materialized-value", 0, "materialize := fun _ value debug => item context ports ⟨0, 0, 0⟩ (Interner.constructorCode.constantRequest value)",
         "materialize := fun _ value debug => item context ports ⟨0, 0, 0⟩ (Interner.constructorCode.constantRequest (value + 1))", 1),
        ("lost-local-copy", 0, "operationRequest opcode\n        (if first then [left, right].set selected repeated else [left, right])) debug prepared leading",
         "operationRequest opcode\n        (if first then [left, right].set selected repeated else [left, right])) debug before leading", 1),
        ("lost-child-events", 2, "(fun action before => (action before []).2.events) captured", "(fun _ _ => []) captured", 1),
        ("wrong-proper-child-depth", 2, "owner usizeBits depth)\n      (observe (unfold depth))", "owner usizeBits 0)\n      (observe (unfold depth))", 1),
        ("exhaustion-is-oom", 2, "(actual.1, start actual.2 leading)", "(.error (.language .outOfMemory), start actual.2 leading)", 1),
        ("wrong-caller-budget", 2, "atDebug fun debug => ConstructorItem.WrapperTraceMutation.constructors\n    (context (callerContext ops allocate safety owner meaning base growth)",
         "atDebug fun debug => ConstructorItem.WrapperTraceMutation.constructors\n    (context (callerContext ops allocate safety owner meaning { base with budget := 0 } growth)", 1),
    ):
        if parts[index].count(before) != count:
            raise ValueError("ambiguous constructor protocol mutation: " + name)
        changed = parts.copy()
        changed[index] = changed[index].replace(before, after)
        variants.append((name, program(changed)))
    records = native.check_controls(output, env, lean, program(parts), variants, prefix="constructor-protocol-")
    for record in records:
        if not record["expectedAcceptance"] and not re.search(
                r"error: (?:Not a definitional equality|Application type mismatch|Type mismatch|Tactic[^\n]*failed|unsolved goals)",
                (output / (record["name"] + ".stdout")).read_text()):
            raise ValueError("constructor protocol control lacks a semantic proof failure: " + record["name"])
    return records
