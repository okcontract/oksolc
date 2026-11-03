"""Child-history identity and its actual recorded-miss consumers.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import json
import re

import check_native_resource_trace as native
from check_zig_air_memory_proofs import without_imports

CHILD = native.OWNED + "ConstructorItem.NativeRecursion.ChildTrace."
NS = native.OWNED + "Caller.ProtocolTrace.Native."
FINITE = native.OWNED + "ConstructorItem.NativeRecursion.ProtocolTrace."
TESTS = native.OWNED + "Caller.ProtocolTrace.HistoryTests."
CLAIMS = [CHILD + name for name in ("record_flatten", "constructors_flatten")]
CLAIMS += [NS + name for name in ("dispatch_history", "middle_history", "history_boundaries", "miss_traced_verified")]
CLAIMS += [FINITE + "miss_projected"]
CLAIMS += [TESTS + name for name in ("unchanged_native", "guarded_history", "spare_traced")]


def dependencies(output):
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    required = {
        CHILD + "record_flatten": {CHILD + "record", CHILD + "flatten"},
        CHILD + "constructors_flatten": {CHILD + "record_flatten", CHILD + "constructors", CHILD + "liftObservations"},
        NS + "dispatch_history": {CHILD + "constructors_flatten", NS + "dispatch"},
        NS + "middle_history": {NS + "dispatch_history", NS + "middle", native.OWNED + "ConstructorItem.NativeRecursion.dispatcher_snapshot"},
        NS + "history_boundaries": {NS + "middle_history", native.OWNED + "MissStream.child_boundaries"},
        NS + "miss_traced_verified": {NS + "history_boundaries", NS + "miss_verified", NS + "MissProjected"},
        FINITE + "miss_projected": {NS + "miss_traced_verified", FINITE + "children", FINITE + "observe", FINITE + "unfold"},
        TESTS + "unchanged_native": {CHILD + "record", CHILD + "flatten", CHILD + "erase_restore"},
        TESTS + "guarded_history": {NS + "history_boundaries", NS + "middle_history", CHILD + "Tests.children"},
        TESTS + "spare_traced": {NS + "miss_resource_traced", native.OWNED + "Insertion.Native.NativeSpareTests.reached_frame",
            native.OWNED + "Recursive.Resource.Projects.mk"},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError("child history lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return sorted(required)


def controls(output, env, lean):
    directory = native.ROOT / "lean/Compiler/Extraction"
    parts = [without_imports((directory / (name + ".lean")).read_text()) for name in (
        "InternerInvocationChildHistory", "InternerCallerProtocolHistory", "InternerRecursiveProtocolMiss", "InternerCallerProtocolHistoryTests")]
    names = ("liftObservations", "flatten", "record_flatten", "constructors_flatten", "dispatch_history", "middle_history",
        "history_boundaries", "miss_traced_verified", "miss_projected", "HistoryTests")
    for index in range(len(parts)):
        for name in names:
            parts[index] = re.sub(r"\b" + name + r"\b", name + "Mutation", parts[index])

    def program(sources):
        return "import Compiler.Extraction.InternerCallerProtocolHistoryTests\n" + "\n".join(sources)

    variants = []
    for name, index, before, after in (
        ("uses-inner-history", 0, "(effects.1.1, effects.2)", "(effects.1.1, effects.1.2)"),
        ("loses-outer-history", 0, "(effects.1.1, effects.2)", "(effects.1.1, [])"),
        ("counts-inner-prefix", 0, "(effects.1.1, effects.2)", "(effects.1.1, effects.1.2 ++ effects.2)"),
        ("changed-observed-input", 0, "mapConstructors (fun observe before => observe (erase before)) observations",
         "mapConstructors (fun observe before => observe { erase before with graph := { before.graph with allocationCursor := 0 } }) observations"),
        ("wrong-dispatch-opcode", 1, "debug key slice before).2 =", "debug { key with instruction := 0 } slice before).2 ="),
        ("recounts-earlier-history", 1,
         "ChildTrace.history (MissStream.selected p request key slice deterministic (ChildTrace.restore [] (ChildTrace.erase before))).2",
         "ChildTrace.history (MissStream.selected p request key slice deterministic before).2"),
        ("loses-entry-offset", 1, "= start + events.length := by", "= events.length := by"),
        ("counts-entry-history", 1, "= start + events.length := by", "= start + (ChildTrace.history before).length + events.length := by"),
        ("observes-wrong-depth", 2,
         "(ChildTrace.liftObservationsMutation (observe (unfold ops allocate safety owner meaning base growth usizeBits depth)))",
         "(ChildTrace.liftObservationsMutation (observe (unfold ops allocate safety owner meaning base growth usizeBits (depth + 1))))"),
    ):
        if parts[index].count(before) != 1:
            raise ValueError("ambiguous child history mutation: " + name)
        changed = parts.copy()
        changed[index] = changed[index].replace(before, after)
        variants.append((name, program(changed)))
    records = native.check_controls(output, env, lean, program(parts), variants, prefix="child-history-")
    for record in records:
        if not record["expectedAcceptance"] and not re.search(
                r"error: (?:Not a definitional equality|Application type mismatch|Type mismatch|Tactic[^\n]*failed|unsolved goals)",
                (output / (record["name"] + ".stdout")).read_text()):
            raise ValueError("child history control lacks a semantic proof failure: " + record["name"])
    return records
