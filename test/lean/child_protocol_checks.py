"""Child protocol recording checks consumed by the native scoped gate.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import json
import re

import check_native_resource_trace as native
from check_zig_air_memory_proofs import without_imports

NS = native.OWNED + "ConstructorItem.NativeRecursion.ChildTrace."
MISS = native.OWNED + "MissStream."
CLAIMS = [NS + name for name in (
    "erase_restore", "restore_history", "record_erases", "record_prefix", "constructors_erase",
    "constructors_prefix", "action_segment", "dispatcher_segment")]
CLAIMS += [MISS + name for name in ("child_boundaries", "initialized_recorded_children")]
CLAIMS += [NS + "Tests." + name for name in (
    "recorded_cache_family", "native_dispatch_child", "guarded_boundaries", "sequence_prefix", "successful_order", "failed_order")]


def dependencies(output):
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    required = {
        NS + "record_erases": {NS + "record", NS + "erase", NS + "restore"},
        NS + "record_prefix": {NS + "record", NS + "prepend"},
        NS + "constructors_erase": {NS + "record_erases", NS + "constructors", native.OWNED + "Recursive.erasing"},
        NS + "constructors_prefix": {NS + "record_prefix", NS + "constructors"},
        NS + "action_segment": {NS + "restore_history", NS + "history", NS + "restore"},
        NS + "dispatcher_segment": {NS + name for name in ("constructors_erase", "constructors_prefix", "action_segment")}
            | {native.OWNED + "ConstructorItem.NativeRecursion.dispatcher_erases"},
        MISS + "child_boundaries": {NS + "action_segment", NS + "constructors_prefix", MISS + "selected", MISS + "childCursor",
            native.OWNED + "ConstructorItem.NativeRecursion.dispatcher_erases"},
        MISS + "initialized_recorded_children": {MISS + "initialized_from_children", MISS + "child_boundaries",
            NS + "constructors", NS + "history", MISS + "childCursor"},
        NS + "Tests.recorded_cache_family": {native.OWNED + "Caller.CacheStream.Tests.existing_family", NS + "record", NS + "erase_restore"},
        NS + "Tests.native_dispatch_child": {NS + "Tests.dispatch", NS + "constructors", NS + "record"},
        NS + "Tests.guarded_boundaries": {MISS + "child_boundaries", NS + "Tests.native_dispatch_child"},
        NS + "Tests.sequence_prefix": {NS + "constructors_prefix", "Compiler.Extraction.Dispatch.maxExponent"},
        NS + "Tests.successful_order": {NS + "Tests.sequence", NS + "Tests.child", NS + "Tests.observations"},
        NS + "Tests.failed_order": {NS + "Tests.sequence_prefix", NS + "Tests.sequence", NS + "Tests.child"},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError("child protocol lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return sorted(required)


def controls(output, env, lean):
    directory = native.ROOT / "lean/Compiler/Extraction"
    parts = [without_imports((directory / (name + ".lean")).read_text()).replace("ChildTrace", "ChildTraceMutation")
        for name in ("InternerInvocationChildTrace", "InternerMissChildTrace", "InternerInvocationChildTraceTests")]
    for index in range(len(parts)):
        for name in ("ProtocolEvent", "childCursor", "child_boundaries", "initialized_recorded_children"):
            parts[index] = re.sub(r"\b" + name + r"\b", name + "Mutation", parts[index])

    def program(parts):
        return "import Compiler.Extraction.InternerInvocationChildTraceTests\n" + "\n".join(parts)

    variants = []
    for name, index, before, after, count in (
        ("rewound-native-state", 0, "observe (erase before)) actual.2)", "observe (erase before)) (erase before))", 1),
        ("changed-native-result", 0, "(actual.1, restore", "(.error (.language .unsupported), restore", 1),
        ("lost-history", 0, "history before ++ observe (erase before)", "observe (erase before)", 1),
        ("reordered-history", 0, "history before ++ observe (erase before)", "observe (erase before) ++ history before", 1),
        ("observed-reached-input", 0, "history before ++ observe (erase before)", "history before ++ observe actual.2", 1),
        ("lost-child-observation", 0, "history before ++ observe (erase before)", "history before", 1),
        ("wrong-child-opcode", 0, "record (children.operation opcode values debug)", "record (children.operation 0 values debug)", 1),
        ("wrong-borrowed-address", 0, "record (children.borrowedOperation address opcode values debug)",
         "record (children.borrowedOperation 0 opcode values debug)", 1),
        ("wrong-local-selection", 0, "record (children.localOperation opcode source selected repeated first debug)",
         "record (children.localOperation opcode source 0 repeated first debug)", 1),
        ("unbound-child-erasure", 0, "(constructors children observations) children :=",
         "(constructors children observations) exhausted :=", 1),
        ("lost-entry-offset", 1,
         "start + (ChildTraceMutation.history world).length - (ChildTraceMutation.history before).length",
         "(ChildTraceMutation.history world).length - (ChildTraceMutation.history before).length", 1),
        ("counts-earlier-history", 1,
         "start + (ChildTraceMutation.history world).length - (ChildTraceMutation.history before).length",
         "start + (ChildTraceMutation.history world).length", 1),
        ("lost-exit-segment", 1, "= start + (ChildTraceMutation.history captured.2).length", "= start", 1),
        ("empty-middle", 1,
         "let middle := ChildTraceMutation.history (selected p request key slice deterministic (ChildTraceMutation.restore [] (ChildTraceMutation.erase called.world))).2",
         "let middle : List ProtocolEventMutation := []", 1),
        ("stale-cursor-origin", 1, "let cursor := childCursorMutation missLeading.length called.world",
         "let cursor := childCursorMutation missLeading.length before", 1),
        ("unrelated-children", 1, ")).SourceConstructorsAt (Nested.storageReads rows) debug traced model) →", ")).SourceConstructorsAt (Nested.storageReads rows) debug exhausted model) →", 1),
        ("reversed-middle", 1, "ChildTraceMutation.history decision.2 = ChildTraceMutation.history called.world ++ middle",
         "ChildTraceMutation.history decision.2 = middle ++ ChildTraceMutation.history called.world", 1),
        ("semantic-projection", 1, "(ordinary decision.1 = true →", "(ordinary decision.1 = false →", 1),
    ):
        if parts[index].count(before) != count:
            raise ValueError("ambiguous child protocol mutation: " + name)
        changed = parts.copy()
        changed[index] = changed[index].replace(before, after)
        variants.append((name, program(changed)))
    records = native.check_controls(output, env, lean, program(parts), variants, prefix="child-protocol-")
    for record in records:
        if not record["expectedAcceptance"] and not re.search(
                r"error: (?:Not a definitional equality|Application type mismatch|Type mismatch|Tactic[^\n]*failed|unsolved goals)",
                (output / (record["name"] + ".stdout")).read_text()):
            raise ValueError("child protocol control lacks a semantic proof failure: " + record["name"])
    return records
