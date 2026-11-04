"""Recorded native miss composition checks for the scoped gate.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import json
import re

import check_native_resource_trace as native
from check_zig_air_memory_proofs import without_imports

NS = native.OWNED + "Caller.ProtocolTrace."
MISS = native.OWNED + "MissStream."
CLAIMS = [NS + name for name in (
    "missBody_erases", "miss_routed", "Native.miss_recorded", "Native.miss_cleanup_segment",
    "finish_projected", "Native.miss_verified", "MissTests.spare_middle", "MissTests.spare_verified")]


def dependencies(output):
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    required = {
        NS + "missBody_erases": {NS + "missBody", NS + "record_erases"},
        NS + "miss_routed": {NS + "missBody", MISS + "selected", NS + "record"},
        NS + "Native.miss_recorded": {NS + "miss_routed", MISS + "routed", MISS + "tail_inputs",
            NS + "Native.insertion_events", NS + "Native.publication_events", native.OWNED + "Publication.admit_complete"},
        NS + "Native.miss_cleanup_segment": {MISS + "routed", MISS + "segment", native.OWNED + "Caller.Close.transferred_stream"},
        NS + "finish_projected": {NS + "close_from_cleanup", native.OWNED + "Caller.Close.taken_spec", NS + "finish"},
        NS + "Native.miss_verified": {NS + "Native.miss_recorded", NS + "Native.miss_cleanup_segment", NS + "finish_projected",
            MISS + "selected_preserved", MISS + "scoped_from_children", NS + "scopeView"},
        NS + "MissTests.spare_middle": {NS + "Native.middle", native.OWNED + "Insertion.Native.NativeSpareTests.reached_frame"},
        NS + "MissTests.spare_verified": {NS + "Native.miss_verified", NS + "MissTests.spare_middle",
            native.OWNED + "ConstructorItem.NativeRecursion.ScopeTests.outcome_children"},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError("recorded miss lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return sorted(required)


def controls(output, env, lean):
    directory = native.ROOT / "lean/Compiler/Extraction"
    parts = [without_imports((directory / (name + ".lean")).read_text()).replace(
        "Caller.ProtocolTrace", "Caller.ProtocolTrace.MissMutation") for name in (
        "InternerCallerProtocolMiss", "InternerCallerProtocolMissReplay", "InternerCallerProtocolMissTests")]

    def program(sources):
        return ("import Compiler.Extraction.InternerCallerProtocolMissTests\nopen " + NS + "Native\n" + "\n".join(sources))

    variants = []
    for name, index, before, after in (
        ("wrong-source-guard", 0,
         "(execution external budget allocator p q observations source buffer) request key deterministic",
         "(execution external budget allocator p q observations source buffer) request key false"),
        ("lost-child-history", 0,
         "before.events ++ middle⟩", "before.events⟩"),
        ("wrong-body-phase", 0,
         "phase := observed.phase },", "phase := .cleanup },"),
        ("lost-body-history", 0,
         "request key slice deterministic before ++ observed.body⟩)", "request key slice deterministic before⟩)"),
        ("wrong-cleanup-segment", 0,
         "observed.cleanup := by", "[] := by"),
        ("changed-original-result", 1,
         "= (result, projected) ∧", "= (.error (.language .outOfMemory), projected) ∧"),
        ("lost-close-history", 1,
         "actual.2.events = leading ++ captured.2.events.map Event.normalization", "actual.2.events = leading"),
        ("dropped-miss-cleanup", 1,
         "actual.2.events = leading ++ middle ++ observed.body ++ observed.cleanup", "actual.2.events = leading ++ middle ++ observed.body"),
    ):
        if parts[index].count(before) != 1:
            raise ValueError("ambiguous recorded miss mutation: " + name)
        changed = parts.copy()
        changed[index] = changed[index].replace(before, after)
        variants.append((name, program(changed)))
    records = native.check_controls(output, env, lean, program(parts), variants, prefix="miss-protocol-")
    for record in records:
        if not record["expectedAcceptance"] and not re.search(
                r"error: (?:Not a definitional equality|Application type mismatch|Type mismatch|Tactic[^\n]*failed|unsolved goals)",
                (output / (record["name"] + ".stdout")).read_text()):
            raise ValueError("recorded miss control lacks a semantic proof failure: " + record["name"])
    return records
