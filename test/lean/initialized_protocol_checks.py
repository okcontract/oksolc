"""Actual initialization/take composition into the recorded native caller.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import json
import re

import check_native_resource_trace as native
from check_zig_air_memory_proofs import without_imports

NS = native.OWNED + "Caller.ProtocolTrace."
CLAIMS = [NS + name for name in ("initialized_taken_recorded", "findBody_after_take", "scoped_after_take", "findBody_taken", "scoped_taken",
    "Native.initialized_miss_traced", "TakenTests.spare_prefix", "TakenTests.nondeterministic_spare")]


def dependencies(output):
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    required = {
        NS + "initialized_taken_recorded": {native.OWNED + "Caller.Take.initialized_taken_stream",
            NS + "initialized_recorded", NS + "record", NS + "scopeView"},
        NS + "findBody_after_take": {NS + "findBody", NS + "missBody", "Compiler.Extraction.Interner.FindCode.controlRun"},
        NS + "findBody_taken": {NS + "findBody_after_take"},
        NS + "scoped_after_take": {"Compiler.Extraction.Interner.Scoped.findDetailed", "Compiler.Extraction.Interner.FindCode.controlRun"},
        NS + "scoped_taken": {NS + "scoped_after_take"},
        NS + "Native.initialized_miss_traced": {NS + "initialized_taken_recorded", NS + "findBody_taken", NS + "scoped_taken",
            NS + "find_projected", NS + "MissContinuation", NS + "Native.miss_traced_verified", NS + "Native.MissProjected", native.OWNED + "key_arguments"},
        NS + "TakenTests.spare_prefix": {NS + "initialized_taken_recorded", NS + "findBody_taken",
            native.OWNED + "Publication.GraphTests.prefix_results", native.OWNED + "Insertion.Native.CallerFirstSuccessTests.native_borrow_good"},
        NS + "TakenTests.nondeterministic_spare": {NS + "TakenTests.spare_prefix", NS + "findBody", NS + "missBody"},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError("initialized caller lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return sorted(required)


def controls(output, env, lean):
    directory = native.ROOT / "lean/Compiler/Extraction"
    parts = [without_imports((directory / (name + ".lean")).read_text()) for name in (
        "InternerCallerTakenStream", "InternerCallerProtocolTaken", "InternerCallerProtocolInitializedMiss", "InternerCallerProtocolTakenTests")]
    for index in range(len(parts)):
        for name in ("initialized_taken_stream", "initialized_taken_recorded", "findBody_after_take", "scoped_after_take", "findBody_taken", "scoped_taken",
                     "initialized_miss_traced", "TakenTests"):
            parts[index] = re.sub(r"\b" + name + r"\b", name + "Mutation", parts[index])

    def program(sources):
        return "import Compiler.Extraction.InternerCallerProtocolTakenTests\n" + "\n".join(sources)

    variants = []
    for name, index, before, after in (
        ("normalization-loses-values", 0, "initialScope.1 = .ok values ∧ taken.1.1 = true ∧",
         "initialScope.1 = .ok [] ∧ taken.1.1 = true ∧"),
        ("successful-take-reported-refused", 0, "initialScope.1 = .ok values ∧ taken.1.1 = true ∧",
         "initialScope.1 = .ok values ∧ taken.1.1 = false ∧"),
        ("drops-initialization-history", 1,
         "let missLeading := leading ++ init.2.events.map Event.normalization ++ taken.2.events.map Event.normalization",
         "let missLeading := leading ++ taken.2.events.map Event.normalization"),
        ("drops-take-history", 1,
         "let missLeading := leading ++ init.2.events.map Event.normalization ++ taken.2.events.map Event.normalization",
         "let missLeading := leading ++ init.2.events.map Event.normalization"),
        ("retains-pre-take-token", 1, "{ lookup := some taken.1.2, items := remaining.values, phase := .cleanup }",
         "{ lookup := some lookup, items := remaining.values, phase := .cleanup }"),
        ("premature-handoff", 1, "{ lookup := some taken.1.2, items := remaining.values, phase := .cleanup }",
         "{ lookup := some taken.1.2, items := remaining.values, phase := .transfer }"),
        ("miss-uses-pre-take-state", 1,
         "missBody external budget allocator p q observations source buffer request key deterministic called := by",
         "missBody external budget allocator p q observations source buffer request key deterministic prepared := by"),
        ("flips-source-guard", 1,
         "missBody external budget allocator p q observations source buffer request key deterministic called := by",
         "missBody external budget allocator p q observations source buffer request key (!deterministic) called := by"),
        ("scoped-return-skips-close", 1,
         "Interner.Scoped.findDetailed r model request before = (miss.1, Interner.Scoped.close r miss.2) := by",
         "Interner.Scoped.findDetailed r model request before = (miss.1, miss.2) := by"),
        ("full-caller-forgets-entry-offset", 2,
         "let logical := Interner.Scoped.findDetailed r logicalModel request { before.graph with allocationCursor := leading.length }",
         "let logical := Interner.Scoped.findDetailed r logicalModel request { before.graph with allocationCursor := 0 }"),
        ("full-caller-loses-child-events", 2,
         "actual.2.events = missLeading ++ middle ++ observed.body ++ observed.cleanup ∧",
         "actual.2.events = missLeading ++ observed.body ++ observed.cleanup ∧"),
        ("full-caller-loses-cleanup-events", 2,
         "actual.2.events = missLeading ++ middle ++ observed.body ++ observed.cleanup ∧",
         "actual.2.events = missLeading ++ middle ++ observed.body ∧"),
    ):
        if parts[index].count(before) != 1:
            raise ValueError("ambiguous initialized caller mutation: " + name)
        changed = parts.copy()
        changed[index] = changed[index].replace(before, after)
        variants.append((name, program(changed)))
    records = native.check_controls(output, env, lean, program(parts), variants, prefix="initialized-protocol-")
    for record in records:
        if not record["expectedAcceptance"] and not re.search(
                r"error: (?:Not a definitional equality|Application type mismatch|Type mismatch|Tactic[^\n]*failed|unsolved goals)",
                (output / (record["name"] + ".stdout")).read_text()):
            raise ValueError("initialized caller control lacks a semantic proof failure: " + record["name"])
    return records
