#!/usr/bin/env python3
"""Check native/scoped miss control and cleanup of the actual scoped result.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import json
import re
from pathlib import Path

import check_live_close as live
from check_zig_air_memory_proofs import without_imports

native = live.native
RECURSIVE = native.OWNED + "Recursive."
NS = native.OWNED + "Caller.ScopeProjection."
MODULE = "Compiler.Extraction.InternerCallerScopeProjectionTests"
CLAIMS = live.CLAIMS + [RECURSIVE + "projects_at_bind",
    native.OWNED + "ConstructorItem.NativeRecursion.dispatcher_projects_cursor"]
CLAIMS += [RECURSIVE + "PreservationTests." + name for name in (
    "all_depths_verified", "cursor_bind_projects", "changed_result_rejected", "changed_graph_rejected")]
CLAIMS += [NS + name for name in ("graph", "handoff", "pure", "miss", "closed_miss_after_take")]
CLAIMS += [NS + "Tests." + name for name in ("graph_contracts", "memory_contracts", "initial", "ordinary_native",
    "matched", "failed_publication", "insertion_handoff", "nondeterministic_skips_search", "semantic_retains_state", "verified_closed")]


def dependencies(output):
    checked = live.dependencies(output)
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    required = {
        RECURSIVE + "projects_at_bind": {RECURSIVE + "ProjectsAt", "Compiler.Algebraic.Effect.bind"},
        RECURSIVE + "PreservationTests.cursor_bind_projects": {RECURSIVE + "projects_at_bind"},
        native.OWNED + "ConstructorItem.NativeRecursion.dispatcher_projects_cursor": {
            native.OWNED + "ConstructorItem.NativeRecursion.dispatch_projects_framed_at", RECURSIVE + "cursorGraph"},
        NS + "graph": {RECURSIVE + "ProjectsAt", NS + "Frame", NS + "scopeAt", native.OWNED + "graph", "Compiler.Extraction.Interner.Scoped.liftGraph"},
        NS + "handoff": {native.OWNED + "handoff", "Compiler.Extraction.Interner.Scoped.handoff", NS + "scopeAt"},
        NS + "miss": {RECURSIVE + "projects_at_bind", NS + "graph", NS + "handoff", NS + "pure", NS + "Graphs"},
        NS + "closed_miss_after_take": {NS + "miss", live.NS + "miss_after_take",
            live.TRACE + "Scope.admit_sound", live.live.live.live.scope.trace.BRIDGE + "check_physical_sound"},
        NS + "Tests.graph_contracts": {RECURSIVE + "PreservationTests.counted_projects", NS + "Graphs"},
        NS + "Tests.memory_contracts": {RECURSIVE + "PreservationTests.counted_projects", native.OWNED + "Contracts"},
        NS + "Tests.matched": {NS + "miss", NS + "Tests.graph_contracts", NS + "Tests.initial"},
        NS + "Tests.verified_closed": {NS + "closed_miss_after_take", NS + "Tests.graph_contracts", NS + "Tests.memory_contracts"},
        NS + "Tests.semantic_retains_state": {native.OWNED + "finish_semantic"},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError("scoped miss lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return list(dict.fromkeys(checked + sorted(required)))


def source_parts():
    directory = native.ROOT / "lean/Compiler/Extraction"
    parts = [without_imports((directory / (name + ".lean")).read_text()) for name in (
        "InternerPhysicalDispatchPreservation", "InternerCallerScopeProjection", "InternerCallerScopedClose",
        "InternerCallerScopeProjectionTests")]
    parts[0] = parts[0].replace("OwnedCall.Recursive", "OwnedCall.Recursive.ScopedMutation")
    for index in range(1, len(parts)):
        parts[index] = parts[index].replace("Caller.ScopeProjection", "Caller.ScopeProjectionMutation")
        for name in ("ProjectsAt", "projects_at_bind", "projects_at_bind_from"):
            parts[index] = re.sub(r"\b" + name + r"\b", "Recursive.ScopedMutation." + name, parts[index])
    return parts


def controls(output, env, lean):
    records = live.controls(output, env, lean)
    parts = source_parts()
    def program(parts):
        return "import " + MODULE + "\n" + "\n".join(parts)
    variants = []
    for name, index, before, after, count in (
        ("rewound-graph", 0, "observe (physical before).2 = (logical (observe before)).2",
         "observe before = (logical (observe before)).2", 1),
        ("lost-reached-predicate", 0, "predicate (physical before).2 ∧", "predicate before ∧", 1),
        ("wrong-handoff-phase", 1, "if before.scope.handedOff then .transfer else .cleanup",
         "if before.scope.handedOff then .cleanup else .transfer", 1),
        ("lost-normalized-items", 1, "⟨⟨some lookup, items, if before.scope.handedOff", "⟨⟨some lookup, [], if before.scope.handedOff", 1),
        ("lost-lookup", 1, "⟨⟨some lookup, items, if before.scope.handedOff", "⟨⟨none, items, if before.scope.handedOff", 1),
        ("missing-caller-slice", 1, "before.scope.slice = some slice ∧", "before.scope.slice = none ∧", 1),
        ("wrong-publication-id", 1, "(physical.publish key slice id)", "(physical.publish key slice (id + 1))", 2),
        ("wrong-insert-branch", 1, "(physical.insert key slice deterministic)", "(physical.insert key slice (!deterministic))", 2),
        ("wrong-key", 1, "(model.simplify key)", "(model.simplify { key with arguments := [] })", 1),
        ("unbound-close-cursor", 2,
         "(start : cursor (Interner.findCode.controlMiss (OwnedCall.execution external allocator physical) request key deterministic\n      (OwnedCall.take external allocator ⟨before, { lookup := some handle }⟩).2).2.world = leading.length)",
         "(start : True)", 1),
        ("missing-initial-predicate", 2,
         "(initial : predicate (OwnedCall.take external allocator ⟨before, { lookup := some handle }⟩).2.world)",
         "(initial : True)", 1),
        ("mismatched-key-input", 2, "(aligned : key.arguments = handle.values)", "(aligned : True)", 1),
        ("semantic-exit-projection", 2,
         "(completed : ordinary (Interner.findCode.controlMiss (OwnedCall.execution external allocator physical) request key deterministic\n      (OwnedCall.take external allocator ⟨before, { lookup := some handle }⟩).2).1 = true)",
         "(completed : True)", 1),
    ):
        if parts[index].count(before) != count:
            raise ValueError("ambiguous scoped miss mutation: " + name)
        changed = parts.copy()
        changed[index] = changed[index].replace(before, after)
        variants.append((name, program(changed)))
    added = native.check_controls(output, env, lean, program(parts), variants, prefix="scoped-miss-")
    for record in added:
        if not record["expectedAcceptance"] and not re.search(
                r"error: (?:Not a definitional equality|Application type mismatch|Type mismatch|Tactic[^\n]*failed|unsolved goals)",
                (output / (record["name"] + ".stdout")).read_text()):
            raise ValueError("scoped miss control lacks a semantic proof failure: " + record["name"])
    return records + added


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--preflight", action="store_true")
    native.check(parser.parse_args(), module=MODULE, claims=CLAIMS, dependency_check=dependencies,
        control_check=controls, normalization_scope=True, live_initialization=True, live_scope=True, live_take=True,
        live_close=True, scoped_miss=True)
