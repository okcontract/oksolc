#!/usr/bin/env python3
"""Check live normalization scope coupling through the actual native caller.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import json
import re
from pathlib import Path

import check_live_normalization as live
from check_zig_air_memory_proofs import without_imports

native = live.native
NS = live.NS
MODULE = "Compiler.Extraction.InternerCallerInitializationScopeTests"
CLAIMS = live.CLAIMS + [NS + name for name in ("capture_replays_at", "checked_scope", "capture_ordinary", "checked_ordinary",
    "coupled", "production_verified", "production_ordinary")]
CLAIMS += [NS + "ScopeTests." + name for name in (
    "temporary_accepted", "scratch_cursor", "borrowed_no_events", "ordinary_oom", "invalid_rejected",
    "incomplete_rejected", "partial_copy_rejected", "unbound_start_rejected", "missing_event_rejected",
    "wrong_owner_rejected", "native_accepted", "native_refused", "production_add", "production_oom")]


def dependencies(output):
    checked = live.dependencies(output)
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    trace = live.scope.trace
    required = {
        trace.TRACE + "Scope.run_projection": {trace.TRACE + "Scope.init_projection"},
        trace.TRACE + "Scope.checked_sound": {trace.TRACE + "Scope.admit_sound"},
        trace.BRIDGE + "checked_scope": {trace.BRIDGE + "check_physical_sound"},
        NS + "capture_replays_at": {trace.TRACE + "init_replay_at", trace.OWNERSHIP + "init_prepared_transport"},
        NS + "checked_scope": {NS + "capture_replays_at", trace.TRACE + "Scope.checked_init_sound", trace.TRACE + "Scope.init_projection",
            trace.BRIDGE + "check_physical_sound", native.NS + "normalized_projection"},
        NS + "coupled": {NS + "checked_scope", NS + "capture_spec", NS + "caller", native.NS + "init_refines",
            "Compiler.Extraction.InsertionSort.normalize_word", NS + "Coupled"},
        NS + "production_verified": {NS + "coupled", native.NS + "caller_buffer"},
        NS + "capture_ordinary": {NS + "capture", native.NS + "prepare", native.NS + "ResourceAdapter.failed", native.OWNED + "ordinary"},
        NS + "checked_ordinary": {NS + "capture_ordinary", NS + "capture_replays_at", trace.TRACE + "Scope.admit", trace.BRIDGE + "checkPhysical"},
        NS + "production_ordinary": {NS + "checked_ordinary", NS + "production_verified"},
        NS + "ScopeTests.production_add": {NS + "production_ordinary", NS + "ScopeTests.native_accepted", native.NS + "Tests.actual_caller_allocation"},
        NS + "ScopeTests.production_oom": {NS + "production_ordinary", NS + "ScopeTests.native_refused", native.NS + "Tests.external_admitted"},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError("live scope lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return list(dict.fromkeys(checked + sorted(required)))


def source_parts():
    directory = native.ROOT / "lean/Compiler/Extraction"
    return [without_imports((directory / (name + ".lean")).read_text()).replace("Caller.Initialization", "Caller.InitializationScopeMutation")
        for name in ("InternerCallerInitialization", "InternerCallerInitializationScope", "InternerCallerInitializationAdmission", "InternerCallerInitializationVerified",
                     "InternerCallerInitializationScopeTests")]


def controls(output, env, lean):
    records = live.controls(output, env, lean)
    parts = source_parts()
    def program(parts):
        return "import " + MODULE + "\n" + "\n".join(parts)
    variants = []
    for name, index, before, after, count in (
        ("physical-rejection-bypassed", 1, "TraceBridge.checkPhysical execution.2.effects",
         "TraceBridge.checkPhysical { execution.2.effects with rejected := none }", 1),
        ("unbound-start", 1, "(start : graph.allocationCursor = leading.length)", "(start : True)", 1),
        ("unmatched-length", 1, "(length : request.arguments.length = source.length)", "(length : True)", 1),
        ("unaccepted-prefix", 1, "leading suffix request graph = .ok scope)", "leading suffix request graph = .ok scope ∨ True)", 1),
        ("lost-protocol-cursor", 1, "leading.length + execution.2.events.length", "leading.length", 2),
        ("rewound-caller-memory", 3, "called.2.world.memory = reached", "called.2.world.memory = before.memory", 1),
        ("closed-caller-handle", 3, "called.2.scope.lookup = some handle", "called.2.scope.lookup = none", 1),
        ("advanced-native-cursor", 3, "called.2.world.graph = before.graph", "called.2.world.graph = { before.graph with allocationCursor := cursor }", 1),
        ("wrong-word", 3, "read values sequence =", "read [] sequence =", 1),
        ("fixed-ordinary-failure", 3, "called.1 = scope.1.mapError Fault.language", "called.1 = .error (.language .outOfMemory)", 1),
        ("unbound-stack-producer", 3, "(allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))", "(allocated : True)", 2),
        ("admission-semantic-native-result", 2,
         "(completed : ordinary ((Normalization.init normalizationOwnershipCode external budget allocator commutative\n      source buffer values before).1.mapError memoryFault) = true)",
         "(completed : True)", 1),
        ("admission-semantic-caller-result", 2,
         "(completed : ordinary (Caller.initLookup external budget allocator source buffer request\n      ⟨before, { lookup := none }⟩).1 = true)",
         "(completed : True)", 1),
        ("admission-unmatched-length", 2, "(length : request.arguments.length = source.length)", "(length : True)", 1),
        ("admission-unbound-buffer", 2, "(bufferLength : buffer.length = 2)", "(bufferLength : True)", 1),
        ("admission-unbound-decision", 2, "(decoded : Interner.Scoped.commutative request.item = .ok commutative)", "(decoded : True)", 1),
        ("admission-unbound-start", 2, "(start : graph.allocationCursor = leading.length)", "(start : True)", 1),
        ("admission-oom-is-success", 2, "execution.2.effects.rejected = none ∧ ∃ lookup, execution.1 = .ok lookup",
         "execution.2.effects.rejected = none ∧ ∃ lookup, execution.1 = .ok (some lookup)", 1),
        ("production-unbound-outcome", 3,
         "(completed : ordinary (Caller.initLookup external budget allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request\n      ⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩).1 = true)",
         "(completed : True)", 1),
    ):
        if parts[index].count(before) != count:
            raise ValueError("ambiguous live scope mutation: " + name)
        changed = parts.copy()
        changed[index] = changed[index].replace(before, after)
        variants.append((name, program(changed)))
    added = native.check_controls(output, env, lean, program(parts), variants, prefix="live-scope-")
    for record in added:
        if not record["expectedAcceptance"] and not re.search(
                r"error: (?:Not a definitional equality|Application type mismatch|Type mismatch|Tactic[^\n]*failed|unsolved goals)",
                (output / (record["name"] + ".stdout")).read_text()):
            raise ValueError("live scope control lacks a semantic proof failure: " + record["name"])
    return records + added


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--preflight", action="store_true")
    native.check(parser.parse_args(), module=MODULE, claims=CLAIMS, dependency_check=dependencies,
        control_check=controls, normalization_scope=True, live_initialization=True, live_scope=True)
