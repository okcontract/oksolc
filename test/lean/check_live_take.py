#!/usr/bin/env python3
"""Check actual live take and its composition with checked initialization.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import json
import re
from pathlib import Path

import check_live_scope as live
from check_zig_air_memory_proofs import without_imports

native = live.native
TRACE = live.live.scope.trace.TRACE
ADAPTER = native.NS + "ResourceAdapter."
NS = native.OWNED + "Caller.Take."
MODULE = "Compiler.Extraction.InternerCallerTakeTests"
CLAIMS = live.CLAIMS + [TRACE + "Scope.checked_init_scope"]
CLAIMS += [live.NS + "successful_stream"]
CLAIMS += [ADAPTER + name for name in ("take_spec", "observe_take_result")]
CLAIMS += [TRACE + name for name in ("take_replay", "take_replay_at")]
CLAIMS += [NS + name for name in ("capture_spec", "recorded_erases", "caller", "capture_replays_at", "checked_scope",
    "capture_clean", "checked_ready", "coupled", "verified", "after_initialization_verified", "after_initialization", "initialized_stream")]
CLAIMS += [NS + "Tests." + name for name in (
    "owned_no_events", "allocated_accepted", "borrowed_duplicate", "empty_protocol_event", "scratch_duplicate",
    "ordinary_oom", "invalid_rejected", "partial_copy_rejected", "unbound_cursor_rejected", "missing_event_rejected",
    "borrowed_ready", "borrowed_admitted", "initializer_handle", "initializer_token", "initializer_result", "initializer_execution",
    "initializer_recorded", "borrowed_initialized", "borrowed_recorded", "scope_position", "coupled_oom", "initialized_add")]


def dependencies(output):
    checked = live.dependencies(output)
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    required = {
        live.NS + "coupled": {TRACE + "Scope.checked_init_scope"},
        TRACE + "Scope.checked_init_scope": {TRACE + "Scope.checked_init_sound", TRACE + "Scope.init_projection"},
        NS + "capture_spec": {ADAPTER + "take_spec", TRACE + "record_transport", live.live.scope.trace.OWNERSHIP + "take_transport"},
        NS + "recorded_erases": {NS + "capture_spec", native.NS + "External.Transport.takeOwned", native.TRACE + "transport"},
        NS + "caller": {NS + "capture_spec", native.OWNED + "take"},
        NS + "capture_replays_at": {TRACE + "take_replay_at", TRACE + "take_replay"},
        NS + "checked_scope": {NS + "capture_replays_at", TRACE + "Scope.admit_sound", live.live.scope.trace.BRIDGE + "check_physical_sound"},
        NS + "coupled": {NS + "checked_scope", NS + "capture_spec", NS + "caller", native.NS + "take_refines", ADAPTER + "observe_take_result", NS + "Coupled"},
        NS + "capture_clean": {NS + "capture", native.NS + "take_refines", ADAPTER + "allocate"},
        NS + "checked_ready": {NS + "capture_clean", NS + "capture_replays_at", TRACE + "Scope.admit", live.live.scope.trace.BRIDGE + "checkPhysical"},
        NS + "verified": {NS + "checked_ready", NS + "coupled"},
        NS + "after_initialization_verified": {NS + "verified", live.NS + "Coupled"},
        NS + "after_initialization": {NS + "after_initialization_verified"},
        live.NS + "successful_stream": {live.NS + "capture_success", live.NS + "production_ordinary", live.NS + "Coupled"},
        NS + "initialized_stream": {live.NS + "successful_stream", live.NS + "capture_success", live.NS + "production_ordinary", live.NS + "checked_scope", NS + "after_initialization_verified"},
        NS + "Tests.initialized_add": {NS + "initialized_stream", NS + "Tests.initializer_execution", NS + "Tests.initializer_recorded", NS + "Tests.allocated_accepted"},
        NS + "Tests.coupled_oom": {NS + "initialized_stream", NS + "Tests.borrowed_initialized", NS + "Tests.borrowed_recorded", NS + "Tests.ordinary_oom"},
        NS + "Tests.borrowed_admitted": {NS + "checked_ready", NS + "Tests.borrowed_ready", native.NS + "Tests.external_admitted"},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError("live take lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return list(dict.fromkeys(checked + sorted(required)))


def source_parts():
    directory = native.ROOT / "lean/Compiler/Extraction"
    parts = [without_imports((directory / (name + ".lean")).read_text()) for name in (
        "NormalizationResourcesTake", "NormalizationTraceTake", "InternerCallerTake", "InternerCallerTakeAdmission", "InternerCallerTakeVerified",
        "InternerCallerTakeInitialization", "InternerCallerTakeStream", "InternerCallerTakeTests")]
    parts[0] = parts[0].replace("Normalization.ResourceAdapter", "Normalization.ResourceAdapter.TakeMutation")
    parts[1] = parts[1].replace("NormalizationOwnership.Trace", "NormalizationOwnership.Trace.TakeMutation")
    for index in range(2, len(parts)):
        parts[index] = parts[index].replace("Caller.Take", "Caller.TakeMutation")
        for name in ("observeTake", "take_spec", "observe_take_result"):
            parts[index] = re.sub(r"\b" + name + r"\b", "ResourceAdapter.TakeMutation." + name, parts[index])
        parts[index] = re.sub(r"\btake_replay_at\b", "NormalizationOwnership.Trace.TakeMutation.take_replay_at", parts[index])
    return parts


def controls(output, env, lean):
    records = live.controls(output, env, lean)
    parts = source_parts()
    def program(parts):
        return "import " + MODULE + "\n" + "\n".join(parts)
    variants = []
    for name, index, before, after, count in (
        ("temporary-still-owned", 0, "owned := none", "owned := after.handle.owned", 1),
        ("semantic-fault-is-oom", 0, "some (.error failure)", "some (.error .outOfMemory)", 1),
        ("wrong-allocator", 2, "primitives external 0 allocator", "primitives external 0 0", 4),
        ("physical-rejection-bypassed", 2, "TraceBridge.checkPhysical execution.2.effects",
         "TraceBridge.checkPhysical { execution.2.effects with rejected := none }", 1),
        ("unbound-start", 2, "(start : graph.allocationCursor = leading.length)", "(start : True)", 1),
        ("rewound-native-memory", 4, "called.2.world.memory = reached", "called.2.world.memory = before.memory", 1),
        ("premature-handoff", 4, "if logical.1 then .cleanup else .lookup", "if logical.1 then .transfer else .lookup", 1),
        ("lost-slice", 4, "called.2.scope = ⟨some remaining, some slice, false⟩", "called.2.scope = ⟨some remaining, none, false⟩", 1),
        ("oom-clears-lookup", 4, "called.2.scope = { lookup := some handle }", "called.2.scope = { lookup := none }", 1),
        ("unadmitted-host", 4, "(admitted : Admitted external)", "(admitted : True)", 2),
        ("unbound-prefix-cursor", 5, "(start : initialScope.2.heap.allocationCursor = leading.length)", "(start : True)", 2),
        ("changed-word", 5, "read request.arguments sequence", "read [] sequence", 2),
        ("unready-admission", 3, "(ready : Ready allocator source original handle before)", "(ready : True)", 2),
        ("unadmitted-duplicate", 3, "(admitted : Admitted external)", "(admitted : True)", 2),
        ("unbound-recorded-cursor", 3, "(start : graph.allocationCursor = leading.length)", "(start : True)", 1),
        ("stream-unbound-stack", 6,
         "(allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))",
         "(allocated : True)", 1),
        ("stream-unbound-initialization", 6,
         "(initialized : Caller.initLookup external budget allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request\n      ⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))",
         "(initialized : (Caller.initLookup external budget allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request\n      ⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩).1 = .ok values)", 1),
        ("stream-stale-take-memory", 6, "let execution := capture external allocator lookup.origin handle prepared.world.memory",
         "let execution := capture external allocator lookup.origin handle before.memory", 1),
        ("stream-wrong-origin", 6, "let execution := capture external allocator lookup.origin handle prepared.world.memory",
         "let execution := capture external allocator .input handle prepared.world.memory", 1),
        ("stream-lost-initialization-events", 6,
         "let resources := Scope.resources (leading ++ (initialization.2.events ++ (execution.2.events ++ suffix)))",
         "let resources := Scope.resources (leading ++ (execution.2.events ++ suffix))", 1),
        ("stream-reordered-events", 6,
         "let resources := Scope.resources (leading ++ (initialization.2.events ++ (execution.2.events ++ suffix)))",
         "let resources := Scope.resources (leading ++ (execution.2.events ++ (initialization.2.events ++ suffix)))", 1),
        ("stream-lost-take-cursor", 6,
         "((leading ++ initialization.2.events).length + execution.2.events.length) execution.2.effects.session execution.1",
         "(leading ++ initialization.2.events).length execution.2.effects.session execution.1", 1),
        ("stream-foreign-handle", 6, "let handle := initialization.2.effects.handle",
         "let handle : Handle := ⟨source, request.arguments, none⟩", 1),
        ("stream-rewound-take-start", 6,
         "checked execution (leading ++ initialization.2.events) suffix lookup values initialScope.2.heap = .ok scope",
         "checked execution leading suffix lookup values initialScope.2.heap = .ok scope", 1),
    ):
        if parts[index].count(before) != count:
            raise ValueError("ambiguous live take mutation: " + name)
        changed = parts.copy()
        changed[index] = changed[index].replace(before, after)
        variants.append((name, program(changed)))
    added = native.check_controls(output, env, lean, program(parts), variants, prefix="live-take-")
    for record in added:
        if not record["expectedAcceptance"] and not re.search(
                r"error: (?:Not a definitional equality|Application type mismatch|Type mismatch|Tactic[^\n]*failed|unsolved goals)",
                (output / (record["name"] + ".stdout")).read_text()):
            raise ValueError("live take control lacks a semantic proof failure: " + record["name"])
    return records + added


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--preflight", action="store_true")
    native.check(parser.parse_args(), module=MODULE, claims=CLAIMS, dependency_check=dependencies,
        control_check=controls, normalization_scope=True, live_initialization=True, live_scope=True, live_take=True)
