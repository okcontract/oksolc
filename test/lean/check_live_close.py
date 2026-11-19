#!/usr/bin/env python3
"""Check reached native cleanup, its scoped trace, and the actual miss consumer.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import json
import re
from pathlib import Path

import check_live_take as live
from check_zig_air_memory_proofs import without_imports

native = live.native
OWNERSHIP = live.live.live.scope.trace.OWNERSHIP
TRACE = live.TRACE
NS = native.OWNED + "Caller.Close."
MODULE = "Compiler.Extraction.InternerCallerCloseTests"
CLAIMS = live.CLAIMS + [OWNERSHIP + "close_transport"]
CLAIMS += [TRACE + name for name in ("close_replay", "close_replay_at", "Scope.close_projection")]
CLAIMS += [NS + name for name in ("lookup_spec", "taken_spec", "observe_success", "capture_replays_at",
    "checked_of_cleanup", "lookup_verified", "taken_verified", "taken_token", "take_success", "after_take", "miss_after_take")]
CLAIMS += [NS + "Tests." + name for name in ("ready_lookup", "owned_lookup", "reached_failure", "handoff_skips_release",
    "separate_host_events", "empty_release", "invalid_release_rejected", "missing_slice_rejected", "wrong_cursor_rejected",
    "missing_event_rejected", "semantic_retains_state", "take_succeeds", "ordinary_miss", "verified_miss", "verified_lookup")]


def dependencies(output):
    checked = live.dependencies(output)
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    required = {
        OWNERSHIP + "close_transport": {OWNERSHIP + "deinit_transport"},
        TRACE + "close_replay": {OWNERSHIP + "Code.closeWith", TRACE + "record", TRACE + "replay"},
        TRACE + "close_replay_at": {TRACE + "close_replay", OWNERSHIP + "close_transport", TRACE + "replay_prefix"},
        TRACE + "Scope.close_projection": {"Compiler.Extraction.Interner.Scoped.close", OWNERSHIP + "Code.closeWith"},
        NS + "lookup_spec": {NS + "capture", NS + "observe", native.OWNED + "cleanup", native.NS + "ResourceAdapter.release"},
        NS + "taken_spec": {NS + "capture", NS + "observe", native.OWNED + "cleanup", native.NS + "ResourceAdapter.outputSlice"},
        NS + "capture_replays_at": {TRACE + "close_replay_at"},
        NS + "checked_of_cleanup": {NS + "observe_success", NS + "capture_replays_at", TRACE + "Scope.close_projection"},
        NS + "lookup_verified": {NS + "lookup_spec", NS + "checked_of_cleanup", native.OWNED + "Caller.cleanup_lookup"},
        NS + "taken_verified": {NS + "taken_spec", NS + "checked_of_cleanup", native.OWNED + "cleanup_taken"},
        NS + "taken_token": {OWNERSHIP + "take_with_success", live.NS + "capture"},
        NS + "take_success": {live.NS + "verified", live.NS + "checked_scope", NS + "taken_token"},
        NS + "after_take": {live.NS + "verified", NS + "taken_token", NS + "taken_verified", native.OWNED + "Post"},
        NS + "miss_after_take": {NS + "after_take", native.OWNED + "miss_post", native.OWNED + "Contracts"},
        NS + "Tests.verified_miss": {NS + "miss_after_take", native.OWNED + "Tests.callbacks_contracts", live.NS + "Tests.borrowed_ready"},
        NS + "Tests.verified_lookup": {NS + "lookup_verified", live.NS + "Tests.borrowed_ready"},
        NS + "Tests.semantic_retains_state": {native.OWNED + "finish_semantic"},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError("live close lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return list(dict.fromkeys(checked + sorted(required)))


def source_parts():
    directory = native.ROOT / "lean/Compiler/Extraction"
    parts = [without_imports((directory / (name + ".lean")).read_text()) for name in (
        "NormalizationClose", "NormalizationTraceClose", "InternerCallerClose", "InternerCallerCloseVerified",
        "InternerCallerCloseTake", "InternerCallerCloseTests")]
    # Keep the imported original interpreter separate from each mutated copy.
    parts = [re.sub(r"\bclose_transport\b", "close_transport_mutation",
             re.sub(r"\bcloseWith\b", "closeWithMutation", part)) for part in parts]
    parts[1] = parts[1].replace("NormalizationOwnership.Trace", "NormalizationOwnership.Trace.CloseMutation")
    parts[1] = re.sub(r"\bresources\b", "Compiler.Extraction.Cache.NormalizationOwnership.Trace.Scope.resources", parts[1])
    for index in range(2, len(parts)):
        parts[index] = parts[index].replace("Caller.Close", "Caller.CloseMutation")
        parts[index] = re.sub(r"\bclose_replay_at\b", "NormalizationOwnership.Trace.CloseMutation.close_replay_at", parts[index])
        parts[index] = parts[index].replace("Scope.close_projection", "NormalizationOwnership.Trace.CloseMutation.Scope.close_projection")
    return parts


def controls(output, env, lean):
    records = live.controls(output, env, lean)
    parts = source_parts()
    def program(parts):
        return "import " + MODULE + "\n" + "\n".join(parts)
    variants = []
    for name, index, before, after, count in (
        ("release-after-handoff", 0, "if phase = .cleanup", "if phase = .transfer", 1),
        ("wrong-token-owner", 0, "lookup.move .caller .released", "lookup.move .lookup .released", 1),
        ("missing-deinit", 0, "code.deinitWith release lookup before", "(lookup, before)", 1),
        ("wrong-allocator", 2, "primitives external 0 allocator", "primitives external 0 0", 1),
        ("missing-current-slice", 2, "before.world.memory, handle, before.scope.slice, none", "before.world.memory, handle, none, none", 1),
        ("rewound-memory", 2, "memory := after.session", "memory := before.world.memory", 1),
        ("release-fault-is-success", 2, "some (.error (memoryFault failure), reached)", "some (.ok (), reached)", 1),
        ("lost-handed-off-descriptor", 2, "if before.scope.handedOff then before.scope.slice else none", "none", 1),
        ("physical-rejection-bypassed", 3, "TraceBridge.checkPhysical execution.2.effects",
         "TraceBridge.checkPhysical { execution.2.effects with rejected := none }", 1),
        ("unbound-cursor", 3, "(start : graph.allocationCursor = leading.length)", "(start : True)", 1),
        ("owned-lookup-after-take", 3, "(detached : handle.owned = none)", "(detached : True)", 1),
        ("dead-caller-slice", 3, "(live : handedOff = false → SliceValid allocator before.memory.heap slice)", "(live : True)", 1),
        ("source-alias", 3, "(separate : original ≠ [] → source.allocation ≠ slice.address)", "(separate : True)", 1),
        ("semantic-exit-cleanup", 4,
         "(completed : ordinary (continuation (OwnedCall.take external allocator ⟨before, { lookup := some handle }⟩).2).1 = true)",
         "(completed : True)", 1),
        ("take-missing-success", 4,
         "(succeeded : (OwnedCall.take external allocator ⟨before, { lookup := some handle }⟩).1 = .ok ()) :",
         "(succeeded : True) :", 1),
        ("take-initial-token", 4,
         "let lookup := (Take.capture external allocator origin handle before.memory).1.2",
         "let lookup := token origin handle", 1),
        ("take-owned-result", 4, "lookup.owned = false ∧ lookup.owner = .caller ∧",
         "lookup.owned = true ∧ lookup.owner = .caller ∧", 1),
        ("take-stale-memory", 4,
         "        Normalization.Taken allocator source original handle before.memory slice remaining called.2.world.memory",
         "        Normalization.Taken allocator source original handle before.memory slice remaining before.memory", 1),
    ):
        if parts[index].count(before) != count:
            raise ValueError("ambiguous live close mutation: " + name)
        changed = parts.copy()
        changed[index] = changed[index].replace(before, after)
        variants.append((name, program(changed)))
    added = native.check_controls(output, env, lean, program(parts), variants, prefix="live-close-")
    for record in added:
        if not record["expectedAcceptance"] and not re.search(
                r"error: (?:Not a definitional equality|Application type mismatch|Type mismatch|Tactic[^\n]*failed|unsolved goals)",
                (output / (record["name"] + ".stdout")).read_text()):
            raise ValueError("live close control lacks a semantic proof failure: " + record["name"])
    return records + added


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--preflight", action="store_true")
    native.check(parser.parse_args(), module=MODULE, claims=CLAIMS, dependency_check=dependencies,
        control_check=controls, normalization_scope=True, live_initialization=True, live_scope=True, live_take=True, live_close=True)
