#!/usr/bin/env python3
"""Checked invocation-local physical replay into recursive normalization resources.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import json
import re

from check_argument_memory import ROOT, NS
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

MODULE = "Compiler.Extraction.NormalizationTraceTests"
OWNERSHIP = "Compiler.Extraction.Cache.NormalizationOwnership."
TRACE = OWNERSHIP + "Trace."
BRIDGE = NS + "Normalization.ResourceAdapter.TraceBridge."
FILES = ["NormalizationPreparedTransport.lean"] + ["NormalizationTrace" + suffix + ".lean" for suffix in (
    "", "Replay", "Init", "Run", "Scope", "Memory", "Production", "Tests")]
CLAIMS = [OWNERSHIP + name for name in (
    "init_transport", "take_transport", "deinit_transport", "finish_transport", "continue_transport", "run_prepared_transport")]
CLAIMS += [TRACE + name for name in (
    "record_transport", "prefix_transport", "record_erases", "rejected_absorbs", "replay_prefix", "move_owned",
    "continue_replay", "continue_record_prefix", "continue_replay_prefix", "prepared_replay", "init_replay", "init_replay_at", "run_replay",
    "Scope.close_items", "Scope.continue_items", "Scope.run_contents", "Scope.observe_transferred",
    "Scope.continue_projection", "Scope.init_projection", "Scope.run_projection", "Scope.admit_sound", "Scope.checked_init_sound", "Scope.checked_success", "Scope.checked_sound")]
CLAIMS += [BRIDGE + name for name in (
    "capture_erases", "capture_native", "capture_replays", "capture_replays_at", "check_physical_sound", "checked_scope", "observe_ordinary", "observe_transfer", "production_verified")]
CLAIMS += [BRIDGE + "Tests." + name for name in (
    "temporary_events", "scratch_events", "borrowed_no_events", "scratch_accepted", "scratch_scope_transfer", "embedded_replay",
    "invalid_entry_rejected", "empty_duplicate_skips_native_allocation", "missing_event_rejected", "reordered_event_rejected", "wrong_allocation_site_rejected", "wrong_owner_rejected", "wrong_release_rejected",
    "preparation_fault_rejected", "physical_suspension_rejected", "temporary_oom_accepted", "ordinary_oom_accepted",
    "partial_copy_rejected", "binary_represented", "production_add")]


def audit(output):
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    required = {
        TRACE + "record_erases": {OWNERSHIP + "run_prepared_transport", OWNERSHIP + "Code.runPrepared", TRACE + "record"},
        TRACE + "run_replay": {TRACE + n for n in ("record", "replay", "continue_replay", "init_replay")},
        TRACE + "Scope.checked_sound": {TRACE + "Scope.run_projection", TRACE + "Scope.checked"}
            | {"Compiler.Extraction.Interner.Scoped." + n for n in ("initScope", "take", "close")},
        BRIDGE + "checked_scope": {BRIDGE + n for n in ("captured", "checked", "capture_replays_at")}
            | {TRACE + "Scope.checked_sound", TRACE + "replay_prefix"},
        BRIDGE + "capture_native": {BRIDGE + "capture_erases", NS + "Normalization.ResourceAdapter.run_eq"},
        BRIDGE + "production_verified": {BRIDGE + n for n in ("checked_scope", "capture_native", "observe_ordinary")}
            | {TRACE + "Scope.run_contents", TRACE + "Scope.observe_transferred", BRIDGE + "observe_transfer"}
            | {NS + "Normalization." + n for n in ("production_verified", "Post", "Admitted", "normalized_projection")},
        BRIDGE + "Tests.production_add": {BRIDGE + "production_verified", BRIDGE + "Tests.scratch_accepted",
            NS + "Normalization.Tests.external_admitted", NS + "Normalization.Tests.actual_caller_allocation"},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError("normalization trace bridge lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return {"checkedDependencies": sorted(required), "obligation": "normalization.recursiveBridge",
            "localPhysicalScopeReplayVerified": True, "recursiveMemoryBridgeVerified": False,
            "boundary": "Exact physical invocation transcript to Scoped.initScope/take/close, with prefix/suffix positions and explicit semantic rejection; intervening graph operations and complete recursive execution remain open."}


def controls(output, env, lean):
    imports = "import Compiler.Extraction.NormalizationResourcesTests\nimport Compiler.Extraction.InternerPreparationTests\n"
    source = "\n".join(without_imports((ROOT / "lean/Compiler/Extraction" / name).read_text()) for name in FILES)
    records = [mutation_check(output, "normalization-trace-unchanged", imports + source, True, env, lean)]
    for name, before, after, count in (
        ("lost-preparation-event", "before.events ++ [.prepare lookup result]", "before.events", 1),
        ("lost-allocator-effects", "(result, ⟨after, before.events ++ [.allocate site result]⟩)", "(result, ⟨before.effects, before.events ++ [.allocate site result]⟩)", 1),
        ("oom-recorded-as-success", "before.events ++ [.allocate site result]", "before.events ++ [.allocate site true]", 1),
        ("lost-release-event", "before.events ++ [.release lookup]", "before.events", 1),
        ("wrong-allocation-site-admitted", "if expected = site then", "if true then", 1),
        ("wrong-owner-admitted", "if expected = lookup then", "if true then", 2),
        ("cursor-not-advanced", "then (result, cursor + 1)", "then (result, cursor)", 2),
        ("mismatch-cursor-accepted", "def rejected (events : List (Event ε)) : Nat := events.length + 1",
         "def rejected (events : List (Event ε)) : Nat := events.length", 1),
        ("mismatch-guard-omitted", "if events.length < cursor then .error (.mismatch cursor)", "if false then .error (.mismatch cursor)", 1),
        ("preparation-fault-projected", "| .error (reason, lookup) => .error (.preparation reason lookup cursor)",
         "| .error _ => .ok projection", 1),
        ("physical-rejection-ignored", "match after.rejected with", "match (none : Option ResourceAdapter.Rejection) with", 1),
        ("handoff-omitted", "if exit = .transfer then (Interner.Scoped.handoff after).2 else after", "after", 1),
        ("wrong-scope-contents", "sort := sortIds", "sort := fun _ => []", 1),
    ):
        if source.count(before) != count:
            raise ValueError("ambiguous normalization trace mutation: " + name + ": " + str(source.count(before)))
        records.append(mutation_check(output, "normalization-trace-" + name, imports + source.replace(before, after), False, env, lean))
    for record in records:
        diagnostic = (output / (record["name"] + ".stdout")).read_text()
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant", diagnostic, re.I):
            raise ValueError("normalization trace control hit a resource or syntax failure: " + record["name"])
        if not record["expectedAcceptance"] and not re.search(
                r"error: (?:unsolved goals|Application type mismatch|Type mismatch|Tactic[^\n]*failed)", diagnostic):
            raise ValueError("normalization trace control lacks a semantic proof failure: " + record["name"])
        if record["name"] == "normalization-trace-wrong-scope-contents":
            # Require the composed theorem to notice wrong contents, even if
            # concrete fixtures or the ownership projection fail earlier too.
            complete = imports + source
            start = complete.index("\ntheorem production_verified")
            end = complete.index("\nend Compiler.Extraction.Memory.Arguments.Normalization.ResourceAdapter.TraceBridge", start)
            first, last = complete[:start].count("\n") + 2, complete[:end].count("\n") + 1
            errors = [int(n) for n in re.findall(r"^<stdin>:(\d+):\d+: error:", diagnostic, re.M)]
            if not any(first <= line <= last for line in errors):
                raise ValueError("wrong scope contents did not break the composed production theorem")
    return records
