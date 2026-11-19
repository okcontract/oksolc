#!/usr/bin/env python3
"""Check the shared live normalization prefix through actual caller initialization.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import json
import re
from pathlib import Path

import check_normalization_host_scope as scope
import prepared_normalization_checks as prepared
import resource_normalization_checks as resource
from check_zig_air_memory_proofs import without_imports

native = scope.native
MODULE = "Compiler.Extraction.InternerCallerInitializationTests"
NS = native.OWNED + "Caller.Initialization."
CLAIMS = list(dict.fromkeys(prepared.CLAIMS + resource.CLAIMS + scope.CLAIMS))
CLAIMS += [scope.trace.OWNERSHIP + "init_prepared_transport"]
CLAIMS += [NS + name for name in ("capture_spec", "recorded_erases", "caller", "capture_success")]
CLAIMS += [NS + "Tests." + name for name in (
    "temporary_live", "scratch_live", "borrowed_live", "ordinary_oom", "invalid_response",
    "incomplete_keeps_live_allocation", "partial_copy", "caller_observation", "caller_retains_temporary", "caller_fault_keeps_scope")]


def dependencies(output):
    checked = prepared.audit(output)["checkedDependencies"] + resource.audit(output)["checkedDependencies"] + scope.dependencies(output)
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    required = {
        scope.trace.OWNERSHIP + "run_prepared_transport": {scope.trace.OWNERSHIP + "init_prepared_transport"},
        resource.ADAPTER + "init_spec": {resource.ADAPTER + "prepare_init", resource.ADAPTER + "prepared_token", native.NS + "init"},
        NS + "capture_spec": {scope.trace.OWNERSHIP + "init_prepared_transport", resource.ADAPTER + "init_spec", scope.trace.TRACE + "record_transport"},
        NS + "recorded_erases": {NS + "capture_spec", native.NS + "External.Transport.init", native.TRACE + "transport"},
        NS + "caller": {NS + "capture_spec", native.OWNED + "Caller.initLookup", resource.ADAPTER + "observeInit"},
        NS + "capture_success": {NS + "caller", NS + "capture_spec", resource.ADAPTER + "InitAligned"},
        NS + "Tests.caller_observation": {NS + "caller"},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError("live normalization lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    prepared.source_binding(output)
    return list(dict.fromkeys(checked + sorted(required)))


def source_parts():
    directory = native.ROOT / "lean/Compiler/Extraction"
    return [without_imports((directory / (name + ".lean")).read_text()).replace("Caller.Initialization", "Caller.InitializationMutation")
        for name in ("InternerCallerInitialization", "InternerCallerInitializationTests")]


def controls(output, env, lean):
    records = prepared.controls(output, env, lean) + resource.controls(output, env, lean) + scope.controls(output, env, lean)
    parts = source_parts()
    def program(parts):
        return "import " + MODULE + "\n" + "\n".join(parts)
    variants = []
    for name, before, after, count in (
        ("wrong-budget", "(primitives external budget allocator source buffer values)", "(primitives external 0 allocator source buffer values)", 3),
        ("wrong-allocator", "(primitives external budget allocator source buffer values)", "(primitives external budget 0 source buffer values)", 3),
        ("wrong-commutativity", "normalizationOwnershipCode.initPrepared commutative source.length buffer.length", "normalizationOwnershipCode.initPrepared false source.length buffer.length", 1),
        ("wrong-source", "(primitives external budget allocator source buffer values)", "(primitives external budget allocator buffer buffer values)", 3),
        ("rewound-native-state", "execution.2.effects.session.mapEffects HostTrace.Recorded.effects)", "before.mapEffects HostTrace.Recorded.effects)", 1),
        ("rewound-private-effects", "execution.2.effects.session.mapEffects HostTrace.Recorded.effects)", "execution.2.effects.session.mapEffects (fun _ => before.effects.effects))", 1),
        ("caller-clears-live-handle", "⟨world, { lookup := some handle }⟩", "⟨world, { lookup := none }⟩", 2),
        ("caller-clears-failed-scope", "{ before with world }", "⟨world, { lookup := none }⟩", 2),
        ("caller-rewinds-memory", "memory := execution.2.effects.session", "memory := before.world.memory", 1),
        ("success-unbound-reached-state",
         "(succeeded : Caller.initLookup external budget allocator source buffer request\n      ⟨before, { lookup := none }⟩ = (.ok values, prepared))",
         "(succeeded : (Caller.initLookup external budget allocator source buffer request\n      ⟨before, { lookup := none }⟩).1 = .ok values)", 1),
        ("success-stale-memory", "prepared = ⟨⟨before.graph, execution.2.effects.session⟩,",
         "prepared = ⟨⟨before.graph, before.memory⟩,", 1),
        ("success-original-values", "execution.2.effects.handle.values = values ∧",
         "request.arguments = values ∧", 1),
    ):
        if parts[0].count(before) != count:
            raise ValueError("ambiguous live normalization mutation: " + name)
        changed = parts.copy()
        changed[0] = changed[0].replace(before, after)
        variants.append((name, program(changed)))
    records += native.check_controls(output, env, lean, program(parts), variants, prefix="live-normalization-")
    for record in records:
        if not record["expectedAcceptance"] and not re.search(
                r"error: (?:Not a definitional equality|Application type mismatch|Type mismatch|Tactic[^\n]*failed|Tactic `decide` proved that the proposition|unsolved goals|'change' tactic failed)",
                (output / (record["name"] + ".stdout")).read_text()):
            raise ValueError("live normalization control lacks a semantic proof failure: " + record["name"])
    return records


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--preflight", action="store_true")
    native.check(parser.parse_args(), module=MODULE, claims=CLAIMS, dependency_check=dependencies,
        control_check=controls, normalization_scope=True, live_initialization=True)
