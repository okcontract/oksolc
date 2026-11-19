#!/usr/bin/env python3
"""Check native host recording against the existing normalization scope proof.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import json
from pathlib import Path

import check_native_resource_trace as native
import trace_normalization_checks as trace
from check_zig_air_memory_proofs import without_imports

MODULE = "Compiler.Extraction.NormalizationHostScopeTests"
NS = trace.BRIDGE + "HostScope."
CLAIMS = trace.CLAIMS + [native.TRACE + name for name in (
    "allocation_observation", "release_observation", "transport", "admitted", "run_erases", "run_prefix")]
CLAIMS += [NS + name for name in ("erases", "production_verified")]
CLAIMS += [NS + "Tests." + name for name in (
    "existing_native_execution", "original_native_execution", "empty_channels", "empty_scope_cursor", "scratch_channels",
    "scratch_accepted", "cleanup_channels", "ordinary_oom_channels", "invalid_response_rejected", "incomplete_rejected",
    "partial_copy_rejected", "production_add")]


def dependencies(output):
    checked = trace.audit(output)["checkedDependencies"]
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    required = {
        NS + "erases": {trace.BRIDGE + "capture_native", native.TRACE + "run_erases", NS + "capture"},
        NS + "production_verified": {trace.BRIDGE + "production_verified", trace.BRIDGE + "capture_native",
            trace.BRIDGE + "checked_scope", native.TRACE + "run_erases", native.TRACE + "admitted"},
        NS + "Tests.existing_native_execution": {trace.BRIDGE + "capture_native", native.TRACE + "Tests.observed"},
        NS + "Tests.original_native_execution": {NS + "erases", native.NS + "run"},
        NS + "Tests.empty_channels": {NS + "capture", native.TRACE + "record", trace.TRACE + "record"},
        NS + "Tests.empty_scope_cursor": {trace.BRIDGE + "checked", trace.TRACE + "Scope.checked"},
        NS + "Tests.invalid_response_rejected": {trace.BRIDGE + "checked", native.TRACE + "Tests.invalid"},
        NS + "Tests.production_add": {NS + "production_verified", NS + "Tests.scratch_accepted", trace.BRIDGE + "Tests.binary_represented"},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError("normalization host scope lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return list(dict.fromkeys(checked + sorted(required)))


def source_parts():
    directory = native.ROOT / "lean/Compiler/Extraction"
    return [without_imports((directory / (name + ".lean")).read_text()).replace("HostScope", "HostScopeMutation")
        for name in ("NormalizationHostScope", "NormalizationHostScopeTests")]


def controls(output, env, lean):
    # Only the affected protocol family and this new connection are mutated.
    # Fresh imported replay checks reused host proofs without rerunning unrelated
    # insertion/append/recursive-entry mutation matrices.
    records = trace.controls(output, env, lean)
    parts = source_parts()
    def program(parts):
        return "import " + MODULE + "\n" + "\n".join(parts)
    variants = []
    for name, before, after, count in (
        ("different-native-budget", "captured (HostTrace.record external) budget allocator", "captured (HostTrace.record external) 0 allocator", 1),
        ("different-native-exit", "captured (HostTrace.record external) budget allocator commutative source buffer values exit before", "captured (HostTrace.record external) budget allocator commutative source buffer values .lookup before", 1),
        ("rewound-native-session", "execution.2.effects.session.mapEffects HostTrace.Recorded.effects) := by", "before.mapEffects HostTrace.Recorded.effects) := by", 1),
        ("native-result-replaced", "(some native.1, native.2) =", "(some (.error .outOfMemory), native.2) =", 1),
        ("host-count-as-protocol-cursor", "leading.length + execution.2.events.length", "leading.length + execution.2.effects.session.effects.events.length", 1),
        ("unmatched-start", "(start : graph.allocationCursor = leading.length)", "(start : True)", 1),
        ("unaccepted-scope", "{ before with memory := memory }) leading suffix request exit graph = .ok scope)", "{ before with memory := memory }) leading suffix request exit graph = .ok scope ∨ True)", 1),
        ("rewound-private-effects", "execution.2.effects.session.mapEffects HostTrace.Recorded.effects) := by", "execution.2.effects.session.mapEffects (fun _ => before.effects.effects)) := by", 1),
    ):
        if parts[0].count(before) != count:
            raise ValueError("ambiguous normalization host scope mutation: " + name)
        changed = parts.copy()
        changed[0] = changed[0].replace(before, after)
        variants.append((name, program(changed)))
    return records + native.check_controls(output, env, lean, program(parts), variants, prefix="normalization-host-scope-")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--preflight", action="store_true")
    native.check(parser.parse_args(), module=MODULE, claims=CLAIMS, dependency_check=dependencies,
        control_check=controls, normalization_scope=True)
