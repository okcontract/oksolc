#!/usr/bin/env python3
"""Audit shared argument/publication transport consumed by native entry induction.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import json
from pathlib import Path
import re

import check_insertion_control_erasure as control
from check_zig_air_memory_proofs import without_imports

native = control.native
MODULE = "Compiler.Extraction.InternerInsertionSharedEffectsTests"
INSERT, NS, RECURSION = control.INSERT, control.NS, control.RECURSION
TESTS = NS + "SharedEffectTests."
CLAIMS = control.CLAIMS.copy()
for namespace, names in (
    (INSERT + "SharedEffects.", ["arguments", "publish", "release"]),
    (NS, ["shared_attempt_transport", "shared_release_transport", "pending_transport", "callback_obligations"]),
    (RECURSION, ["unfold_shared_erases"]),
    (TESTS, ["attempts_erase", "releases_erase", "duplicate_success", "duplicate_refusal", "incoming_ownership_rejected",
        "empty_arguments_skip_host", "invalid_allocation_retained", "partial_copy_retained", "duplicate_cleanup",
        "missing_arguments_skips_host", "alias_selects_normalized", "replacement_success", "publication_refusal",
        "release_fault_retains_probe", "admission_skips_probe"]),
):
    CLAIMS += [namespace + name for name in names]


def dependencies(output):
    checked = control.dependencies(output)
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    required = {
        INSERT + "SharedEffects.arguments": {native.NS + "External.Transport.takeOwned", INSERT + "ownsArguments", INSERT + "callbacks"},
        INSERT + "SharedEffects.publish": {native.OWNED + "Publication.EffectTransport.publish", INSERT + "callbacks"},
        INSERT + "SharedEffects.release": {native.NS + "External.Transport.free", INSERT + "arguments", INSERT + "callbacks"},
        NS + "shared_attempt_transport": {INSERT + "SharedEffects.arguments", INSERT + "SharedEffects.publish", NS + "callbacks"},
        NS + "shared_release_transport": {INSERT + "SharedEffects.release", NS + "callbacks"},
        NS + "pending_transport": {NS + "shared_attempt_transport", NS + "shared_release_transport",
            NS + "ResidualTransport.append", NS + "ResidualTransport.release", NS + "PendingTransport.mk"},
        NS + "callback_obligations": {NS + "pending_transport", NS + "ResidualObligations", NS + "CallbackObligations"},
        RECURSION + "unfold_shared_erases": {NS + "callback_obligations", RECURSION + "unfold_native_erases",
            NS + "insert_transport", NS + "callerPrimitives", "Nat.rec"},
        TESTS + "attempts_erase": {NS + "shared_attempt_transport", native.TRACE + "transport",
            native.OWNED + "Publication.Recording.probe_transport"},
        TESTS + "releases_erase": {NS + "shared_release_transport", native.TRACE + "transport"},
        TESTS + "partial_copy_retained": {NS + "callbacks", native.NS + "takeOwned", native.TRACE + "record"},
        TESTS + "release_fault_retains_probe": {NS + "callbacks", native.OWNED + "Publication.publish",
            native.OWNED + "Publication.Recording.recordProbe"},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError("shared insertion erasure lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return list(dict.fromkeys(checked + sorted(required)))


def source_parts():
    directory = native.ROOT / "lean/Compiler/Extraction"
    parts = [without_imports((directory / (name + ".lean")).read_text()) for name in (
        "InternerInsertionSharedEffects", "InternerInsertionSharedRecursionEffects", "InternerInsertionSharedEffectsTests")]
    # Copy the bridges, reduced obligation interfaces and fixtures; retain the
    # original normalization/publication/native bodies and existing induction.
    names = ["shared_attempt_transport", "shared_release_transport", "pending_transport", "callback_obligations", "unfold_shared_erases"]
    for index, source in enumerate(parts):
        source = source.replace("SharedEffects", "SharedMutationEffects").replace("SharedEffectTests", "SharedMutationEffectTests")
        source = source.replace("ResidualTransport", "SharedResidualTransport").replace("ResidualObligations", "SharedResidualObligations")
        source = re.sub(r"\b(" + "|".join(names) + r")\b", lambda m: m[0] + "_sharedMutation", source)
        parts[index] = source
    return parts


def controls(output, env, lean):
    records = control.controls(output, env, lean)
    parts = source_parts()
    def program(parts):
        return "import " + MODULE + "\n" + "\n".join(parts)
    variants = []
    for name, index, before, after, occurrences in (
        ("different-argument-address", 0, "((callbacks right allocator count source input key normalized rightGraph).attempt .arguments owner)",
            "((callbacks right allocator count source input key { normalized with address := normalized.address + 1 } rightGraph).attempt .arguments owner)", 1),
        ("different-publication-id", 0, "((callbacks right allocator count source input key normalized rightGraph).attempt .publish owner)",
            "((callbacks right allocator (count + 1) source input key normalized rightGraph).attempt .publish owner)", 1),
        ("graph-before-append-only", 0, "(graphs : ∀ owner before, rightGraph owner", "(graphs : ∀ owner before, owner.appended = false → rightGraph owner", 3),
        ("wrong-release-selector", 0, "((callbacks right allocator count source input key normalized rightGraph).release action owner)",
            "((callbacks right allocator count source input key normalized rightGraph).release .normalized owner)", 1),
        ("omitted-pop-obligation", 0, "action ≠ .normalized → action ≠ .arguments → ∀ owner,",
            "action ≠ .normalized → action ≠ .arguments → action ≠ .pop → ∀ owner,", 1),
        ("different-recursive-container", 1, "Insertion.Native.callerPrimitives right rightAllocate runtimeSafety allocator container",
            "Insertion.Native.callerPrimitives right rightAllocate runtimeSafety allocator (container + 1)", 1),
        ("lost-duplicate-free-effects", 2, "⟨120, [.allocate .duplicate 12 (some 60)", "⟨17, [.allocate .duplicate 12 (some 60)", 1),
        ("old-publication-table", 2, "(memory published.2).effects.keys Publication.Tests.forceKey = some ⟨8, 42⟩",
            "(memory published.2).effects.keys Publication.Tests.forceKey = some ⟨5, 42⟩", 1),
        ("refusal-as-semantic-error", 2, "(published true).1 = .ok false",
            "(published true).1 = .error (.base (.publication (.language .outOfMemory)))", 1),
    ):
        if parts[index].count(before) != occurrences:
            raise ValueError("ambiguous shared insertion mutation: " + name)
        changed = parts.copy()
        changed[index] = changed[index].replace(before, after)
        variants.append((name, program(changed)))
    return records + native.check_controls(output, env, lean, program(parts), variants, prefix="insertion-shared-")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--preflight", action="store_true")
    native.check(parser.parse_args(), module=MODULE, claims=CLAIMS, dependency_check=dependencies,
        control_check=controls, publication=True, native_dispatch=True, recursive_entries=True,
        item_preparation=True, insertion_control=True, insertion_shared=True)
