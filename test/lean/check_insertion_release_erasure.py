#!/usr/bin/env python3
"""Audit actual native release transport, recording and entry-induction consumption.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import json
from pathlib import Path
import re

import check_insertion_shared_erasure as shared
from check_zig_air_memory_proofs import without_imports

native = shared.native
MODULE = "Compiler.Extraction.InternerInsertionReleaseEffectsTests"
INSERT, NS, RECURSION = shared.INSERT, shared.NS, shared.RECURSION
ROOT_NS = "Compiler.Extraction."
ITEM = ROOT_NS + "AssemblyItemDeinit."
EXPR = ROOT_NS + "ExpressionDeinit."
POP = ROOT_NS + "RepresentativeArray.Pop.Registered."
TESTS = NS + "ReleaseEffectTests."
CLAIMS = shared.CLAIMS.copy()
for namespace, names in (
    (ROOT_NS + "AssemblyItem.", ["destroy_transport"]),
    (ITEM, ["free_transport", "stage_transport", "execute_transport", "run_transport", "Native.finish_transport", "Native.run_transport"]),
    (EXPR, ["executeStages_transport", "Native.step_transport", "Native.run_transport"]),
    (POP, ["finish_transport", "run_transport"]),
    (INSERT, ["release_transport", "allocation_transport"]),
    (NS, ["releaseValue_transport", "releaseLast_transport", "pop_transport", "release_callbacks_transport", "residual_obligations"]),
    (RECURSION, ["unfold_release_erases"]),
    (native.TRACE, ["release_request_observation", "release_request_transport", "release_request_prefix", "bytes_transport",
        "object_transport", "native_item_erases", "expression_erases", "expression_prefix"]),
    (TESTS, ["releases_erase", "allocation_cleanup", "allocation_rejected_before_host", "native_payload_cleanup",
        "failed_invalidation_retains_release", "absent_payload_skips_host", "missing_object_skips_host", "last_cleanup_order",
        "late_read_retains_prior_frees", "final_write_retains_all_frees", "pop_skips_host", "registry_fault_retains_decrement"]),
    (ITEM + "Native.Tests.", ["derived_contract", "actual_destruction", "absent_and_empty", "rejected_payload",
        "failed_invalidation_keeps_release", "field_failures", "projection_preserves_offset"]),
    (EXPR + "Native.Tests.", ["derived_contract", "completed", "late_read_rejection", "final_write_rejection",
        "item_write_rejection", "arguments_rejected", "empty_sentinel", "second_run_rejected"]),
    (NS + "PopTests.", ["derived_contract", "completed", "write_rejected", "late_read_rejected", "registry_rejected", "boundary_rejected"]),
):
    CLAIMS += [namespace + name for name in names]


def dependencies(output):
    checked = shared.dependencies(output)
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    required = {
        ROOT_NS + "AssemblyItem.destroy_transport": {ROOT_NS + "AssemblyItem.destroy", native.NS + "HostReleaseTransport"},
        ITEM + "free_transport": {ITEM + "free", native.NS + "HostReleaseTransport"},
        ITEM + "run_transport": {ITEM + "execute_transport", ITEM + "stage_transport", ITEM + "run", ITEM + "assemblyItemDeinitCode"},
        ITEM + "Native.run_transport": {ITEM + "run_transport", ITEM + "Native.finish_transport", ITEM + "Native.readPayload"},
        EXPR + "Native.step_transport": {ITEM + "Native.run_transport", ROOT_NS + "AssemblyItem.destroy_transport",
            native.NS + "External.Transport.free", EXPR + "Native.Fields.item", EXPR + "Native.Fields.arguments"},
        EXPR + "Native.run_transport": {EXPR + "executeStages_transport", EXPR + "Native.step_transport", EXPR + "expressionDeinitCode"},
        POP + "run_transport": {POP + "finish_transport", POP + "run", ROOT_NS + "RepresentativeArray.Pop.run"},
        INSERT + "allocation_transport": {ROOT_NS + "AssemblyItem.destroy_transport", INSERT + "release_transport", INSERT + "callbacks"},
        NS + "releaseValue_transport": {ITEM + "Native.run_transport", NS + "releaseValue"},
        NS + "releaseLast_transport": {EXPR + "Native.run_transport", NS + "releaseLast", ROOT_NS + "RepresentativeArray.Last.select"},
        NS + "pop_transport": {POP + "run_transport", NS + "pop"},
        NS + "release_callbacks_transport": {NS + "shared_release_transport", INSERT + "allocation_transport",
            NS + "releaseValue_transport", NS + "releaseLast_transport", NS + "pop_transport", NS + "callbacks"},
        NS + "residual_obligations": {NS + "release_callbacks_transport", NS + "AppendTransport", NS + "ResidualTransport.mk"},
        RECURSION + "unfold_release_erases": {NS + "residual_obligations", RECURSION + "unfold_shared_erases", NS + "insert_transport", "Nat.rec"},
        native.TRACE + "release_request_transport": {native.TRACE + "recordRelease", native.TRACE + "request_transport"},
        native.TRACE + "expression_erases": {EXPR + "Native.run_transport", native.TRACE + "bytes_transport", native.TRACE + "object_transport", native.TRACE + "transport"},
        native.TRACE + "expression_prefix": {EXPR + "Native.run_transport", native.TRACE + "release_request_prefix", native.TRACE + "prefix_transport"},
        TESTS + "releases_erase": {NS + "release_callbacks_transport", native.TRACE + "bytes_transport", native.TRACE + "object_transport"},
        TESTS + "last_cleanup_order": {NS + "callbacks", EXPR + "Native.run", native.TRACE + "recordRelease", native.TRACE + "record"},
        TESTS + "registry_fault_retains_decrement": {NS + "callbacks", POP + "run", POP + "finish"},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError("native release erasure lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return list(dict.fromkeys(checked + sorted(required)))


def source_parts():
    directory = native.ROOT / "lean/Compiler/Extraction"
    parts = [without_imports((directory / (name + ".lean")).read_text()) for name in (
        "AssemblyReleaseEffects", "RepresentativePopEffects", "InternerInsertionReleaseEffects",
        "InternerInsertionReleaseRecursionEffects", "AssemblyReleaseTrace", "InternerInsertionReleaseEffectsTests")]
    # Keep the imported state projection and every original execution body.
    # Recheck the new proof bridges, reduced premise and actual recorder together.
    before, after = parts[0].split("def State.mapEffects", 1)
    parts[0] = before + "variable" + after.split("variable", 1)[1]
    names = {name.rsplit(".", 1)[-1] for name in re.findall(r"^theorem ([\w.]+)", "\n".join(parts), re.M)}
    names.update(["recordRelease", "recordBytes", "recordObject"])
    for index, source in enumerate(parts):
        source = source.replace("HostReleaseTransport", "ReleaseMutationHostTransport").replace("AppendTransport", "ReleaseAppendTransport")
        source = source.replace("ReleaseEffectTests", "ReleaseMutationTests")
        source = re.sub(r"\b(" + "|".join(sorted(names)) + r")\b", lambda m: m[0] + "_releaseMutation", source)
        parts[index] = source
    return parts


def controls(output, env, lean):
    records = shared.controls(output, env, lean)
    parts = source_parts()
    def program(parts):
        return "import " + MODULE + "\n" + "\n".join(parts)
    variants = []
    for name, index, before, after, count in (
        ("valid-memory-only", 0, "∀ argument before, original argument", "∀ argument before, before.memory.valid = true → original argument", 1),
        ("different-object", 0, "(AssemblyItem.destroy original allocator object)", "(AssemblyItem.destroy original allocator (object + 1))", 1),
        ("different-payload-extent", 0, "(free original allocator slice)", "(free original allocator { slice with length := slice.length + 1 })", 1),
        ("rewound-stage-continuation", 0, "exact ih reached", "exact ih before", 2),
        ("different-pop-owner", 1, "(run allocator owner) (run allocator owner)", "(run allocator owner) (run allocator (owner + 1))", 1),
        ("different-last-row", 2, "(releaseLast right allocator container)", "(releaseLast right allocator (container + 1))", 1),
        ("append-before-publication-only", 2, "∀ cells value owner, Effect.Transport", "∀ cells value owner, owner.appended = false → Effect.Transport", 1),
        ("different-recursive-safety", 3, "Insertion.Native.callerPrimitives right rightAllocate runtimeSafety allocator container",
            "Insertion.Native.callerPrimitives right rightAllocate (!runtimeSafety) allocator container", 1),
        ("wrong-release-length", 4, ".payloadFree slice.address slice.length slice.offset", ".payloadFree slice.address (slice.length + 1) slice.offset", 1),
        ("wrong-object-event", 4, "recordRelease_releaseMutation Event.itemFree host", "recordRelease_releaseMutation (fun id => .itemFree (id + 1)) host", 1),
        ("lost-release-effects", 4, "((), host argument state)", "((), state.effects)", 3),
        ("uncleared-allocation-local", 5, "allocation.2.item.object = none", "allocation.2.item.object = some 6", 1),
    ):
        if parts[index].count(before) != count:
            raise ValueError("ambiguous native release mutation: " + name)
        changed = parts.copy()
        changed[index] = changed[index].replace(before, after)
        variants.append((name, program(changed)))
    return records + native.check_controls(output, env, lean, program(parts), variants, prefix="insertion-release-")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--preflight", action="store_true")
    native.check(parser.parse_args(), module=MODULE, claims=CLAIMS, dependency_check=dependencies,
        control_check=controls, publication=True, native_dispatch=True, recursive_entries=True, item_preparation=True,
        insertion_control=True, insertion_shared=True, insertion_release=True)
