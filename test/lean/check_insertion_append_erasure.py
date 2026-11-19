#!/usr/bin/env python3
"""Audit native append/growth erasure, recording and entry-induction consumption.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import json
from pathlib import Path
import re

import check_insertion_release_erasure as release
from check_zig_air_memory_proofs import without_imports

native = release.native
MODULE = "Compiler.Extraction.InternerInsertionAppendEffectsTests"
NS, RECURSION = release.NS, release.RECURSION
ARRAY = "Compiler.Extraction.RepresentativeArray."
BACKING = ARRAY + "Backing."
APPEND = ARRAY + "Append."
TESTS = NS + "AppendEffectTests."
CLAIMS = release.CLAIMS.copy()
for namespace, names in (
    (BACKING, ["reserve_transport", "Registry.run_transport", "Release.check_transport", "Release.run_transport",
        "RegisteredCopy.run_transport", "publication_transport", "Relocation.finish_transport", "Relocation.run_transport", "Fallback.run_transport"]),
    (ARRAY, ["Remap.run_transport", "Growth.Registered.run_transport", "Capacity.Registered.ensure_transport",
        "Growth.firstAllocation_transport", "Growth.run_transport", "Capacity.ensure_transport"]),
    (APPEND, ["Execution.runWithCapacity_transport", "Execution.ownerWithCapacity_transport", "Registered.admit_transport",
        "Registered.finish_transport", "Registered.run_transport", "Registered.growingCapacity_transport", "Registered.runWithGrowth_transport"]),
    (NS, ["allocation_transport", "growthCallbacks_transport", "append_transport"]),
    (RECURSION, ["unfold_append_erases"]),
    (native.TRACE, ["private_observation", "private_prefix", "backing_transport", "backing_free_transport", "growth_transport",
        "optional_growth_transport", "backing_prefix", "backing_free_prefix", "append_erases"]),
    (TESTS, ["growth_erases", "growth_order", "growth_oom", "rejected_region", "unsupported_remap_skips_host",
        "partial_copy_keeps_allocation", "partial_publication_keeps_free", "missing_local_skips_host", "registry_collision_keeps_request",
        "empty_and_invalid_skip_host", "first_records_request", "spare_skips_host"]),
    (APPEND + "Registered.GrowthTests.", ["derived_contract", "all_outcomes_parent", "failed_growth", "wrong_allocator", "partial_copy", "partial_publication"]),
    (BACKING + "Registry.Tests.", ["without_final_premises", "oom_keeps_effects", "wrong_region_keeps_effects", "overlap_keeps_old_backing",
        "null_region_rejects", "extent_overflow_is_oom", "capacity_width_rejects", "collision_keeps_allocation",
        "empty_does_not_register", "invalid_state_skips_allocator", "selected_allocator_brand"]),
):
    CLAIMS += [namespace + name for name in names]


def dependencies(output):
    checked = release.dependencies(output)
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    required = {
        BACKING + "reserve_transport": {"Compiler.ZigAir.Memory.RegionAllocation.reserve_transport", BACKING + "reserve"},
        BACKING + "Registry.run_transport": {BACKING + "Registry.run", BACKING + "reserve_transport", "Compiler.Extraction.Memory.allocate"},
        BACKING + "Release.run_transport": {BACKING + "Release.run", BACKING + "Release.check_transport", BACKING + "Release.External.Transport"},
        BACKING + "Relocation.run_transport": {BACKING + "Relocation.run", BACKING + "RegisteredCopy.run_transport", BACKING + "Relocation.finish_transport"},
        BACKING + "Relocation.finish_transport": {BACKING + "Release.run_transport", BACKING + "publication_transport"},
        BACKING + "Fallback.run_transport": {BACKING + "Registry.run_transport", BACKING + "Relocation.run_transport"},
        ARRAY + "Remap.run_transport": {ARRAY + "Remap.run", BACKING + "Release.run_transport"},
        ARRAY + "Growth.Registered.run_transport": {ARRAY + "Growth.prepare", ARRAY + "Remap.run_transport", BACKING + "Fallback.run_transport", BACKING + "publication_transport"},
        ARRAY + "Capacity.Registered.ensure_transport": {ARRAY + "Capacity.prepare", ARRAY + "Growth.Registered.run_transport"},
        ARRAY + "Growth.firstAllocation_transport": {ARRAY + "Growth.firstAllocation", BACKING + "reserve_transport", ARRAY + "Copy.run", ARRAY + "Publication.run"},
        ARRAY + "Capacity.ensure_transport": {ARRAY + "Capacity.ensure", ARRAY + "Growth.run_transport"},
        APPEND + "Execution.runWithCapacity_transport": {APPEND + "Execution.runWithCapacity", APPEND + "Execution.assumeCapacity"},
        APPEND + "Execution.ownerWithCapacity_transport": {APPEND + "Execution.runWithCapacity_transport", "Compiler.ZigAir.Memory.fieldPointer"},
        APPEND + "Registered.finish_transport": {APPEND + "Registered.finish", APPEND + "Registered.admit_transport"},
        APPEND + "Registered.run_transport": {APPEND + "Execution.ownerWithCapacity_transport", ARRAY + "Capacity.ensure_transport", APPEND + "Registered.finish_transport"},
        APPEND + "Registered.growingCapacity_transport": {ARRAY + "Capacity.Registered.ensure_transport", APPEND + "Registered.growingCapacity"},
        APPEND + "Registered.runWithGrowth_transport": {APPEND + "Execution.ownerWithCapacity_transport", APPEND + "Registered.growingCapacity_transport", APPEND + "Registered.finish_transport"},
        NS + "append_transport": {NS + "append", NS + "allocation_transport", NS + "growthCallbacks_transport",
            APPEND + "Registered.run_transport", APPEND + "Registered.runWithGrowth_transport", ARRAY + "Growth.Registered.Callbacks.OptionalTransport"},
        RECURSION + "unfold_append_erases": {NS + "append_transport", RECURSION + "unfold_release_erases", NS + "insert_transport", "Nat.rec"},
        native.TRACE + "private_observation": {native.TRACE + "recordPrivate", native.TRACE + "recordResult"},
        native.TRACE + "request_observation": {native.TRACE + "recordRequest", native.TRACE + "recordResult"},
        native.TRACE + "append_erases": {NS + "append_transport", native.TRACE + "backing_transport", native.TRACE + "optional_growth_transport"},
        TESTS + "growth_erases": {native.TRACE + "append_erases", NS + "append"},
        TESTS + "growth_order": {NS + "append", native.TRACE + "recordBacking", native.TRACE + "recordBackingFree", ARRAY + "Remap.run"},
        TESTS + "partial_publication_keeps_free": {BACKING + "Relocation.run", ARRAY + "Publication.Registered.run", native.TRACE + "recordResult"},
        TESTS + "first_records_request": {APPEND + "Registered.run", native.TRACE + "recordBacking"},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError("native append erasure lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return list(dict.fromkeys(checked + sorted(required)))


def source_parts():
    directory = native.ROOT / "lean/Compiler/Extraction"
    parts = [without_imports((directory / (name + ".lean")).read_text()) for name in (
        "RepresentativeBackingEffects", "RepresentativeCapacityEffects", "RepresentativeAppendEffects",
        "InternerInsertionAppendEffects", "InternerInsertionAppendRecursionEffects", "RepresentativeBackingTrace",
        "InternerInsertionAppendEffectsTests")]
    names = {name.rsplit(".", 1)[-1] for name in re.findall(r"^theorem ([\w.]+)", "\n".join(parts), re.M)}
    names.update(["recordPrivate", "recordBacking", "recordBackingFree", "recordGrowth"])
    for index, source in enumerate(parts):
        source = source.replace("RegionAllocation.reserve_transport", "original_region_transport")
        for interface in ("Allocate.Transport", "Release.External.Transport", "Callbacks.Transport", "Callbacks.OptionalTransport"):
            source = source.replace(interface, interface + "AppendMutation")
        source = source.replace("AppendEffectTests", "AppendMutationTests")
        source = re.sub(r"\b(" + "|".join(sorted(names)) + r")\b", lambda m: m[0] + "_appendMutation", source)
        parts[index] = source.replace("original_region_transport", "RegionAllocation.reserve_transport")
    return parts


def controls(output, env, lean):
    records = release.controls(output, env, lean)
    parts = source_parts()
    def program(parts):
        return "import " + MODULE + "\n" + "\n".join(parts)
    variants = []
    for name, index, before, after, count in (
        ("different-allocator-brand", 0, "right allocator bytes alignment (project effects)", "right (allocator + 1) bytes alignment (project effects)", 1),
        ("different-free-extent", 0, "right allocator base bytes alignment (project effects)", "right allocator base (bytes + 1) alignment (project effects)", 1),
        ("different-remap", 0, "Growth.Registered.run callback right rightFree", "Growth.Registered.run .unsupported right rightFree", 1),
        ("mismatched-growth-route", 0, "| _, _ => False", "| _, _ => True", 1),
        ("rewound-first-allocation-effects", 1, "project (Growth.firstAllocation state header capacity (left allocator) effects).2", "project effects", 1),
        ("capacity-at-zero-only", 2, "∀ state header minimum effects, right state header minimum", "∀ state header minimum effects, minimum = 0 → right state header minimum", 1),
        ("wrong-reached-registry", 2, "(reached.mapEffects project) registry =", "(reached.mapEffects project) before.heap =", 1),
        ("different-native-container", 3, "AppendTransport project left right runtimeSafety allocator container input", "AppendTransport project left right runtimeSafety allocator (container + 1) input", 1),
        ("different-recursive-container", 4, "Insertion.Native.callerPrimitives right rightAllocate runtimeSafety allocator container", "Insertion.Native.callerPrimitives right rightAllocate runtimeSafety allocator (container + 1)", 1),
        ("wrong-request-alignment", 5, ".backingAllocate request.1 request.2.1 request.2.2 response", ".backingAllocate request.1 request.2.1 (request.2.2 + 1) response", 1),
        ("wrong-free-extent", 5, ".backingFree request.1 request.2.1 request.2.2.1 request.2.2.2", ".backingFree request.1 request.2.1 (request.2.2.1 + 1) request.2.2.2", 1),
        ("lost-private-effects", 5, "(host argument before.effects) before", "((host argument before.effects).1, before.effects) before", 1),
    ):
        if parts[index].count(before) != count:
            raise ValueError("ambiguous native append mutation: " + name)
        changed = parts.copy()
        changed[index] = changed[index].replace(before, after)
        variants.append((name, program(changed)))
    return records + native.check_controls(output, env, lean, program(parts), variants, prefix="insertion-append-")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--preflight", action="store_true")
    native.check(parser.parse_args(), module=MODULE, claims=CLAIMS, dependency_check=dependencies,
        control_check=controls, publication=True, native_dispatch=True, recursive_entries=True, item_preparation=True,
        insertion_control=True, insertion_shared=True, insertion_release=True, insertion_append=True)
