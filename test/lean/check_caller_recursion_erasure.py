#!/usr/bin/env python3
"""Audit actual publication binding and recorded all-entry native recursion.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import json
from pathlib import Path
import re

import check_insertion_append_erasure as append
from check_zig_air_memory_proofs import without_imports

native = append.native
MODULE = "Compiler.Extraction.InternerCallerRecursionTraceTests"
RECURSION = append.RECURSION
RECORDING = native.OWNED + "Insertion.Recording."
PUBLICATION = native.OWNED + "Publication."
TESTS = RECURSION + "CallerTraceTests."
LOCAL_CLAIMS = [RECURSION + name for name in (
    "context_publishes", "context_inserts", "context_seed_independent", "unfold_caller_erases", "unfold_recorded_erases")]
LOCAL_CLAIMS += [TESTS + name for name in (
    "existing_entries_erase", "replacement_is_existing", "replacement_events", "replacement_reached", "refused_probe", "exhausted_keeps_history")]
LOCAL_CLAIMS += [native.TRACE + name for name in ("growth_prefix", "optional_growth_prefix")]
LOCAL_CLAIMS += [PUBLICATION + "Recording." + name for name in ("restore_history", "action_segment")]
LOCAL_CLAIMS += [RECURSION + name for name in ("unfold_recorded_prefix", "dispatcher_recorded_prefix", "dispatcher_recorded_segment")]
LOCAL_CLAIMS += [TESTS + name for name in ("existing_entries_prefix", "child_dispatch_prefix", "child_dispatch_segment",
    "child_failure_events", "child_failure_keeps_history", "child_paired_segment")]


CLAIMS = append.CLAIMS + LOCAL_CLAIMS


def local_dependencies(output):
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    required = {
        RECURSION + "context_publishes": {RECURSION + "callerContext", PUBLICATION + "callbacks", PUBLICATION + "publish"},
        RECURSION + "context_inserts": {RECURSION + "callerContext", append.NS + "callerPrimitives", append.NS + "insert"},
        RECURSION + "context_seed_independent": {RECURSION + "context", RECURSION + "callerContext"},
        RECURSION + "unfold_caller_erases": {RECURSION + "unfold_append_erases", PUBLICATION + "EffectTransport.publish",
            PUBLICATION + "external_transport", RECURSION + "unfold", "Nat.rec"},
        RECURSION + "unfold_recorded_erases": {RECURSION + "unfold_caller_erases", RECORDING + "operations",
            native.TRACE + "transport", PUBLICATION + "Recording.probe_transport", native.TRACE + "bytes_transport",
            native.TRACE + "object_transport", native.TRACE + "create_transport", native.TRACE + "copy_transport",
            native.TRACE + "backing_transport", native.TRACE + "optional_growth_transport"},
        TESTS + "existing_entries_erase": {RECURSION + "unfold_recorded_erases", RECURSION + "RecursionEffectTests.base"},
        TESTS + "replacement_is_existing": {RECURSION + "context_publishes", PUBLICATION + "Recording.Tests.replacement"},
        TESTS + "replacement_events": {TESTS + "replacement_is_existing", PUBLICATION + "Recording.Tests.replacement_events"},
        TESTS + "refused_probe": {TESTS + "replacement_is_existing", PUBLICATION + "Recording.Tests.refused_probe"},
        native.TRACE + "growth_prefix": {native.TRACE + "backing_free_prefix", native.TRACE + "recordGrowth"},
        native.TRACE + "optional_growth_prefix": {native.TRACE + "growth_prefix"},
        PUBLICATION + "Recording.restore_history": {PUBLICATION + "Recording.clearHistory", native.TRACE + "prepend"},
        PUBLICATION + "Recording.action_segment": {PUBLICATION + "Recording.restore_history", PUBLICATION + "Recording.clearHistory"},
        RECURSION + "unfold_recorded_prefix": {RECURSION + "unfold_caller_erases", native.TRACE + "prefix_transport",
            PUBLICATION + "Recording.probe_prefix", native.TRACE + "release_request_prefix", native.TRACE + "request_prefix",
            native.TRACE + "backing_prefix", native.TRACE + "optional_growth_prefix"},
        RECURSION + "dispatcher_recorded_prefix": {RECURSION + "dispatcher_erases", RECURSION + "unfold_recorded_prefix"},
        RECURSION + "dispatcher_recorded_segment": {RECURSION + "dispatcher_recorded_prefix", RECURSION + "unfold_recorded_erases",
            RECURSION + "dispatcher_erases", PUBLICATION + "Recording.action_segment"},
        TESTS + "existing_entries_prefix": {RECURSION + "unfold_recorded_prefix", RECURSION + "RecursionEffectTests.base"},
        TESTS + "child_dispatch_prefix": {RECURSION + "dispatcher_recorded_prefix", TESTS + "childDispatch"},
        TESTS + "child_dispatch_segment": {PUBLICATION + "Recording.action_segment", TESTS + "child_dispatch_prefix"},
        TESTS + "child_failure_events": {TESTS + "childDispatch"},
        TESTS + "child_failure_keeps_history": {TESTS + "child_failure_events", TESTS + "child_dispatch_prefix"},
        TESTS + "child_paired_segment": {RECURSION + "dispatcher_recorded_segment", TESTS + "childDispatch"},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError("native caller recursion lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return sorted(required)


def dependencies(output):
    return list(dict.fromkeys(append.dependencies(output) + local_dependencies(output)))


def source_parts():
    directory = native.ROOT / "lean/Compiler/Extraction"
    parts = [without_imports((directory / (name + ".lean")).read_text()) for name in (
        "InternerCallerRecursionEffects", "InternerCallerRecursionTrace", "InternerCallerTraceSegments", "InternerCallerRecursionTraceTests")]
    names = set(re.findall(r"^theorem ([\w.]+)", "\n".join(parts), re.M)) | {"callerContext", "operations", "clearHistory"}
    for index, source in enumerate(parts):
        source = re.sub(r"\b(" + "|".join(sorted(names)) + r")\b", lambda m: m[0] + "_callerMutation",
            source.replace("CallerTraceTests", "CallerMutationTests"))
        for name in names:
            source = source.replace("Publication.Recording.Tests." + name + "_callerMutation", "Publication.Recording.Tests." + name)
        parts[index] = source
    return parts


def local_controls(output, env, lean):
    parts = source_parts()
    def program(parts):
        return "import " + MODULE + "\n" + "\n".join(parts)
    # Mutations check the general proofs and original caller clients. The
    # unchanged control and root audit also check the new concrete child fixture;
    # re-evaluating it after a rejected general proof can obscure that diagnostic
    # with resource exhaustion on deliberately mismatched depth/source geometry.
    legacy_marker = "/-- The same general entry fixture"
    if parts[3].count(legacy_marker) != 1:
        raise ValueError("ambiguous caller recursion fixture boundary")
    legacy_tests = parts[3].split(legacy_marker)[0] + "end " + RECURSION + "CallerMutationTests\n"
    variants = []
    for name, index, before, after, count in (
        ("segment-retains-old-history", 2, "{ state with events := [] }", "state", 1),
        ("segment-captures-old-history", 2, "let captured := action (clearHistory_callerMutation before)", "let captured := action before", 1),
        ("segment-drops-history", 2,
         "action before = (captured.1, captured.2.mapEffects (Effects.mapAllocator (prepend before.memory.effects.allocator.events)))",
         "action before = (captured.1, captured.2)", 1),
        ("segment-reverses-history", 2, "before.memory.effects.allocator.events ++ captured.2.memory.effects.allocator.events",
         "captured.2.memory.effects.allocator.events ++ before.memory.effects.allocator.events", 2),
        ("segment-forces-native-oom", 2,
         "(captured.1, captured.2.mapEffects (Publication.Effects.mapAllocator Recorded.effects))",
         "(.error (.language .outOfMemory), captured.2.mapEffects (Publication.Effects.mapAllocator Recorded.effects))", 1),
        ("segment-rewinds-native-state", 2,
         "(captured.1, captured.2.mapEffects (Publication.Effects.mapAllocator Recorded.effects))",
         "(captured.1, before.mapEffects (Publication.Effects.mapAllocator Recorded.effects))", 1),
        ("segment-unmatched-budgets", 2, "(budgets : leftBase.budget = rightBase.budget)", "(budgets : True)", 1),
        ("segment-unmatched-allocators", 2, "(allocators : leftBase.allocator = rightBase.allocator)", "(allocators : True)", 1),
        ("segment-unmatched-queries", 2, "(queries : leftBase.queries = rightBase.queries)", "(queries : True)", 1),
        ("segment-wrong-native-depth", 2, "unfold rightBound owner usizeBits depth", "unfold rightBound owner usizeBits (depth + 1)", 1),
        ("segment-wrong-native-owner", 2, "context rightBound owner usizeBits", "context rightBound (owner + 1) usizeBits", 1),
        ("segment-wrong-prefix-order", 2,
         "(clearHistory_callerMutation before).mapEffects (Effects.mapAllocator (prepend before.memory.effects.allocator.events)) = before",
         "(clearHistory_callerMutation before).mapEffects (Effects.mapAllocator (prepend before.memory.effects.allocator.events.reverse)) = before", 1),
        ("segment-wrong-native-arguments", 2,
         "let right := ((context rightBound owner usizeBits (unfold rightBound owner usizeBits depth) debug).primitives source address native).simplify key owned",
         "let right := ((context rightBound owner usizeBits (unfold rightBound owner usizeBits depth) debug).primitives source address native).simplify { key with arguments := [] } owned", 1),
        ("wrong-publication-allocator", 0, "Publication.callbacks ops.probe ops.arguments base.allocator source", "Publication.callbacks ops.probe ops.arguments (base.allocator + 1) source", 1),
        ("wrong-publication-source", 0, "Publication.callbacks ops.probe ops.arguments base.allocator source", "Publication.callbacks ops.probe ops.arguments base.allocator { source with length := source.length + 1 }", 1),
        ("unbound-seed-publication", 0, "(Publication.callbacks ops.probe ops.arguments base.allocator source (base.primitives source address input))", "(base.primitives source address input)", 1),
        ("wrong-item-source", 0, "base.allocator container source address meaning input\n", "base.allocator container source { address with offset := address.offset + 1 } meaning input\n", 1),
        ("unmatched-budgets", 0, "(budgets : leftBase.budget = rightBase.budget)", "(budgets : True)", 1),
        ("unmatched-allocators", 0, "(allocators : leftBase.allocator = rightBase.allocator)", "(allocators : True)", 1),
        ("unmatched-queries", 0, "(queries : leftBase.queries = rightBase.queries)", "(queries : True)", 1),
        ("unbound-caller-host", 0, "external := Publication.external ops.arguments", "external := base.external", 1),
        ("different-recursion-depth", 0, "meaning rightBase rightGrowth) owner usizeBits depth)", "meaning rightBase rightGrowth) owner usizeBits (depth + 1))", 1),
        ("lost-probe-outcome", 1, "probe := Publication.Recording.recordProbe ops.probe", "probe := Publication.Recording.recordProbe (fun _ before => (false, before.effects))", 1),
        ("lost-native-item-allocation", 1, "create := recordCreate ops.create", "create := recordCreate (fun _ before => (none, before.effects))", 1),
    ):
        if parts[index].count(before) != count:
            raise ValueError("ambiguous caller recursion mutation: " + name)
        changed = parts.copy()
        changed[index] = changed[index].replace(before, after)
        changed[3] = legacy_tests
        variants.append((name, program(changed)))
    added = native.check_controls(output, env, lean, program(parts), variants, prefix="caller-recursion-")
    for record in added:
        if not record["expectedAcceptance"] and not re.search(
                r"error: (?:Not a definitional equality|Application type mismatch|Type mismatch|Tactic[^\n]*failed|unsolved goals)",
                (output / (record["name"] + ".stdout")).read_text()):
            raise ValueError("caller recursion control lacks a semantic proof failure: " + record["name"])
    return added


def controls(output, env, lean):
    return append.controls(output, env, lean) + local_controls(output, env, lean)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--preflight", action="store_true")
    native.check(parser.parse_args(), module=MODULE, claims=CLAIMS, dependency_check=dependencies,
        control_check=controls, publication=True, native_dispatch=True, recursive_entries=True, item_preparation=True,
        insertion_control=True, insertion_shared=True, insertion_release=True, insertion_append=True, caller_recursion=True)
