"""Actual caller protocol checks consumed by the native scoped gate.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import json
import re

import check_native_resource_trace as native
from check_zig_air_memory_proofs import without_imports

NS = native.OWNED + "Caller.ProtocolTrace."
CHILD = native.OWNED + "ConstructorItem.NativeRecursion.ChildTrace."
CLAIMS = [NS + name for name in (
    "record_erases", "record_prefix", "graph_recorded", "findBody_erases", "forceBody_erases",
    "finish_erases", "invoke_erases", "find_erases", "force_erases", "findBody_prefix", "forceBody_prefix",
    "finish_prefix", "invoke_prefix", "find_segment", "force_segment", "cached_events", "cached_projected",
    "lookup_body", "scoped_lookup", "lookup_projected", "classification_projected", "initialized_recorded",
    "finish_empty", "capacity_recorded", "capacity_projected", "scoped_initialization_failed", "initialization_failed_projected")]
CLAIMS += [NS + name for name in ("initialization_projected", "take_projected", "handoff_projected",
    "close_from_cleanup", "lookup_close_projected", "taken_close_projected")]
CLAIMS += [NS + "Native." + name for name in (
    "dispatch_erases", "find_segment", "insertion_events", "publication_events", "publication_rejected", "insertion_rejected")]
CLAIMS += [NS + "Tests." + name for name in (
    "cache_events", "cache_observed", "cache_scope", "cache_composed", "capacity_no_events", "semantic_retention", "missing_token", "force_publication", "force_scope", "take_oom", "take_oom_scope")]


def dependencies(output):
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    required = {
        NS + "record_erases": {NS + "record", NS + "Recorded.native"},
        NS + "record_prefix": {NS + "record", NS + "prepend"},
        NS + "graph_recorded": {NS + "record", NS + "graphObservation", native.OWNED + "graph"},
        NS + "findBody_erases": {NS + "record_erases", NS + "findBody", native.OWNED + "Caller.findBody"},
        NS + "forceBody_erases": {NS + "record_erases", NS + "forceBody", native.OWNED + "Caller.forceBody"},
        NS + "finish_erases": {NS + "finish", native.OWNED + "finish", native.OWNED + "cleanup"},
        NS + "invoke_erases": {NS + "finish_erases", NS + "invoke"},
        NS + "find_erases": {NS + "invoke_erases", NS + "findBody_erases"},
        NS + "force_erases": {NS + "invoke_erases", NS + "forceBody_erases"},
        NS + "findBody_prefix": {NS + "record_prefix", NS + "findBody"},
        NS + "forceBody_prefix": {NS + "record_prefix", NS + "forceBody"},
        NS + "finish_prefix": {NS + "record_prefix", NS + "finish"},
        NS + "invoke_prefix": {NS + "finish_prefix", NS + "invoke"},
        NS + "find_segment": {NS + name for name in ("find_erases", "invoke_prefix", "findBody_prefix")},
        NS + "force_segment": {NS + name for name in ("force_erases", "invoke_prefix", "forceBody_prefix")},
        NS + "cached_events": {NS + "initialization", NS + "closing", native.OWNED + "Caller.Initialization.capture_success"},
        NS + "Native.dispatch_erases": {CHILD + "constructors_erase", NS + "Native.dispatch",
            native.OWNED + "ConstructorItem.NativeRecursion.dispatcher_snapshot"},
        NS + "Native.find_segment": {NS + "find_segment", NS + "Native.graphObservations", NS + "Native.physical"},
        NS + "Native.insertion_events": {NS + "Native.graphObservations", native.OWNED + "Insertion.Native.checkedCount_read"},
        NS + "Native.publication_events": {NS + "Native.graphObservations", native.OWNED + "Publication.admit"},
        NS + "Native.publication_rejected": {NS + "Native.graphObservations", native.OWNED + "Publication.publish"},
        NS + "Native.insertion_rejected": {NS + "Native.graphObservations", native.OWNED + "Insertion.Native.body_rejected"},
        NS + "Tests.cache_observed": {NS + "cached_events", native.OWNED + "Caller.CacheStream.Tests.trace_layout"},
        NS + "Tests.cache_events": {NS + "Tests.cache_observed"},
        NS + "Tests.cache_scope": {NS + "Tests.cache_observed", native.OWNED + "Caller.CacheStream.Tests.existing_family", NS + "scopeView"},
        NS + "cached_projected": {NS + "lookup_projected"},
        NS + "lookup_body": {NS + "findBody", native.OWNED + "Caller.Initialization.capture_success"},
        NS + "scoped_lookup": {"Compiler.Extraction.Interner.Scoped.findDetailed", "Compiler.Extraction.Interner.FindCode.controlRun"},
        NS + "lookup_projected": {NS + "lookup_body", NS + "scoped_lookup", NS + "initialized_recorded", NS + "lookup_close_projected"},
        NS + "initialized_recorded": {NS + "initialization_projected", native.OWNED + "Caller.Initialization.successful_stream"},
        NS + "classification_projected": {NS + "lookup_projected"},
        NS + "finish_empty": {NS + "finish", native.OWNED + "cleanup"},
        NS + "capacity_recorded": {NS + "finish_empty", NS + "findBody"},
        NS + "capacity_projected": {NS + "capacity_recorded", NS + "scopeView"},
        NS + "scoped_initialization_failed": {"Compiler.Extraction.Interner.Scoped.findDetailed", "Compiler.Extraction.Interner.FindCode.controlRun"},
        NS + "initialization_failed_projected": {NS + "initialization_projected", NS + "finish_empty",
            NS + "scoped_initialization_failed", native.OWNED + "Caller.initialize_failed"},
        NS + "Tests.capacity_no_events": {NS + "capacity_recorded"},
        NS + "initialization_projected": {NS + "initialization", NS + "scopeView", native.OWNED + "Caller.Initialization.checked_ordinary", native.OWNED + "Caller.Initialization.coupled"},
        NS + "take_projected": {NS + "taking", NS + "scopeView", native.OWNED + "Caller.Take.verified"},
        NS + "handoff_projected": {NS + "handingOff", NS + "scopeView", native.OWNED + "handoff"},
        NS + "close_from_cleanup": {NS + "closing", NS + "scopeView", native.OWNED + "Caller.Close.checked_of_cleanup"},
        NS + "lookup_close_projected": {NS + "close_from_cleanup", native.OWNED + "Caller.Close.lookup_verified"},
        NS + "taken_close_projected": {NS + "close_from_cleanup", native.OWNED + "Caller.Close.taken_verified"},
        NS + "Tests.cache_composed": {NS + "Tests.cache_events", NS + "find_erases", native.OWNED + "Caller.CacheStream.Tests.existing_family"},
        NS + "Tests.force_publication": {NS + "force_erases", NS + "Tests.forced"},
        CHILD + "Tests.recorded_cache_family": {NS + "Tests.cache_events", CHILD + "Tests.cacheObservation"},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError("caller protocol lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return sorted(required)


def controls(output, env, lean):
    directory = native.ROOT / "lean/Compiler/Extraction"
    parts = [without_imports((directory / (name + ".lean")).read_text()).replace("ProtocolTrace", "ProtocolTraceMutation")
        for name in ("InternerCallerProtocolTrace", "InternerCallerNativeProtocol", "InternerCallerProtocolScope", "InternerCallerProtocolPrefix", "InternerCallerProtocolFailure", "InternerCallerProtocolLookup", "InternerCallerProtocolCache", "InternerCallerProtocolTraceTests")]

    def program(parts):
        return "import Compiler.Extraction.InternerCallerProtocolTraceTests\n" + "\n".join(parts)

    variants = []
    for name, index, before, after, count in (
        ("rewound-native-state", 0, "⟨actual.2, observed.1, before.events ++ observed.2⟩", "⟨before.native, observed.1, before.events ++ observed.2⟩", 1),
        ("changed-native-result", 0, "(actual.1, ⟨actual.2, observed.1", "(.error (.language .unsupported), ⟨actual.2, observed.1", 1),
        ("lost-history", 0, "before.events ++ observed.2", "observed.2", 1),
        ("reordered-history", 0, "before.events ++ observed.2", "observed.2 ++ before.events", 1),
        ("observed-reached-input", 0, "observe before.native before.tokens", "observe actual.2 before.tokens", 1),
        ("lost-initialization-events", 0, "({ tokens with toScope := scope }, captured.2.events.map Event.normalization)", "({ tokens with toScope := scope }, [])", 1),
        ("wrong-initialization-values", 0, "commutative source buffer request.arguments before.world.memory", "commutative source buffer [] before.world.memory", 1),
        ("wrong-take-origin", 0, "Take.capture external allocator lookup.origin handle", "Take.capture external allocator .input handle", 1),
        ("lost-take-events", 0, "phase := if captured.1.1 then .cleanup else tokens.phase },\n      captured.2.events.map Event.normalization)",
         "phase := if captured.1.1 then .cleanup else tokens.phase }, [])", 1),
        ("stale-take-token", 0, "{ tokens with lookup := some captured.1.2, phase :=", "{ tokens with lookup := some lookup, phase :=", 1),
        ("hidden-missing-token", 0, "{ tokens with incomplete := true }", "{ tokens with incomplete := false }", 2),
        ("lost-parent-token", 0, "(tokens, observe slice before.world)", "({}, observe slice before.world)", 1),
        ("wrong-graph-input", 0, "observe slice before.world",
         "observe slice { before.world with graph := { before.world.graph with allocationCursor := before.world.graph.allocationCursor + 1 } }", 1),
        ("release-after-handoff", 0, "if before.scope.handedOff then NormalizationOwnership.Exit.transfer",
         "if before.scope.handedOff then NormalizationOwnership.Exit.cleanup", 1),
        ("wrong-cleanup-guard", 0, "if ordinary result then", "if !ordinary result then", 1),
        ("lost-cleanup-events", 0, "({ tokens with lookup := some captured.1 }, captured.2.events.map Event.normalization)",
         "({ tokens with lookup := some captured.1 }, [])", 1),
        ("lost-normalized-items", 0, "⟨some lookup, captured.2.effects.handle.values, .lookup⟩", "⟨some lookup, [], .lookup⟩", 1),
        ("premature-take-phase", 0, "phase := if captured.1.1 then .cleanup else tokens.phase", "phase := .cleanup", 1),
        ("lost-take-phase", 0, "phase := if captured.1.1 then .cleanup else tokens.phase", "phase := tokens.phase", 1),
        ("lost-handoff-phase", 0, "handoff := record OwnedCall.handoff handingOff", "handoff := record OwnedCall.handoff unchanged", 1),
        ("wrong-handoff-observation", 0, "({ tokens with phase := .transfer }, [])", "({ tokens with phase := .cleanup }, [])", 1),
        ("cleared-items-at-close", 0, "{ tokens with lookup := some captured.1 }", "{ tokens with lookup := some captured.1, items := [] }", 1),
        ("cleared-phase-at-close", 0, "{ tokens with lookup := some captured.1 }", "{ tokens with lookup := some captured.1, phase := .lookup }", 1),
        ("wrong-scope-cursor", 2, "allocationCursor := before.events.length", "allocationCursor := before.native.world.graph.allocationCursor", 1),
        ("wrong-dispatch-opcode", 1, "usizeBits key.instruction key.arguments debug operand slice.address)",
         "usizeBits 0 key.arguments debug operand slice.address)", 1),
        ("probe-after-rejection", 1, "| .error _ => []\n    | .ok () =>", "| .error _ => [.publicationProbe key false]\n    | .ok () =>", 1),
        ("wrong-probe-outcome", 1, "| .ok () => [.publicationProbe key (ops.probe key (Publication.forget before.memory)).1]",
         "| .ok () => [.publicationProbe key true]", 1),
        ("insert-after-rejection", 1, "| .error _ => []\n      | .ok _ =>", "| .error _ => [.publicationProbe key false]\n      | .ok _ =>", 1),
        ("wrong-insertion-mode", 1, "          key slice deterministic cells before growth []).2.events.map Event.insertion",
         "          key slice false cells before growth []).2.events.map Event.insertion", 1),
    ):
        if parts[index].count(before) != count:
            raise ValueError("ambiguous caller protocol mutation: " + name)
        changed = parts.copy()
        changed[index] = changed[index].replace(before, after)
        variants.append((name, program(changed)))
    records = native.check_controls(output, env, lean, program(parts), variants, prefix="caller-protocol-")
    for record in records:
        if not record["expectedAcceptance"] and not re.search(
                r"error: (?:Not a definitional equality|Application type mismatch|Type mismatch|Tactic[^\n]*failed|unsolved goals)",
                (output / (record["name"] + ".stdout")).read_text()):
            raise ValueError("caller protocol control lacks a semantic proof failure: " + record["name"])
    return records
