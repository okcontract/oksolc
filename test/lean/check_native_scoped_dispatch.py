#!/usr/bin/env python3
"""Check the initialized/taken scope through native miss and reached cleanup.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import json
import re
from pathlib import Path

import check_scoped_miss as scoped
import check_caller_recursion_erasure as caller
import child_protocol_checks as child_protocol
import caller_protocol_checks as caller_protocol
import constructor_protocol_checks as constructor_protocol
import miss_protocol_checks as miss_protocol
import history_protocol_checks as history_protocol
import initialized_protocol_checks as initialized_protocol
import constructor_return_checks as constructor_return
from check_zig_air_memory_proofs import without_imports

native = scoped.native
NS = native.OWNED + "ConstructorItem.NativeRecursion."
MODULE = "Compiler.Extraction.InternerNativeScopedStreamTests"
CLAIMS = scoped.CLAIMS + [scoped.RECURSIVE + "projects_at_bind_from", scoped.NS + "graph_at", scoped.NS + "miss_at"]
CLAIMS += [NS + name for name in ("simplify_at", "scoped_miss_at", "scoped_miss_from_frame", "closed_miss_from_frame", "closed_miss_after_take", "closed_miss_initialized_stream")]
CLAIMS += [NS + "ScopeTests." + name for name in ("outcome_children", "seed_graph_operations", "spare_from_children", "spare_take_entry", "spare_closed_from_children", "spare_initialized_closed")]
CLAIMS += [native.OWNED + "Insertion.Native.NativeSpareTests.reached_frame"]
CLAIMS += [native.OWNED + name for name in ("insert_post_at", "miss_post_at", "Caller.Close.of_post", "Caller.ScopeProjection.close_completion")]

STORAGE_TRACE = "Compiler.Extraction.Storage.Trace."
INSERTION = native.OWNED + "Insertion.Native."
CLAIMS += [STORAGE_TRACE + name for name in ("transport", "rejected_absorbs", "execute_recorded")]
CLAIMS += [STORAGE_TRACE + "Tests." + name for name in (
    "existing_family", "cleanup_before_attempt", "ordinary_oom_cleans", "semantic_fault_stops",
    "wrong_site", "wrong_owner", "wrong_kind", "wrong_release", "wrong_release_owner", "exhausted", "fault_is_not_oom")]
CLAIMS += [INSERTION + name for name in ("execution_observed", "execution_recorded", "body_recorded", "TraceTests.spare_body")]
ACTION = "Compiler.Extraction.Interner.InsertionExecution."
CLAIMS += [ACTION + name for name in ("transaction_verified", "action_verified")]
CLAIMS += [ACTION + "ActionTests." + name for name in (
    "success", "publication_oom", "stopped_cleanup_fault", "exhausted_trace", "missing_representatives", "ordinary_words")]
CLAIMS += [INSERTION + name for name in ("insert_replayed", "scoped_insert_replayed", "insert_replayed_verified",
    "TraceTests.spare_header", "TraceTests.spare_scoped_replay")]
INVOCATION = "Compiler.Extraction.Interner.InvocationTrace."
CLAIMS += [INVOCATION + name for name in ("normalizations_length", "insertions_length", "normalizations_append",
    "insertions_append", "normalizations_embed", "insertions_embed")]
CLAIMS += [INVOCATION + "Tests." + name for name in ("normalization_foreign", "insertion_foreign", "no_skipping",
    "insertion_slot", "normalization_slot", "cleanup_cursor", "foreign_admission")]
CLAIMS += [native.OWNED + "Caller.Close.transferred_stream"]
CLAIMS += [INSERTION + name for name in ("scoped_insert_stream", "finished_insert_stream", "initialized_insert_stream", "TraceTests.spare_initialized_insert")]
PUBLICATION = native.OWNED + "Publication."
CLAIMS += [INVOCATION + "publish_slot"]
CLAIMS += [INVOCATION + "Tests." + name for name in ("publication_views", "publication_foreign",
    "publication_wrong_key", "publication_no_skipping", "publication_exhausted")]
CLAIMS += [PUBLICATION + name for name in ("publish_stream", "closed_publish_stream", "StreamTests.force_closed")]
MISS = native.OWNED + "MissStream."
CLAIMS += [MISS + name for name in ("routed", "finish_map", "inserted", "published", "failed",
    "Tests.spare_selected", "Tests.spare_inserted", "CountedTests.selected_effects", "CountedTests.failed_closed")]
CLAIMS += [MISS + name for name in ("selected_preserved", "tail_inputs", "from_children",
    "AdmissionTests.spare_from_children", "AdmissionTests.spare_outcomes")]
CLAIMS += [MISS + name for name in ("scoped_routed", "scoped_selected", "scoped_publish_return", "projected",
    "scoped_from_children", "ReplayTests.spare_projected", "ReplayTests.absent_candidate", "ReplayTests.counted_routes")]
CLAIMS += [native.OWNED + "Caller.Take.initialized_taken_stream", MISS + "initialized_from_children",
    MISS + "InitializedTests.spare_initialized"]
CACHE = native.OWNED + "Caller.CacheStream."
CLAIMS += [CACHE + name for name in ("scoped_cached", "cached", "Tests.trace_layout", "Tests.existing_family")]

CLAIMS = list(dict.fromkeys(CLAIMS + caller.LOCAL_CLAIMS + child_protocol.CLAIMS + caller_protocol.CLAIMS + constructor_protocol.CLAIMS + miss_protocol.CLAIMS + history_protocol.CLAIMS + initialized_protocol.CLAIMS + constructor_return.CLAIMS))


def dependencies(output):
    checked = scoped.dependencies(output) + caller.local_dependencies(output) + child_protocol.dependencies(output) + caller_protocol.dependencies(output) + constructor_protocol.dependencies(output) + miss_protocol.dependencies(output) + history_protocol.dependencies(output) + initialized_protocol.dependencies(output) + constructor_return.dependencies(output)
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    required = {
        scoped.RECURSIVE + "projects_at_bind_from": {scoped.RECURSIVE + "ProjectsAt", "Compiler.Algebraic.Effect.bind"},
        scoped.NS + "graph_at": {scoped.NS + "Frame", native.OWNED + "graph", "Compiler.Extraction.Interner.Scoped.liftGraph"},
        scoped.NS + "miss_at": {scoped.RECURSIVE + "projects_at_bind_from", scoped.NS + "graph_at", scoped.NS + "graph", scoped.NS + "handoff"},
        NS + "simplify_at": {NS + "dispatch_projects_framed_at", NS + "dispatcher_snapshot", native.OWNED + "NativeGraph.Facts.reads", NS + "dispatchModel"},
        NS + "scoped_miss_at": {NS + "simplify_at", scoped.NS + "miss_at", NS + "context", NS + "dispatchModel"},
        NS + "scoped_miss_from_frame": {NS + "scoped_miss_at", NS + "InputFrame"},
        NS + "closed_miss_from_frame": {NS + "simplify_at", NS + "scoped_miss_from_frame", native.OWNED + "miss_post_at",
            native.OWNED + "Caller.Close.of_post", scoped.NS + "close_completion", native.OWNED + "finish"},
        NS + "closed_miss_after_take": {NS + "closed_miss_from_frame", native.OWNED + "Caller.Close.take_success", native.OWNED + "take"},
        NS + "closed_miss_initialized_stream": {NS + "closed_miss_after_take", native.OWNED + "Caller.Take.initialized_stream",
            native.OWNED + "Caller.Initialization.capture_success", native.OWNED + "Caller.Take.checked_scope",
            native.OWNED + "Caller.ScopeProjection.scopeAt"},
        NS + "ScopeTests.spare_initialized_closed": {NS + "closed_miss_initialized_stream",
            native.OWNED + "Publication.GraphTests.prefix_results", native.OWNED + "Insertion.Native.NativeSpareTests.reached_frame",
            native.OWNED + "Insertion.Native.CallerFirstSuccessTests.native_borrow_good"},
        NS + "ScopeTests.outcome_children": {scoped.RECURSIVE + "projectionAt", NS + "ScopeTests.resultChildren"},
        NS + "ScopeTests.seed_graph_operations": {NS + "dispatchModel"},
        NS + "ScopeTests.spare_from_children": {NS + "scoped_miss_from_frame", native.OWNED + "Insertion.Native.NativeSpareTests.reached_frame"},
        NS + "ScopeTests.spare_take_entry": {native.OWNED + "Caller.initialize_origin", native.OWNED + "Publication.GraphTests.prefix_results"},
        NS + "ScopeTests.spare_closed_from_children": {NS + "closed_miss_after_take", NS + "ScopeTests.spare_take_entry",
            native.OWNED + "Insertion.Native.CallerSpareSuccessTests.derived_input", native.OWNED + "Insertion.Native.NativeSpareTests.reached_frame"},
        native.OWNED + "Insertion.Native.NativeSpareTests.reached_frame": {NS + "InputFrame.caller"},
        native.OWNED + "insert_post_at": {native.OWNED + "Post", native.OWNED + "handoff", native.OWNED + "graph"},
        native.OWNED + "miss_post_at": {native.OWNED + "insert_post_at", native.OWNED + "Held", native.OWNED + "Good", "Compiler.Extraction.Interner.FindCode.controlMiss"},
        native.OWNED + "Caller.Close.of_post": {native.OWNED + "Caller.Close.taken_verified", native.OWNED + "Post", native.OWNED + "finish"},
        scoped.NS + "close_completion": {scoped.live.NS + "Completion", scoped.live.live.live.live.scope.trace.BRIDGE + "check_physical_sound", scoped.live.TRACE + "Scope.admit_sound"},
        scoped.live.NS + "after_take": {scoped.live.NS + "of_post", scoped.live.NS + "take_success"},
        scoped.live.NS + "miss_after_take": {native.OWNED + "miss_post_at"},
        scoped.NS + "closed_miss_after_take": {scoped.NS + "close_completion"},
    }
    required.update({
        STORAGE_TRACE + "execute_recorded": {STORAGE_TRACE + "record", STORAGE_TRACE + "replay", STORAGE_TRACE + "transport",
            "Compiler.Extraction.Storage.Program.execute", "Compiler.Extraction.Storage.Cleanup.execute"},
        INSERTION + "execution_recorded": {STORAGE_TRACE + "execute_recorded", INSERTION + "execution_observed",
            INSERTION + "observedCalls", INSERTION + "recordExecution", INSERTION + "callbacks"},
        INSERTION + "body_recorded": {INSERTION + "execution_recorded", INSERTION + "checkedExecution_read",
            INSERTION + "body", native.OWNED + "Insertion.projected", native.OWNED + "Insertion.cell"},
        INSERTION + "TraceTests.spare_body": {INSERTION + "body_recorded", INSERTION + "CallerSpareSuccessTests.derived_input",
            INSERTION + "NativeSpareTests.initial_facts"},
        STORAGE_TRACE + "Tests.existing_family": {STORAGE_TRACE + "execute_recorded", "Compiler.Extraction.Storage.ExecutionTests.operations"},
        STORAGE_TRACE + "Tests.cleanup_before_attempt": {STORAGE_TRACE + "record", "Compiler.Extraction.Storage.ExecutionTests.dependentOperations"},
    })
    required.update({
        ACTION + "transaction_verified": {ACTION + "verified", ACTION + "transaction", "Compiler.Extraction.Storage.Program.execute"},
        ACTION + "action_verified": {ACTION + "transaction_verified", ACTION + "action", "Compiler.Extraction.Interner.invariant_observations"},
        INSERTION + "insert_replayed": {INSERTION + "body_recorded", INSERTION + "execution_recorded", ACTION + "action", INSERTION + "insert"},
        INSERTION + "scoped_insert_replayed": {INSERTION + "insert_replayed", "Compiler.Extraction.Interner.Scoped.liftGraph"},
        INSERTION + "insert_replayed_verified": {INSERTION + "insert_replayed", INSERTION + "execution_recorded", ACTION + "action_verified"},
        INSERTION + "TraceTests.spare_scoped_replay": {INSERTION + "scoped_insert_replayed", INSERTION + "TraceTests.spare_header",
            INSERTION + "NativeSpareTests.initial_facts"},
        ACTION + "ActionTests.ordinary_words": {ACTION + "action_verified", STORAGE_TRACE + "Tests.existing_family"},
        INSERTION + "scoped_insert_stream": {INSERTION + "scoped_insert_replayed", INVOCATION + "operations", INVOCATION + "insertions"},
        INSERTION + "initialized_insert_stream": {INSERTION + "scoped_insert_stream", native.OWNED + "Caller.Take.initialized_taken_stream",
            INSERTION + "finished_insert_stream",
            INVOCATION + "resources", INVOCATION + "normalizations", native.OWNED + "Local.slice"},
        native.OWNED + "Caller.Close.transferred_stream": {native.OWNED + "Caller.Close.checked_of_cleanup",
            native.OWNED + "Caller.Close.taken_spec", native.OWNED + "deinit_detached", INVOCATION + "normalizations"},
        INSERTION + "finished_insert_stream": {INSERTION + "scoped_insert_stream", native.OWNED + "finish_handoff",
            native.OWNED + "Caller.Close.transferred_stream", native.OWNED + "Caller.Close.HandoffCompletion", INSERTION + "finishInsertion"},
        INSERTION + "TraceTests.spare_initialized_insert": {INSERTION + "initialized_insert_stream", INSERTION + "TraceTests.spare_header",
            native.OWNED + "Publication.GraphTests.prefix_results", INSERTION + "CallerSpareSuccessTests.derived_input",
            INSERTION + "NativeSpareTests.completed", native.OWNED + "Caller.Close.HandoffCompletion.closed"},
        INVOCATION + "Tests.normalization_foreign": {INVOCATION + "normalizations", scoped.live.live.live.live.scope.trace.TRACE + "replay"},
        INVOCATION + "Tests.insertion_foreign": {INVOCATION + "operations", STORAGE_TRACE + "replay"},
        INVOCATION + "Tests.cleanup_cursor": {ACTION + "action", ACTION + "ActionTests.captured", INVOCATION + "operations"},
        PUBLICATION + "publish_stream": {PUBLICATION + "publish_projection", INVOCATION + "publish_slot", INVOCATION + "publish"},
        PUBLICATION + "closed_publish_stream": {PUBLICATION + "publish_stream", PUBLICATION + "publish_held",
            native.OWNED + "Caller.Close.of_post", native.OWNED + "Caller.ScopeProjection.close_completion"},
        PUBLICATION + "StreamTests.force_closed": {PUBLICATION + "closed_publish_stream", PUBLICATION + "force_after_take",
            PUBLICATION + "OriginTests.derived_input", PUBLICATION + "OriginTests.prefix_results"},
        INVOCATION + "publish_slot": {INVOCATION + "publish", "Compiler.Extraction.Interner.publish"},
        MISS + "routed": {MISS + "selected", "Compiler.Extraction.Interner.FindCode.controlMiss", native.OWNED + "graph", native.OWNED + "handoff"},
        MISS + "finish_map": {native.OWNED + "finish", native.OWNED + "ordinary", native.OWNED + "cleanup"},
        MISS + "inserted": {MISS + "routed", INSERTION + "finished_insert_stream", NS + "context_inserts"},
        MISS + "published": {MISS + "routed", MISS + "finish_map", PUBLICATION + "closed_publish_stream", NS + "context_publishes"},
        MISS + "failed": {MISS + "routed", native.OWNED + "Caller.Close.of_post", native.OWNED + "Caller.ScopeProjection.close_completion"},
        MISS + "Tests.spare_selected": {MISS + "selected", NS + "dispatcher_snapshot", INSERTION + "NativeSpareTests.reached_frame"},
        MISS + "Tests.spare_inserted": {MISS + "inserted", MISS + "Tests.spare_selected", INSERTION + "TraceTests.spare_header", INSERTION + "CallerSpareSuccessTests.derived_input"},
        MISS + "CountedTests.selected_effects": {MISS + "routed", native.OWNED + "Caller.ScopeProjection.Tests.model"},
        MISS + "CountedTests.failed_closed": {MISS + "failed", native.OWNED + "Recursive.PreservationTests.counted_projects", native.OWNED + "Caller.ScopeProjection.Tests.initial"},
        MISS + "selected_preserved": {NS + "simplify_at", NS + "callerContext", NS + "InputFrame", MISS + "selected"},
        MISS + "tail_inputs": {native.OWNED + "Caller.GraphCustody.publication", NS + "InputFrame",
            "Compiler.Extraction.RepresentativeArray.readHeader_items"},
        MISS + "from_children": {MISS + name for name in ("Completion", "selected_preserved", "tail_inputs", "inserted", "published", "failed")},
        MISS + "AdmissionTests.spare_from_children": {MISS + "from_children", INSERTION + "NativeSpareTests.reached_frame",
            INSERTION + "CallerSpareSuccessTests.derived_input"},
        MISS + "AdmissionTests.spare_outcomes": {MISS + "AdmissionTests.spare_from_children", MISS + "Tests.spare_selected",
            NS + "ScopeTests.outcome_children"},
        MISS + "scoped_routed": {"Compiler.Extraction.Interner.FindCode.controlMiss", "Compiler.Extraction.Interner.Scoped.execution"},
        MISS + "scoped_selected": {MISS + "scoped_routed"},
        MISS + "scoped_publish_return": {"Compiler.Extraction.Interner.Scoped.liftGraph", "Compiler.Extraction.Interner.Scoped.handoff"},
        MISS + "projected": {MISS + name for name in ("scoped_selected", "scoped_publish_return", "routed", "segment", "replay", "Projected")},
        MISS + "scoped_from_children": {MISS + "projected", MISS + "from_children", MISS + "selected_preserved"},
        MISS + "ReplayTests.spare_projected": {MISS + "scoped_from_children", MISS + "Tests.spare_selected",
            INSERTION + "NativeSpareTests.reached_frame", NS + "ScopeTests.outcome_children"},
        MISS + "ReplayTests.absent_candidate": {MISS + "replay"},
        MISS + "ReplayTests.counted_routes": {MISS + "scoped_routed", native.OWNED + "Caller.ScopeProjection.Tests.model"},
        native.OWNED + "Caller.Take.initialized_taken_stream": {native.OWNED + "Caller.Take.initialized_stream",
            native.OWNED + "Caller.Close.take_success", native.OWNED + "Caller.Take.checked_scope",
            native.OWNED + "Caller.Initialization.capture_success", INVOCATION + "resources", INVOCATION + "normalizations"},
        MISS + "initialized_from_children": {native.OWNED + "Caller.Take.initialized_taken_stream", MISS + "scoped_from_children",
            MISS + "Completion", MISS + "Projected", MISS + "segment", MISS + "replay"},
        MISS + "InitializedTests.spare_initialized": {MISS + "initialized_from_children", MISS + "Tests.spare_selected",
            INSERTION + "NativeSpareTests.reached_frame", NS + "ScopeTests.outcome_children", native.OWNED + "Publication.GraphTests.prefix_results"},
        CACHE + "scoped_cached": {"Compiler.Extraction.Interner.FindCode.controlRun", "Compiler.Extraction.Interner.Scoped.findDetailed"},
        CACHE + "cached": {CACHE + "scoped_cached", native.OWNED + "Caller.Initialization.successful_stream",
            native.OWNED + "Caller.Initialization.checked_scope", native.OWNED + "Caller.Close.lookup_verified",
            native.OWNED + "Caller.Close.capture_replays_at", native.OWNED + "Caller.find_cached", INVOCATION + "resources"},
        CACHE + "Tests.trace_layout": {CACHE + "Tests.initialization", CACHE + "Tests.close"},
        CACHE + "Tests.existing_family": {CACHE + "cached", CACHE + "Tests.trace_layout",
            native.OWNED + "ConstructorItem.CacheTests.prefix_observed", native.OWNED + "ConstructorItem.prepare_success",
            native.OWNED + "ConstructorItem.good_frame", native.OWNED + "ConstructorItem.CacheTests.poison"},
    })
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError("native scoped dispatch lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return list(dict.fromkeys(checked + sorted(required)))


def insertion_trace_controls(output, env, lean):
    directory = native.ROOT / "lean/Compiler/Extraction"
    parts = [without_imports((directory / (name + ".lean")).read_text()) for name in (
        "StorageExecutionTrace", "StorageExecutionTraceTests", "InternerInsertionNativeTrace", "InsertionExecutionAction",
        "InternerInsertionNativeReplay", "InsertionExecutionActionTests", "InternerInsertionNativeTraceTests")]
    header = ("import Compiler.Extraction.StorageExecutionEffects\n"
              "import Compiler.Extraction.StorageExecutionTests\n"
              "import Compiler.Extraction.InternerScope\n"
              "import Compiler.Extraction.InternerNativeSpareInsertionTests\n")
    def program(chunks):
        return header + "\n".join(chunks)
    variants = []
    for part, name, before, after in (
        (0, "lost-attempt", "before.events ++ [.attempt site owner result]", "before.events"),
        (0, "wrong-site", "before.events ++ [.attempt site owner result]", "before.events ++ [.attempt .item owner result]"),
        (0, "wrong-owner", "before.events ++ [.attempt site owner result]", "before.events ++ [.attempt site {} result]"),
        (0, "wrong-response", "before.events ++ [.attempt site owner result]", "before.events ++ [.attempt site owner (.ok true)]"),
        (0, "lost-effects", "(result, ⟨after, before.events ++ [.attempt", "(result, ⟨before.effects, before.events ++ [.attempt"),
        (0, "lost-history", "before.events ++ [.attempt site owner result]", "[.attempt site owner result]"),
        (0, "lost-release", "before.events ++ [.release action owner result]", "before.events"),
        (0, "wrong-release-owner", "before.events ++ [.release action owner result]", "before.events ++ [.release action {} result]"),
        (0, "unchecked-site", "if site = expected ∧ owner = reached then", "if owner = reached then"),
        (0, "unchecked-owner", "if site = expected ∧ owner = reached then", "if site = expected then"),
        (0, "unchecked-release", "if action = expected ∧ owner = reached then", "if owner = reached then"),
        (0, "unchecked-release-owner", "if action = expected ∧ owner = reached then", "if action = expected then"),
        (0, "rewound-cursor", "if site = expected ∧ owner = reached then (result, cursor + 1)",
         "if site = expected ∧ owner = reached then (result, cursor)"),
        (0, "fault-is-oom", "if site = expected ∧ owner = reached then (result, cursor + 1)",
         "if site = expected ∧ owner = reached then (.ok (result.toOption.getD false), cursor + 1)"),
        (2, "wrong-native-determinism", "insertProgram.execute ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩\n    (Trace.record",
         "insertProgram.execute ⟨!deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩\n    (Trace.record"),
        (2, "wrong-native-arguments", "(Trace.record (observedCalls ops allocate safety allocator container source address meaning input key normalized cells before growth))",
         "(Trace.record (observedCalls ops allocate safety allocator container source address meaning input key { normalized with items := [] } cells before growth))"),
        (2, "stale-projected-owner", "replayed.1.2 captured.2.effects) ∧", "{} captured.2.effects) ∧"),
        (2, "stale-native-effects", "replayed.1.2 captured.2.effects) ∧", "replayed.1.2 (observedStart before)) ∧"),
        (3, "action-lost-owner", "project cells table cell key owner with", "project cells table cell key {} with"),
        (3, "action-lost-cursor", "allocationCursor := reached", "allocationCursor := cursor"),
        (3, "action-fault-is-oom", "| .error _ => .error .safetyFault", "| .error _ => .error .outOfMemory"),
        (3, "action-missing-rows-accepted", "| none => (.error .safetyFault, before)", "| none => (.ok 0, before)"),
        (3, "action-wrong-id", "| .ok outcome => insertionOutcome cells outcome",
         "| .ok outcome => (insertionOutcome cells outcome).map (fun id => id + 1)"),
        (3, "action-wrong-initial-owner", "operations {} cursor\n  let outcome", "operations { appended := true } cursor\n  let outcome"),
        (4, "native-missing-representatives", "(rows : before.graph.representatives = some cells) :", "(rows : True) :"),
        (4, "native-wrong-entry-cursor", "mismatch) { before.graph with allocationCursor := leading.length }",
         "mismatch) { before.graph with allocationCursor := leading.length + 1 }"),
        (4, "native-wrong-end-cursor", "leading.length + captured.2.events.length } ∧\n      actual.2.memory",
         "leading.length } ∧\n      actual.2.memory"),
        (4, "scope-lost-items", "logical.2 = ⟨scope,", "logical.2 = ⟨{ scope with items := [] },"),
        (4, "scope-premature-handoff", "logical.2 = ⟨scope,", "logical.2 = ⟨{ scope with phase := .transfer },"),
        (4, "word-missing-key-binding", "keyCode.run candidate.item candidate.arguments candidate.sequence = some key →", "True →"),
        (4, "word-missing-denotation", "key.eval meaning before.graph.read = some candidate.value →", "True →"),
        (4, "word-unrelated-invariant", "(valid : Interner.Invariant meaning before.graph)",
         "(valid : Interner.Invariant meaning (Interner.observedHeap [] (fun _ => none)))"),
        (4, "word-semantic-fault-accepted",
         "(completed : (execution ops allocate safety allocator container source address meaning input key normalized\n      deterministic cells before growth).1.1 = .ok outcome)", "(completed : True)"),

    ):
        if parts[part].count(before) != 1:
            raise ValueError("ambiguous insertion trace mutation: " + name)
        changed = parts.copy()
        changed[part] = changed[part].replace(before, after)
        variants.append((name, program(changed)))
    records = native.check_controls(output, env, lean, program(parts), variants, prefix="insertion-trace-")
    for record in records:
        if not record["expectedAcceptance"] and not re.search(
                r"error: (?:Not a definitional equality|Application type mismatch|Type mismatch|Tactic[^\n]*failed|unsolved goals)",
                (output / (record["name"] + ".stdout")).read_text()):
            raise ValueError("insertion trace control lacks a semantic proof failure: " + record["name"])
    return records


def invocation_controls(output, env, lean):
    directory = native.ROOT / "lean/Compiler/Extraction"
    parts = [without_imports((directory / (name + ".lean")).read_text()) for name in (
        "InternerInvocationTrace", "InternerInvocationTraceTests", "InternerInvocationClose",
        "InternerInsertionInvocation", "InternerInsertionInvocationTests",
        "InternerPublicationInvocation", "InternerPublicationInvocationTests", "InternerCallerTakenStream")]
    header = ("import Compiler.Extraction.InternerInsertionNativeTraceTests\n"
              "import Compiler.Extraction.InternerCallerTakeStream\n"
              "import Compiler.Extraction.InternerCallerCloseTake\n"
              "import Compiler.Extraction.InternerCallerInsertionCapacityCompletion\n"
              "import Compiler.Extraction.InternerCallerScopedClose\n"
              "import Compiler.Extraction.InternerCallerPublicationCompletionTests\n")
    def program(chunks):
        return header + "\n".join(chunks[:3] + [chunks[7]] + chunks[3:7])
    variants = []
    for part, name, before, after in (
        (7, "prefix-stale-memory", "let taken := capture external allocator lookup.origin handle prepared.world.memory",
         "let taken := capture external allocator lookup.origin handle before.memory"),
        (7, "prefix-reordered", "leading ++ initialization.2.events.map Event.normalization ++ taken.2.events.map Event.normalization",
         "leading ++ taken.2.events.map Event.normalization ++ initialization.2.events.map Event.normalization"),
        (7, "prefix-attached-handle", "some remaining, some slice, false", "some handle, some slice, false"),
        (7, "prefix-owned-token", "taken.1.2.owned = false", "taken.1.2.owned = true"),
        (7, "prefix-lookup-owner", "taken.1.2.owner = .caller", "taken.1.2.owner = .lookup"),
        (7, "prefix-early-handoff", "remaining.values, .cleanup", "remaining.values, .transfer"),
        (7, "prefix-stale-cursor", "allocationCursor := missLeading.length", "allocationCursor := leading.length"),
        (7, "prefix-oom-as-success", "takeScope.1 = .ok () ∧", "takeScope.1 = .error .outOfMemory ∧"),
        (0, "normalization-accepts-insertion", "| .insertion _ => .foreign", "| .insertion _ => .allocate .temporary true"),
        (0, "insertion-accepts-normalization", "| .normalization _ => .foreign", "| .normalization _ => .attempt .arguments {} (.ok true)"),
        (0, "normalization-drops-slots", "events.map normalization",
         "events.filterMap (fun event => match event with | .normalization call => some call | .insertion _ => none)"),
        (0, "insertion-drops-slots", "events.map insertion",
         "events.filterMap (fun event => match event with | .insertion call => some call | .normalization _ => none)"),
        (0, "normalization-reversed", "Scope.resources (normalizations events) mismatch", "Scope.resources (normalizations events.reverse) mismatch"),
        (0, "insertion-reversed", "Storage.Trace.replay (insertions events) mismatch", "Storage.Trace.replay (insertions events.reverse) mismatch"),
        (3, "unbound-initializer",
         "⟨{ before with memory := { before.memory with memory := stack } }, { lookup := none }⟩ = (.ok values, prepared))",
         "⟨{ before with memory := { before.memory with memory := stack } }, { lookup := none }⟩ = (.ok values, { prepared with scope := { lookup := none } }))"),
        (3, "unbound-take", "(transferred : OwnedCall.take external allocator prepared = (.ok (), called))",
         "(transferred : (OwnedCall.take external allocator prepared).1 = .ok ())"),
        (3, "unbound-slice", "(selectedSlice : called.scope.slice = some normalized)", "(selectedSlice : True)"),
        (3, "stale-take-memory", "let taken := Caller.Take.capture external allocator lookup.origin handle prepared.world.memory",
         "let taken := Caller.Take.capture external allocator lookup.origin handle before.memory"),
        (3, "lost-initialization", "let insertionLeading := leading ++ initialization.2.events.map Event.normalization ++ taken.2.events.map Event.normalization",
         "let insertionLeading := leading ++ taken.2.events.map Event.normalization"),
        (3, "lost-take", "let insertionLeading := leading ++ initialization.2.events.map Event.normalization ++ taken.2.events.map Event.normalization",
         "let insertionLeading := leading ++ initialization.2.events.map Event.normalization"),
        (3, "reordered-prefix", "let insertionLeading := leading ++ initialization.2.events.map Event.normalization ++ taken.2.events.map Event.normalization",
         "let insertionLeading := leading ++ taken.2.events.map Event.normalization ++ initialization.2.events.map Event.normalization"),
        (3, "stale-insertion-entry", "let logical := Interner.Scoped.liftGraph action takeScope.2",
         "let logical := Interner.Scoped.liftGraph action initialScope.2"),
        (3, "stale-insertion-capture", "deterministic cells called.world growth []", "deterministic cells before growth []"),
        (3, "wrong-ending-cursor", "allocationCursor := insertionLeading.length + captured.2.events.length",
         "allocationCursor := insertionLeading.length"),
        (3, "premature-transfer", "logical.2 = ⟨takeScope.2.scope,", "logical.2 = ⟨{ takeScope.2.scope with phase := .transfer },"),
        (3, "missing-representatives", "(rows : called.world.graph.representatives = some cells)", "(rows : True)"),
        (2, "close-owned-handle", "(detached : handle.owned = none)", "(detached : True)"),
        (2, "close-owned-token", "(unowned : lookup.owned = false)", "(unowned : True)"),
        (2, "close-stale-cursor", "{ world.graph with allocationCursor := leading.length }",
         "{ world.graph with allocationCursor := 0 }"),
        (2, "close-lost-handoff", "let before : OwnedCall.State σ := ⟨world, ⟨some handle, some slice, true⟩⟩",
         "let before : OwnedCall.State σ := ⟨world, ⟨some handle, some slice, false⟩⟩"),
        (2, "semantic-exit-unwound", "else (actual.1, ⟨actual.2, ⟨some handle, some slice, true⟩⟩)",
         "else (actual.1, ⟨actual.2, ⟨none, some slice, true⟩⟩)"),
        (2, "oom-not-closed", "if ordinary actual.1 then",
         "if (match actual.1 with | .ok _ => true | .error _ => false) then"),
        (3, "close-lost-insertion", "let closeLeading := leading ++ captured.2.events.map Event.insertion",
         "let closeLeading := leading"),
        (3, "insertion-without-handoff", "let logical := (do Interner.Scoped.handoff; Interner.Scoped.liftGraph action)",
         "let logical := Interner.Scoped.liftGraph action"),
        (3, "finish-stale-caller", "input key deterministic called growth)", "input key deterministic prepared growth)"),
        (3, "finish-initial-token", "allocator taken.1.2 remaining normalized", "allocator lookup remaining normalized"),
        (0, "publication-mismatch-is-oom", "let rejected := (.error .safetyFault,", "let rejected := (.error .outOfMemory,"),
        (0, "publication-ignores-key", "if queried = key then", "if true then"),
        (0, "publication-reverses-decision", "Interner.publish accepted key id before", "Interner.publish (!accepted) key id before"),
        (0, "publication-writes-wrong-id", "Interner.publish accepted key id before", "Interner.publish accepted key (id + 1) before"),
        (0, "publication-stale-cursor", "allocationCursor := before.allocationCursor + 1", "allocationCursor := before.allocationCursor"),
        (5, "publication-stale-probe", "hostProbe key (forget before.memory)",
         "hostProbe { key with sequence := key.sequence + 1 } (forget before.memory)"),
        (5, "publication-missing-validity", "(valid : Valid before.memory)", "(valid : True)"),
        (5, "publication-missing-admission", "(valid : Valid before.memory) (input : Input allocator source key owned before)",
         "(valid : Valid before.memory) (input : True)"),
        (5, "publication-dead-incoming", "(live : SliceValid allocator before.memory.heap owned)", "(live : True)"),
        (5, "publication-missing-held", "(held : Held allocator source values owned before)", "(held : True)"),
        (5, "publication-handoff-on-oom", "body.1 = actual.1 ∧ body.2 = ⟨actual.2, ⟨some handle, some owned, response.1⟩⟩",
         "body.1 = actual.1 ∧ body.2 = ⟨actual.2, ⟨some handle, some owned, true⟩⟩"),
        (5, "publication-no-handoff", "; handoff : Action (Effects σ) Unit", "; pure () : Action (Effects σ) Unit"),
        (5, "publication-close-before-probe", "let closeLeading := leading ++ [.publicationProbe key response.1]", "let closeLeading := leading"),
        (5, "publication-lost-close-events", "let events := closeLeading ++ close.2.events.map Event.normalization ++ trailing",
         "let events := closeLeading ++ trailing"),
        (5, "publication-close-stale-memory", "let close := Caller.Close.capture (external host) allocator lookup phase handle body.2",
         "let close := Caller.Close.capture (external host) allocator lookup phase handle ⟨before, ⟨some handle, some owned, false⟩⟩"),
        (5, "publication-owned-token", "(unowned : lookup.owned = false)", "(unowned : True)"),
        (5, "publication-attached-handle", "(detached : handle.owned = none)", "(detached : True)"),
    ):
        expected = 2 if name in {"publication-reverses-decision", "publication-writes-wrong-id", "publication-stale-probe"} else 1
        if parts[part].count(before) != expected:
            raise ValueError("ambiguous invocation trace mutation: " + name)
        changed = parts.copy()
        changed[part] = changed[part].replace(before, after)
        variants.append((name, program(changed)))
    records = native.check_controls(output, env, lean, program(parts), variants, prefix="invocation-trace-")
    for record in records:
        if not record["expectedAcceptance"] and not re.search(
                r"error: (?:Not a definitional equality|Application type mismatch|Type mismatch|Tactic[^\n]*failed|unsolved goals)",
                (output / (record["name"] + ".stdout")).read_text()):
            raise ValueError("invocation trace control lacks a semantic proof failure: " + record["name"])
    return records


def miss_controls(output, env, lean):
    directory = native.ROOT / "lean/Compiler/Extraction"
    source = "\n".join(without_imports((directory / (name + ".lean")).read_text()) for name in (
        "InternerMissInvocation", "InternerMissInvocationTests"))
    header = ("import Compiler.Extraction.InternerInsertionInvocationTests\n"
              "import Compiler.Extraction.InternerPublicationInvocation\n"
              "import Compiler.Extraction.InternerCallerRecursionEffects\n"
              "import Compiler.Extraction.InternerNativeScopedDispatchTests\n")
    variants = []
    for name, before, after, count in (
        ("ignores-determinism", "if deterministic && request.item.kind == 1 then", "if request.item.kind == 1 then", 1),
        ("ignores-kind", "if deterministic && request.item.kind == 1 then", "if deterministic then", 1),
        ("dispatches-skipped", "else (.ok none, before)", "else physical.simplify key slice before", 1),
        ("loses-dispatch-effects", "then physical.simplify key slice before else", "then ((physical.simplify key slice before).1, before) else", 1),
        ("error-rewinds-world", "| .error fault => (.error fault, { before with world := decision.2 })",
         "| .error fault => (.error fault, before)", 1),
        ("insertion-late-handoff", "| .ok none => (do handoff; graph (fun owned => physical.insert key owned deterministic))",
         "| .ok none => (do let id ← graph (fun owned => physical.insert key owned deterministic); handoff; pure id)", 1),
        ("publication-early-handoff", "(do let _ ← graph (fun owned => physical.publish key owned id); handoff; pure id)",
         "(do handoff; let _ ← graph (fun owned => physical.publish key owned id); pure id)", 1),
        ("publication-wrong-id", "physical.publish key owned id", "physical.publish key owned (id + 1)", 1),
        ("wrong-return-id", "(do let _ ← graph (fun owned => physical.publish key owned id); handoff; pure id)",
         "(do let _ ← graph (fun owned => physical.publish key owned id); handoff; pure (id + 1))", 1),
        ("insertion-stale-capture", "key slice deterministic cells reached growth []", "key slice deterministic cells before growth []", 1),
        ("insertion-wrong-classification", "key slice deterministic cells reached growth []", "key slice (!deterministic) cells reached growth []", 1),
        ("publication-stale-probe", "ops.probe key (Publication.forget reached.memory)", "ops.probe key (Publication.forget before.memory)", 1),
        ("publication-wrong-replay-id", "Interner.InvocationTrace.publish events key id", "Interner.InvocationTrace.publish events key (id + 1)", 1),
        ("publication-wrong-final-id", "actual = (tail.1.map (fun _ => id), tail.2) ∧", "actual = (tail.1.map (fun _ => id + 1), tail.2) ∧", 1),
        ("failed-stale-world", "actual = (.error fault, ⟨reached, ⟨some handle, some slice, false⟩⟩) ∧",
         "actual = (.error fault, ⟨before, ⟨some handle, some slice, false⟩⟩) ∧", 1),
        ("failed-stale-close", "let close := Caller.Close.capture external allocator lookup .cleanup handle actual.2",
         "let close := Caller.Close.capture external allocator lookup .cleanup handle ⟨before, ⟨some handle, some slice, false⟩⟩", 1),
        ("failed-semantic-close", "(ordinary actual.1 = true → ∃ after, finish external allocator", "(ordinary actual.1 = false → ∃ after, finish external allocator", 1),
        ("failed-transfer-close", "let close := Caller.Close.capture external allocator lookup .cleanup handle actual.2",
         "let close := Caller.Close.capture external allocator lookup .transfer handle actual.2", 1),
        ("attached-handle", "(detached : handle.owned = none)", "(detached : True)", 3),
        ("owned-token", "(unowned : lookup.owned = false)", "(unowned : True)", 3),
    ):
        if source.count(before) != count:
            raise ValueError("ambiguous miss routing mutation: " + name)
        variants.append((name, header + source.replace(before, after)))
    records = native.check_controls(output, env, lean, header + source, variants, prefix="miss-routing-")
    for record in records:
        if not record["expectedAcceptance"] and not re.search(
                r"error: (?:Not a definitional equality|Application type mismatch|Type mismatch|Tactic[^\n]*failed|unsolved goals)",
                (output / (record["name"] + ".stdout")).read_text()):
            raise ValueError("miss routing control lacks a semantic proof failure: " + record["name"])
    return records


def admission_controls(output, env, lean):
    directory = native.ROOT / "lean/Compiler/Extraction"
    source = "\n".join(without_imports((directory / (name + ".lean")).read_text()) for name in (
        "InternerMissAdmission", "InternerMissAdmissionTests"))
    header = ("import Compiler.Extraction.InternerMissInvocationTests\n"
              "import Compiler.Extraction.InternerNativeScopedDispatch\n")
    variants = []
    for name, before, after, count in (
        ("wrong-dispatch-owner", "let p := physical ops allocate safety owner meaning base growth owner usizeBits children debug source address input",
         "let p := physical ops allocate safety owner meaning base growth (owner + 1) usizeBits children debug source address input", 2),
        ("stale-reached-frame", "originalRows source values slice decision.2)", "originalRows source values slice before)", 2),
        ("lost-appended-rows", "⟨added ++ later, backing, bound,", "⟨added, backing, bound,", 1),
        ("reversed-row-extension", "⟨added ++ later, backing, bound,", "⟨later ++ added, backing, bound,", 1),
        ("semantic-frame-claim", "ordinary decision.1 = true →", "ordinary decision.1 = false →", 2),
        ("wrong-logical-guard", "let logical := if deterministic && request.item.kind == 1 then",
         "let logical := if deterministic then", 1),
        ("missing-child-frame", "InputFrame safety base.allocator owner rows source values slice world)).SourceConstructorsAt",
         "True)).SourceConstructorsAt", 2),
        ("missing-child-predicate", "fun world => predicate world ∧\n      InputFrame",
         "fun world => True ∧\n      InputFrame", 2),
        ("wrong-input-alignment", "(aligned : key.arguments = slice.items)", "(aligned : key.arguments = [])", 4),
        ("wrong-header-owner", "readItems world.memory.memory (Owner.headerAddress ⟨owner, 0⟩)",
         "readItems world.memory.memory (Owner.headerAddress ⟨owner + 1, 0⟩)", 1),
        ("wrong-publication-allocator", "∧ Publication.Input allocator source key slice world ∧",
         "∧ Publication.Input (allocator + 1) source key slice world ∧", 1),
        ("wrong-reached-rows", "world.graph.representatives = some cells := by",
         "world.graph.representatives = some originalRows := by", 1),
        ("wrong-selected-id", "request key slice deterministic before handle lookup values id leading trailing\n",
         "request key slice deterministic before handle lookup values (id + 1) leading trailing\n", 1),
        ("owned-close-token", "(unowned : lookup.owned = false)", "(unowned : lookup.owned = true)", 2),
    ):
        if source.count(before) != count:
            raise ValueError("ambiguous miss admission mutation: " + name)
        variants.append((name, header + source.replace(before, after)))
    records = native.check_controls(output, env, lean, header + source, variants, prefix="miss-admission-")
    for record in records:
        if not record["expectedAcceptance"] and not re.search(
                r"error: (?:Not a definitional equality|Application type mismatch|Type mismatch|Tactic[^\n]*failed|unsolved goals)",
                (output / (record["name"] + ".stdout")).read_text()):
            raise ValueError("miss admission control lacks a semantic proof failure: " + record["name"])
    return records


def replay_controls(output, env, lean):
    directory = native.ROOT / "lean/Compiler/Extraction"
    source = "\n".join(without_imports((directory / (name + ".lean")).read_text()) for name in (
        "InternerMissReplay", "InternerMissReplayTests"))
    header = "import Compiler.Extraction.InternerMissAdmissionTests\n"
    variants = []
    for name, before, after, count in (
        ("scoped-wrong-guard", "let decision := if deterministic && request.item.kind == 1 then",
         "let decision := if deterministic then", 1),
        ("scoped-late-handoff", "| .ok none => (do Interner.Scoped.handoff; Interner.Scoped.liftGraph (model.insert key deterministic))",
         "| .ok none => (do let id ← Interner.Scoped.liftGraph (model.insert key deterministic); Interner.Scoped.handoff; pure id)", 1),
        ("scoped-wrong-id", "Interner.Scoped.liftGraph (model.publish key id)", "Interner.Scoped.liftGraph (model.publish key (id + 1))", 2),
        ("scoped-stale-error", "| .error fault => (.error fault, { before with heap := decision.2 })",
         "| .error fault => (.error fault, before)", 1),
        ("unbound-publication", "publish := Interner.InvocationTrace.publish events", "publish := seed.publish", 1),
        ("unbound-insertion", "| some cell => Interner.InsertionExecution.action cell key deterministic (operations events mismatch)",
         "| some cell => seed.insert key deterministic", 1),
        ("missing-candidate-is-oom", "| none => fun before => (.error .safetyFault, before)",
         "| none => fun before => (.error .outOfMemory, before)", 1),
        ("discarded-native-rows", "let cells := reached.graph.representatives.getD []", "let cells : List Storage.Cell := []", 1),
        ("stale-insertion-world", "key slice deterministic cells reached growth []", "key slice deterministic cells before growth []", 1),
        ("wrong-insertion-classification", "key slice deterministic cells reached growth []", "key slice (!deterministic) cells reached growth []", 1),
        ("lost-insertion-events", "⟨captured.2.events.map Event.insertion, [], some candidate, .transfer⟩",
         "⟨[], [], some candidate, .transfer⟩", 1),
        ("stale-publication-probe", "ops.probe key (Publication.forget reached.memory)", "ops.probe key (Publication.forget before.memory)", 1),
        ("lost-publication-cleanup", "close.2.events.map Event.normalization, none, phase⟩", "[], none, phase⟩", 1),
        ("cleanup-before-body", "let events := leading ++ observed.body ++ observed.cleanup ++ trailing",
         "let events := leading ++ observed.cleanup ++ observed.body ++ trailing", 1),
        ("return-cursor-after-close", "allocationCursor := (leading ++ observed.body).length",
         "allocationCursor := (leading ++ observed.body ++ observed.cleanup).length", 2),
        ("semantic-close", "(ordinary actual.1 = true →", "(ordinary actual.1 = false →", 1),
        ("forced-transfer-close", "lookup observed.phase handle actual.2", "lookup .transfer handle actual.2", 1),
        ("wrong-dispatch-boundary", "request key slice deterministic before).2 = leading.length →",
         "request key slice deterministic before).2 = (leading ++ trailing).length →", 1),
        ("wrong-return-id", "(tail.1.map (fun _ => id), tail.2)", "(tail.1.map (fun _ => id + 1), tail.2)", 1),
    ):
        if source.count(before) != count:
            raise ValueError("ambiguous miss replay mutation: " + name)
        variants.append((name, header + source.replace(before, after)))
    records = native.check_controls(output, env, lean, header + source, variants, prefix="miss-replay-")
    for record in records:
        if not record["expectedAcceptance"] and not re.search(
                r"error: (?:Not a definitional equality|Application type mismatch|Type mismatch|Tactic[^\n]*failed|unsolved goals)",
                (output / (record["name"] + ".stdout")).read_text()):
            raise ValueError("miss replay control lacks a semantic proof failure: " + record["name"])
    return records


def initialized_miss_controls(output, env, lean):
    directory = native.ROOT / "lean/Compiler/Extraction"
    parts = [without_imports((directory / (name + ".lean")).read_text()) for name in (
        "InternerMissInitialized", "InternerMissInitializedTests")]
    header = "import Compiler.Extraction.InternerMissReplayTests\n"
    source = header + "\n".join(parts)
    variants = []
    for name, before, after, count in (
        ("unbound-initialization", "(.ok values, prepared))", "(.ok values, { prepared with scope := { lookup := none } }))", 1),
        ("unbound-take", "base.allocator prepared = (.ok (), called))", "base.allocator prepared = (.error (.language .outOfMemory), called))", 1),
        ("wrong-source-values", "slice.items = values ∧", "slice.items = request.arguments ∧", 1),
        ("stale-token", "remaining taken.1.2", "remaining lookup", 3),
        ("missing-middle", "let tailLeading := missLeading ++ middle", "let tailLeading := missLeading", 1),
        ("wrong-suffix-order", "let events := tailLeading ++ observed.body ++ observed.cleanup ++ trailing",
         "let events := tailLeading ++ observed.cleanup ++ observed.body ++ trailing", 1),
        ("stale-miss-entry", "request key deterministic takeScope.2", "request key deterministic initialScope.2", 1),
        ("seed-ports", "(replay seed events observed.candidate mismatch)", "seed", 1),
        ("wrong-entry-boundary", "cursor called.world = missLeading.length", "cursor called.world = leading.length", 1),
        ("wrong-child-boundary", "cursor decision.2 = tailLeading.length", "cursor decision.2 = missLeading.length", 1),
        ("stale-native-state", "request key deterministic called", "request key deterministic prepared", 1),
        ("close-before-body", "normalizations (tailLeading ++ observed.body)", "normalizations tailLeading", 1),
        ("semantic-close", "(ordinary actual.1 = true →", "(ordinary actual.1 = false →", 1),
    ):
        if parts[0].count(before) != count:
            raise ValueError("ambiguous initialized miss mutation: " + name)
        variants.append((name, header + parts[0].replace(before, after) + "\n" + parts[1]))
    records = native.check_controls(output, env, lean, source, variants, prefix="initialized-miss-")
    for record in records:
        if not record["expectedAcceptance"] and not re.search(
                r"error: (?:Not a definitional equality|Application type mismatch|Type mismatch|Tactic[^\n]*failed|unsolved goals)",
                (output / (record["name"] + ".stdout")).read_text()):
            raise ValueError("initialized miss control lacks a semantic proof failure: " + record["name"])
    return records


def cache_stream_controls(output, env, lean):
    directory = native.ROOT / "lean/Compiler/Extraction"
    parts = [without_imports((directory / (name + ".lean")).read_text()).replace(
        "successful_stream", "cache_mutation_successful_stream").replace("Caller.CacheStream", "Caller.CacheStreamMutation")
        for name in ("InternerCallerInitializedStream", "InternerCallerCacheStream")]
    def program(parts):
        return "import Compiler.Extraction.InternerCallerCacheStreamTests\n" + "\n".join(parts)
    variants = []
    for name, index, before, after, count in (
        ("unbound-stack", 0,
         "(allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))",
         "(allocated : True)", 1),
        ("unadmitted-host", 0, "(admitted : Admitted external)", "(admitted : True)", 1),
        ("stale-initial-state", 0, "prepared = ⟨⟨before.graph, execution.2.effects.session⟩",
         "prepared = ⟨⟨before.graph, before.memory⟩", 1),
        ("lost-init-cursor", 0, "(leading.length + execution.2.events.length)", "leading.length", 1),
        ("unbound-cache-hit", 1, "(found : before.graph.table key = some id)", "(found : True)", 1),
        ("wrong-key-values", 1, "(made : Interner.makeKey request values = .ok key)",
         "(made : Interner.makeKey request request.arguments = .ok key)", 2),
        ("wrong-capacity-input", 1,
         "(capacityQuery : model.atCapacity { before.graph with allocationCursor := leading.length } = q.atCapacity before.graph)",
         "(capacityQuery : model.atCapacity before.graph = q.atCapacity before.graph)", 1),
        ("wrong-classification-result", 1, "(classificationQuery : model.deterministic request.item = q.deterministic request.item)",
         "(classificationQuery : model.deterministic request.item = .ok false)", 1),
        ("stale-cleanup-handle", 1, "let handle := initialization.2.effects.handle",
         "let handle : Handle := ⟨source, request.arguments, none⟩", 1),
        ("missing-initialization", 1, "let closeLeading := leading ++ initialization.2.events.map Event.normalization",
         "let closeLeading := leading", 1),
        ("missing-cleanup", 1, "let events := closeLeading ++ close.2.events.map Event.normalization ++ trailing",
         "let events := closeLeading ++ trailing", 1),
        ("reordered-cleanup", 1, "let events := closeLeading ++ close.2.events.map Event.normalization ++ trailing",
         "let events := close.2.events.map Event.normalization ++ closeLeading ++ trailing", 1),
        ("stale-close-cursor", 1, "Close.checked close (normalizations closeLeading)",
         "Close.checked close (normalizations leading)", 1),
        ("stale-reached-memory", 1, "after.world.memory = close.2.effects.session", "after.world.memory = before.memory", 1),
        ("wrong-return", 1, "logical.1 = .ok id", "logical.1 = .ok (id + 1)", 1),
        ("wrong-scope-phase", 1, "logical.2 = ⟨⟨some close.1, values, .lookup⟩",
         "logical.2 = ⟨⟨some close.1, values, .transfer⟩", 2),
        ("lost-close-cursor", 1, "(closeLeading ++ close.2.events.map Event.normalization).length",
         "closeLeading.length", 1),
    ):
        if parts[index].count(before) != count:
            raise ValueError("ambiguous cache stream mutation: " + name)
        changed = parts.copy()
        changed[index] = changed[index].replace(before, after)
        variants.append((name, program(changed)))
    records = native.check_controls(output, env, lean, program(parts), variants, prefix="cache-stream-")
    for record in records:
        if not record["expectedAcceptance"] and not re.search(
                r"error: (?:Not a definitional equality|Application type mismatch|Type mismatch|Tactic[^\n]*failed|unsolved goals)",
                (output / (record["name"] + ".stdout")).read_text()):
            raise ValueError("cache stream control lacks a semantic proof failure: " + record["name"])
    return records


def source_parts():
    directory = native.ROOT / "lean/Compiler/Extraction"
    return [without_imports((directory / (name + ".lean")).read_text()).replace(
        "ConstructorItem.NativeRecursion", "ConstructorItem.NativeRecursion.ScopedDispatchMutation")
        for name in ("InternerNativeScopedDispatch", "InternerNativeScopedClose", "InternerNativeScopedTake", "InternerNativeScopedDispatchTests",
            "InternerNativeScopedStream", "InternerNativeScopedStreamTests")]


def stream_variants(parts):
    variants = []
    for name, before, after in (
        ("stream-missing-validity", "(valid : Valid before.memory)", "(valid : True)"),
        ("stream-missing-stack", "(allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))",
         "(allocated : True)"),
        ("stream-unbound-initializer",
         "(initialized : Caller.initLookup base.external budget base.allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request\n      ⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))",
         "(initialized : (Caller.initLookup base.external budget base.allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request\n      ⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩).1 = .ok values)"),
        ("stream-unbound-take", "(transferred : OwnedCall.take base.external base.allocator prepared = (.ok (), called))",
         "(transferred : (OwnedCall.take base.external base.allocator prepared).1 = .ok ())"),
        ("stream-stale-take-memory", "let taken := Caller.Take.capture base.external base.allocator lookup.origin handle prepared.world.memory",
         "let taken := Caller.Take.capture base.external base.allocator lookup.origin handle before.memory"),
        ("stream-wrong-origin", "let taken := Caller.Take.capture base.external base.allocator lookup.origin handle prepared.world.memory",
         "let taken := Caller.Take.capture base.external base.allocator .input handle prepared.world.memory"),
        ("stream-initial-cleanup-token", "let cleanup := Caller.Close.capture base.external base.allocator taken.1.2 phase remaining body.2",
         "let cleanup := Caller.Close.capture base.external base.allocator lookup phase remaining body.2"),
        ("stream-initial-cleanup-handle", "let cleanup := Caller.Close.capture base.external base.allocator taken.1.2 phase remaining body.2",
         "let cleanup := Caller.Close.capture base.external base.allocator taken.1.2 phase handle body.2"),
        ("stream-lost-initialization", "let takeLeading := leading ++ initialization.2.events", "let takeLeading := leading"),
        ("stream-lost-take", "let closeLeading := takeLeading ++ (taken.2.events ++ middle)", "let closeLeading := takeLeading ++ middle"),
        ("stream-lost-graph-segment", "let closeLeading := takeLeading ++ (taken.2.events ++ middle)",
         "let closeLeading := takeLeading ++ taken.2.events"),
        ("stream-reordered-segments", "let closeLeading := takeLeading ++ (taken.2.events ++ middle)",
         "let closeLeading := takeLeading ++ (middle ++ taken.2.events)"),
        ("stream-stale-miss-entry", "request key deterministic takeScope.2", "request key deterministic initialScope.2"),
        ("stream-unbound-entry-cursor", "cursor called.world = takeLeading.length + taken.2.events.length →", "True →"),
        ("stream-unbound-close-cursor", "cursor body.2.world = closeLeading.length →", "True →"),
        ("stream-semantic-exit", "ordinary body.1 = true → cursor called.world", "True → cursor called.world"),
    ):
        if parts[4].count(before) != 1:
            raise ValueError("ambiguous native stream mutation: " + name)
        changed = parts.copy()
        changed[4] = changed[4].replace(before, after)
        variants.append((name, "import " + MODULE + "\n" + "\n".join(changed)))
    return variants


def controls(output, env, lean):
    records = scoped.controls(output, env, lean)
    parts = source_parts()
    def program(parts):
        return "import " + MODULE + "\n" + "\n".join(parts)
    variants = []
    for name, before, after, count in (
        ("rewound-model-cursor", "key.arguments debug before }", "key.arguments debug { before with allocationCursor := 0 } }", 1),
        ("wrong-model-opcode", "children usizeBits key.instruction key.arguments debug before }", "children usizeBits (key.instruction + 1) key.arguments debug before }", 1),
        ("wrong-model-width", "children usizeBits key.instruction key.arguments debug before }", "children (usizeBits + 1) key.instruction key.arguments debug before }", 1),
        ("missing-alignment", "(aligned : key.arguments = normalized.items)", "(aligned : True)", 3),
        ("missing-held-input", "(held : Held base.allocator source values normalized before)", "(held : True)", 1),
        ("missing-custody", "(custody : Caller.GraphCustody base.allocator normalized rows before.memory)", "(custody : True)", 1),
        ("missing-source-privacy", "(privateSource : Caller.SourcePrivate source before.memory.effects.keys)", "(privateSource : True)", 1),
        ("missing-initial-invariant", "(initial : predicate before)", "(initial : True)", 1),
        ("missing-proper-children", "(coupled : (projectionAt (cursorGraph cursor) (fun world => predicate world ∧\n      InputFrame safety base.allocator owner rows source values normalized world)).SourceConstructorsAt (Nested.storageReads rows) debug children model)", "(coupled : True)", 2),
        ("semantic-exit-projection", "ordinary executed.1 = true →", "True →", 3),
        ("wrong-native-owner", "(facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)", "(facts : NativeGraph.Facts safety base.allocator (owner + 1) data capacity before rows)", 1),
        ("wrong-child-snapshot", "InputFrame safety base.allocator owner rows source values normalized world)).SourceConstructorsAt", "InputFrame safety base.allocator owner [] source values normalized world)).SourceConstructorsAt", 3),
        ("stale-entry-snapshot", "(originalRows ++ added) before predicate", "originalRows before predicate", 1),
        ("stale-child-snapshot", "(coupled (originalRows ++ added)) publishes inserts", "(coupled originalRows) publishes inserts", 1),
    ):
        if parts[0].count(before) != count:
            raise ValueError("ambiguous native scoped dispatch mutation: " + name)
        changed = parts.copy()
        changed[0] = changed[0].replace(before, after)
        variants.append((name, program(changed)))
    for name, before, after in (
        ("close-owned-lookup", "(detached : handle.owned = none)", "(detached : True)"),
        ("close-owned-token", "(unowned : lookup.owned = false)", "(unowned : True)"),
        ("close-wrong-owner", "(caller : lookup.owner = .caller)", "(caller : True)"),
        ("close-lost-entry-phase", "(locals : before.scope = ⟨some handle, some normalized, false⟩)",
         "(locals : before.scope = ⟨some handle, some normalized, true⟩)"),
        ("close-missing-input-frame", "(input : InputFrame safety base.allocator owner originalRows source values normalized before.world)",
         "(input : True)"),
        ("close-wrong-publication-id", "(seed.publish key id))", "(seed.publish key (id + 1)))"),
        ("close-wrong-insert-branch", "(seed.insert key deterministic))", "(seed.insert key (!deterministic)))"),
        ("close-publication-lifetime", "(∀ fault, ((base.primitives source address native).publish key normalized id world).1 = .error fault →\n          SliceValid base.allocator ((base.primitives source address native).publish key normalized id world).2.memory.heap normalized)",
         "True"),
        ("close-insertion-lifetime", "Good source values ((base.primitives source address native).insert key normalized deterministic world).2)", "True)"),
        ("close-semantic-exit", "ordinary body.1 = true → cursor body.2.world = leading.length →", "True → cursor body.2.world = leading.length →"),
        ("close-unbound-cursor", "ordinary body.1 = true → cursor body.2.world = leading.length →", "ordinary body.1 = true → True →"),
        ("close-stale-native-state", "OwnedCall.finish base.external base.allocator body.1 body.2 =", "OwnedCall.finish base.external base.allocator body.1 before ="),
        ("close-stale-scoped-state", ".ok (Interner.Scoped.close resources logical.2)",
         ".ok (Interner.Scoped.close resources (Caller.ScopeProjection.scopeAt (cursorGraph cursor) lookup handle.values before))"),
    ):
        if parts[1].count(before) != 1:
            raise ValueError("ambiguous native scoped close mutation: " + name)
        changed = parts.copy()
        changed[1] = changed[1].replace(before, after)
        variants.append((name, program(changed)))
    for name, before, after in (
        ("take-missing-readiness", "(ready : Ready base.allocator source values handle before.memory)", "(ready : True)"),
        ("take-missing-host-contract", "(admitted : Admitted base.external)", "(admitted : True)"),
        ("take-unbound-reached-state",
         "(transferred : OwnedCall.take base.external base.allocator ⟨before, { lookup := some handle }⟩ = (.ok (), called))",
         "(transferred : (OwnedCall.take base.external base.allocator ⟨before, { lookup := some handle }⟩).1 = .ok ())"),
        ("take-missing-locals", "(locals : called.scope = ⟨some remaining, some normalized, false⟩)", "(locals : True)"),
        ("take-missing-alignment", "(aligned : key.arguments = handle.values)", "(aligned : True)"),
        ("take-initial-token", "let lookup := (Caller.Take.capture base.external base.allocator origin handle before.memory).1.2",
         "let lookup := token origin handle"),
        ("take-wrong-recording-memory", "let lookup := (Caller.Take.capture base.external base.allocator origin handle before.memory).1.2",
         "let lookup := (Caller.Take.capture base.external base.allocator origin handle called.world.memory).1.2"),
        ("take-wrong-recording-handle", "let lookup := (Caller.Take.capture base.external base.allocator origin handle before.memory).1.2",
         "let lookup := (Caller.Take.capture base.external base.allocator origin remaining before.memory).1.2"),
        ("take-stale-postcondition", "Normalization.Taken base.allocator source values handle before.memory normalized remaining called.world.memory ∧",
         "Normalization.Taken base.allocator source values handle before.memory normalized remaining before.memory ∧"),
    ):
        if parts[2].count(before) != 1:
            raise ValueError("ambiguous native scoped take mutation: " + name)
        changed = parts.copy()
        changed[2] = changed[2].replace(before, after)
        variants.append((name, program(changed)))
    variants.extend(stream_variants(parts))
    added = native.check_controls(output, env, lean, program(parts), variants, prefix="native-scoped-")
    for record in added:
        if not record["expectedAcceptance"] and not re.search(
                r"error: (?:Not a definitional equality|Application type mismatch|Type mismatch|Tactic[^\n]*failed|unsolved goals)",
                (output / (record["name"] + ".stdout")).read_text()):
            raise ValueError("native scoped control lacks a semantic proof failure: " + record["name"])
    return records + added + insertion_trace_controls(output, env, lean) + invocation_controls(output, env, lean) + miss_controls(output, env, lean) + admission_controls(output, env, lean) + replay_controls(output, env, lean) + initialized_miss_controls(output, env, lean) + cache_stream_controls(output, env, lean) + caller.local_controls(output, env, lean) + child_protocol.controls(output, env, lean) + caller_protocol.controls(output, env, lean) + constructor_protocol.controls(output, env, lean) + miss_protocol.controls(output, env, lean) + history_protocol.controls(output, env, lean) + initialized_protocol.controls(output, env, lean) + constructor_return.controls(output, env, lean)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--preflight", action="store_true")
    native.check(parser.parse_args(), module=MODULE, claims=CLAIMS, dependency_check=dependencies,
        control_check=controls, normalization_scope=True, live_initialization=True, live_scope=True, live_take=True,
        live_close=True, scoped_miss=True, native_scoped_dispatch=True)
