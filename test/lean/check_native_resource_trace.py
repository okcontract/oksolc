#!/usr/bin/env python3
"""Check exact host-call recording through native normalization and caller control.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import json
from pathlib import Path
import re

from check_argument_memory import ROOT, inputs, lean_check, prove
from check_word_swap import audit
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
from build_toolchain import digest, run, write_json

MODULE = "Compiler.Extraction.NormalizationHostTraceTests"
ARG = "Compiler.Extraction.Memory.Arguments."
NS = ARG + "Normalization."
OWNED = NS + "OwnedCall."
TRACE = NS + "HostTrace."
FILES = [
    "ZigAir/MemoryAllocationEffects.lean", "Extraction/ArgumentMemoryEffects.lean",
    "Extraction/NormalizationMemoryEffects.lean", "Extraction/NormalizationHostTrace.lean",
    "Extraction/GraphEffects.lean", "Extraction/InternerOwnedMemoryEffects.lean",
    "Extraction/InternerCallerMemoryEffects.lean", "Extraction/NormalizationHostTraceTests.lean",
]
CLAIMS = ["Compiler.ZigAir.Memory." + name for name in (
    "RegionAllocation.reserve_transport", "WordAllocation.reserve_transport")]
CLAIMS += [ARG + name for name in ("Allocation.reserve_transport", "Duplication.run_transport")]
CLAIMS += [NS + "External.Transport." + name for name in (
    "admitted", "reserve", "prepare", "init", "takeOwned", "free", "deinitialize", "close", "continueWith", "run")]
CLAIMS += [TRACE + name for name in (
    "allocation_observation", "release_observation", "transport", "admitted", "prefix_transport", "run_erases", "run_prefix")]
CLAIMS += ["Compiler.Algebraic.Effect.Transport." + name for name in ("pure", "bind")]
CLAIMS += [OWNED + "EffectTransport." + name for name in ("graph", "take", "deinit", "cleanup", "finish")]
CLAIMS += [OWNED + "Caller.EffectTransport." + name for name in ("initLookup", "findBody", "invoke", "find")]
CLAIMS += [OWNED + "Caller.host_trace_erases"]
CLAIMS += [TRACE + "Tests." + name for name in (
    "actual_admitted", "lifecycle_erases", "temporary_transfer", "temporary_cleanup", "borrowed_duplicate",
    "borrowed_lookup", "empty_transfer", "oom_retained", "incomplete_retains_allocation", "invalid_response_retained",
    "partial_copy_retained", "rejected_release_skips_host", "existing_history")]
CLAIMS += [OWNED + "HostTraceTests." + name for name in (
    "nested_transport", "release_transport", "callbacks_transport", "caller_erases", "nested_oom_reached_state",
    "nested_oom_event_order", "semantic_fault_event_order", "semantic_fault_retains_parent")]
CLAIMS += [OWNED + "Tests.callbacks_contracts", OWNED + "Caller.Tests.find_nested_failure",
    OWNED + "Semantic.Tests.semantics", OWNED + "Recursive.ProductionTests.success_verified"]


def dependencies(output):
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    required = {
        NS + "External.Transport.run": {ARG + "Allocation.reserve_transport", ARG + "Duplication.run_transport",
            NS + "External.Transport.free", NS + "run", NS + "prepare"},
        TRACE + "run_erases": {TRACE + "record", TRACE + "transport", NS + "External.Transport.run"},
        OWNED + "Caller.EffectTransport.findBody": {"Compiler.Extraction.Interner.FindCode.controlRun",
            "Compiler.Algebraic.Effect.Transport.bind", OWNED + "EffectTransport.take",
            OWNED + "EffectTransport.graph", OWNED + "Caller.EffectTransport.initLookup"},
        OWNED + "Caller.host_trace_erases": {TRACE + "transport", OWNED + "Caller.EffectTransport.find",
            OWNED + "EffectTransport.finish", OWNED + "cleanup", OWNED + "Primitives.Transport"},
        OWNED + "HostTraceTests.caller_erases": {OWNED + "Caller.host_trace_erases",
            OWNED + "HostTraceTests.callbacks_transport", OWNED + "Tests.callbacksWith", OWNED + "nested"},
        OWNED + "HostTraceTests.nested_oom_event_order": {TRACE + "record", OWNED + "Caller.find", OWNED + "nested"},
        OWNED + "Semantic.Tests.semantics": {OWNED + "Tests.callbacksWith", OWNED + "Tests.release_good"},
        OWNED + "Recursive.ProductionTests.success_verified": {OWNED + "Recursive.ProductionTests.production_contract", OWNED + "Tests.callbacksWith"},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError("native host trace lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return sorted(required)


def controls(output, env, lean):
    # The imports contain the existing fixtures, not any instrumentation module.
    # New proofs/consumers are compiled against the mutated definitions together.
    source = "import Compiler.Extraction.InternerCallerTests\n" + "\n".join(
        without_imports((ROOT / "lean/Compiler" / name).read_text()) for name in FILES)
    variants = []
    for name, before, after in (
        ("lost-allocation-event", "effects.events ++ [.allocate site bytes response]", "effects.events"),
        ("wrong-byte-count", "effects.events ++ [.allocate site bytes response]", "effects.events ++ [.allocate site (bytes + 1) response]"),
        ("wrong-allocation-site", "effects.events ++ [.allocate site bytes response]", "effects.events ++ [.allocate .temporary bytes response]"),
        ("lost-allocator-effects", "(response, ⟨after, effects.events", "(response, ⟨effects.effects, effects.events"),
        ("changed-response", "(response, ⟨after, effects.events", "(none, ⟨after, effects.events"),
        ("invalid-region-as-oom", "effects.events ++ [.allocate site bytes response]", "effects.events ++ [.allocate site bytes none]"),
        ("lost-release-event", "before.effects.events ++ [.free slice]⟩", "before.effects.events⟩"),
        ("wrong-released-slice", "before.effects.events ++ [.free slice]⟩", "before.effects.events ++ [.free ⟨slice.address + 1, slice.items⟩]⟩"),
        ("lost-free-effects", "⟨host.free slice (before.mapEffects Recorded.effects),", "⟨before.effects.effects,"),
        ("lost-history", "effects.events ++ [.allocate site bytes response]", "[.allocate site bytes response]"),
        ("rewound-graph", "⟨before.graph, before.memory.mapEffects project⟩",
         "⟨{ before.graph with allocationCursor := 0 }, before.memory.mapEffects project⟩"),
    ):
        if source.count(before) != 1:
            raise ValueError("ambiguous native host trace mutation: " + name)
        variants.append((name, source.replace(before, after)))
    return check_controls(output, env, lean, source, variants)


def check_controls(output, env, lean, source, variants, prefix=""):
    records = [mutation_check(output, prefix + "unchanged", source, True, env, lean)]
    records += [mutation_check(output, prefix + name, changed, False, env, lean) for name, changed in variants]
    for record in records:
        diagnostic = (output / (record["name"] + ".stdout")).read_text()
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant|already been declared", diagnostic, re.I):
            raise ValueError("invalid native host trace control failure: " + record["name"])
    return records


def check(args, *, module=MODULE, claims=CLAIMS, dependency_check=dependencies, control_check=controls,
          publication=False, native_dispatch=False, recursive_entries=False, item_preparation=False, insertion_control=False, insertion_shared=False, insertion_release=False, insertion_append=False, caller_recursion=False, normalization_scope=False, live_initialization=False, live_scope=False, live_take=False, live_close=False, scoped_miss=False, native_scoped_dispatch=False):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.native-host-trace.v1", "status": "failed", "jobs": 4,
        "preflightOnly": args.preflight, "scope": ("Actual initialization/take and native insertion/publication/cleanup segments use a shared tagged protocol. The source guard and actual dispatcher result select the reached insertion, publication or error suffix. A caller input frame and proper-child preservation derive its ownership, publication admission and insertion header/rows. A shared successful initialization/take prefix now feeds the whole scoped miss and checked cleanup through recorded suffix ports, deriving the real token and detached handle. No insertion/publication graph projections or suffix lifetime contracts are supplied. Actual recorded finite entries and their dispatcher now preserve history and derive an exact appended physical host segment, including reached failures. This does not identify that physical segment with tagged protocol slots. A cache hit now derives its complete tagged initialization/cleanup stream, checked close and end cursor from actual input observations, reusing the same successful initialization as taken misses. A conditional child-recording route now computes the tagged dispatcher segment and both relative cursor boundaries, consumed by the initialized miss. The actual find/force source interpreters now compute initialization/take/close observations, preserve native results and caller locals, and retain history. Native graph ports use the shared dispatcher and guarded insertion/publication recorders. Existing cache leaves derive their observations from this execution. Constructor item/scratch/literal/borrowed/local wrappers now derive actual observations at every finite recursive depth and feed the initialized miss. The recorder retains the existing scoped arguments and phase through cleanup. General initialization/take/handoff/close proofs derive local physical admission and exact scoped projection; the complete recorded cache caller and wrapped cache cases preserve the full scoped result. Every child native/scoped/frame relation and accepted complete stream remain obligations. Ordinary error cleanup and semantic retention remain distinct. Complete invocation recording and erasure, native contracts and all-entry induction remain open"
            if native_scoped_dispatch else "Native/scoped miss control and handoff correspondence, with checked cleanup on the actual scoped result; local graph projections and complete invocation binding remain explicit"
            if scoped_miss else "Reached native cleanup with derived scoped admission, composed through take and the actual ordinary miss continuation using existing graph contracts; complete invocation and scoped graph execution remain open"
            if live_close else "Actual live take with admission derived from readiness and permitted hosts, coupled to scoped transfer and initialization; recursive graph work and deferred cleanup composition remain open"
            if live_take else "Checked live normalization scope coupled to the actual caller, ready native handle, ordinary results, word meaning and protocol cursor; intervening graph/take/cleanup composition remains open"
            if live_scope else "Live normalization prefix with exact native/host erasure and actual Caller.initLookup consumption; scoped replay and intervening recursive graph operations remain open"
            if live_initialization else "One actual normalization lifecycle with separate host/protocol transcripts, exact native erasure and accepted scoped word semantics; interleaved recursive caller coupling remains open"
            if normalization_scope else "Actual native caller publication/insertion binding and recorded all-entry recursion erasure at every finite depth; native map buckets and scoped resource coupling remain open"
            if caller_recursion else "Native append/growth recording and derived insertion erasure consumed by all-depth entry induction; seed publication remains explicit"
            if insertion_append else "Native release recording and all-outcome callback erasure consumed by all-depth entry induction; append/growth and seed publication remain explicit"
            if insertion_release else "Native argument/publication callback erasure consumed by all-depth entry induction, conditional on append/non-argument releases and seed publication transport"
            if insertion_shared else "Native insertion control and all-depth entry erasure derived from item/clone transport and explicit remaining argument/append/publication/release callback obligations"
            if insertion_control else "Exact item/payload host recording and native item/clone callback erasure; all-depth entry erasure remains conditional on complete insertion transport"
            if item_preparation else "Exact erasure of all native constructor entries at every finite recursion depth, conditional on local host/publication/insertion transport"
            if recursive_entries else "Exact native dispatcher and publication erasure through caller control, conditional on proper-child and insertion transport"
            if native_dispatch else "Exact publication probe recording and derived publication erasure through native caller control"
            if publication else "Exact normalization host-call recording and native caller erasure; existing nested callback fixtures"),
        "publicationHostTraceErasureVerified": False, "nativeDispatcherErasureVerified": False,
        "nativeRecursiveEntriesErasureVerified": False, "nativeItemPreparationErasureVerified": False,
        "nativeInsertionControlErasureVerified": False, "nativeInsertionSharedErasureVerified": False, "nativeInsertionReleaseErasureVerified": False,
        "nativeInsertionAppendErasureVerified": False,
        "nativeCallerRecursionErasureVerified": False,
        "normalizationHostScopeVerified": False, "liveCallerInitializationVerified": False, "liveCallerScopeVerified": False, "liveCallerTakeVerified": False,
        "liveCallerCloseVerified": False, "nativeScopedMissVerified": False, "nativeScopedDispatchVerified": False, "nativeInsertionProtocolReplayVerified": False, "nativeInsertionActionReplayVerified": False, "nativeInsertionStreamPrefixVerified": False, "nativeInsertionStreamCloseVerified": False, "nativePublicationStreamVerified": False, "nativeMissTailRoutingVerified": False, "nativeMissTailAdmissionVerified": False, "nativeMissReplayVerified": False, "nativeInitializedMissVerified": False, "nativeHostSegmentsVerified": False, "nativeCacheStreamVerified": False, "nativeChildProtocolCompositionVerified": False, "nativeCallerProtocolRecordingVerified": False, "nativeConstructorProtocolRecordingVerified": False, "nativeCallerScopeRecordingVerified": False, "nativeHostTraceErasureVerified": False, "completeInvocationTraceVerified": False,
        "scopedResourceCouplingVerified": False, "composedProductionTheoremVerified": False, "wholeCompilerVerified": False,
        "remaining": [("Derive each recorded recursive child's native/scoped/frame relation and accepted complete stream, then close remaining suffix/candidate/word obligations and all-entry induction"
            if native_scoped_dispatch else "Derive the local native graph projections and lifetime contracts under proper-child induction; bind initialization/take/miss/close cursors and events to the complete invocation"
            if scoped_miss else "Bind scoped graph decisions, handoff and all segments to the complete native invocation; discharge existing graph contracts in the all-entry induction"
            if live_close else "Compose recursive graph operations and deferred cleanup with the initialization/take relation and its derived take admission"
            if live_take else "Compose actual take, recursive graph operations and cleanup with the checked live initialization relation"
            if live_scope else "Connect the live prefix to Scoped.initScope, then compose take and cleanup around recursive graph operations"
            if live_initialization else "Compose normalization scope observation across native caller initialization, take, recursive graph operations and cleanup"
            if normalization_scope else "Native map bucket implementation and complete invocation recording"
            if caller_recursion else "Seed publication binding, native map buckets, and complete invocation recording"
            if insertion_append else "Native append/growth transport and recording, seed publication binding, native map buckets, and complete invocation recording"
            if insertion_release else "Native append/growth and non-argument release transport, seed publication binding, complete recording, and native map buckets"
            if insertion_shared else "Discharge native insertion argument/growth/publication/release callback obligations and complete their recording; native map buckets"
            if insertion_control else "Native insertion argument/growth/publication/release transport and recording, complete insertion composition, and native map buckets"
            if item_preparation else "Production insertion/recursive callback instrumentation and native map bucket implementation"
            if publication else "Production insertion/publication/recursive callback instrumentation"),
            "Binding actual host calls to the ownership protocol and scoped resource model",
            "All-entry word-preservation induction and production constructor correspondence"]}
    try:
        report["inputs"], report["leanInputs"] = inputs(), lean_check.source_inputs()
        env, _, report["tools"] = lean_check.toolchain(args.lean_bin, 4)
        run(output, "build", [report["tools"]["lake"]["path"], "build", module], cwd=ROOT / "lean", env=env)
        report["audit"] = audit(output, env, report["tools"]["lean"]["path"], module, claims)
        report["checkedDependencies"] = dependency_check(output)
        report["controls"] = control_check(output, env, report["tools"]["lean"]["path"])
        if not args.preflight:
            proof, artifacts = prove.check_module(module, claims, lean_bin=args.lean_bin, jobs=4, fresh=True, timeout=1800)
            directory = output / "proof"
            directory.mkdir()
            for name, data in artifacts.items():
                (directory / name).write_bytes(data)
            write_json(directory / "report.json", proof)
            report["proofReportSha256"] = digest(directory / "report.json")
            if (proof.get("status") != "passed" or proof.get("freshKernelReplay") is not True or
                    proof.get("replayIncludesImports") is not True or proof.get("auditedDeclarations") != claims):
                raise ValueError("native host trace fresh imported kernel replay failed")
        if inputs() != report["inputs"] or lean_check.source_inputs() != report["leanInputs"]:
            raise ValueError("native host trace inputs changed during acceptance")
        report.update(status="passed", nativeHostTraceErasureVerified=not args.preflight, publicationHostTraceErasureVerified=publication and not args.preflight,
            nativeDispatcherErasureVerified=native_dispatch and not args.preflight,
            nativeRecursiveEntriesErasureVerified=recursive_entries and not args.preflight,
            nativeInsertionControlErasureVerified=insertion_control and not args.preflight,
            nativeInsertionSharedErasureVerified=insertion_shared and not args.preflight,
            nativeInsertionReleaseErasureVerified=insertion_release and not args.preflight,
            nativeInsertionAppendErasureVerified=insertion_append and not args.preflight,
            nativeCallerRecursionErasureVerified=caller_recursion and not args.preflight,
            normalizationHostScopeVerified=normalization_scope and not args.preflight,
            liveCallerInitializationVerified=live_initialization and not args.preflight,
            liveCallerScopeVerified=live_scope and not args.preflight,
            liveCallerTakeVerified=live_take and not args.preflight,
            liveCallerCloseVerified=live_close and not args.preflight,
            nativeScopedMissVerified=scoped_miss and not args.preflight,
            nativeScopedDispatchVerified=native_scoped_dispatch and not args.preflight,
            nativeInsertionProtocolReplayVerified=native_scoped_dispatch and not args.preflight,
            nativeInsertionActionReplayVerified=native_scoped_dispatch and not args.preflight,
            nativeInsertionStreamPrefixVerified=native_scoped_dispatch and not args.preflight,
            nativeInsertionStreamCloseVerified=native_scoped_dispatch and not args.preflight,
            nativePublicationStreamVerified=native_scoped_dispatch and not args.preflight,
            nativeMissTailRoutingVerified=native_scoped_dispatch and not args.preflight,
            nativeMissTailAdmissionVerified=native_scoped_dispatch and not args.preflight,
            nativeMissReplayVerified=native_scoped_dispatch and not args.preflight,
            nativeInitializedMissVerified=native_scoped_dispatch and not args.preflight,
            nativeCallerScopeRecordingVerified=not args.preflight and all(
                OWNED + "Caller.ProtocolTrace." + name in claims for name in (
                    "initialization_projected", "take_projected", "handoff_projected",
                    "lookup_close_projected", "taken_close_projected", "cached_projected")),
            nativeConstructorProtocolRecordingVerified=not args.preflight and OWNED + "ConstructorItem.NativeRecursion.ProtocolTrace.initialized_children" in claims,
            nativeCallerProtocolRecordingVerified=not args.preflight and OWNED + "Caller.ProtocolTrace.Native.find_segment" in claims,
            nativeChildProtocolCompositionVerified=not args.preflight and OWNED + "MissStream.initialized_recorded_children" in claims,
            nativeCacheStreamVerified=not args.preflight and OWNED + "Caller.CacheStream.cached" in claims,
            nativeHostSegmentsVerified=not args.preflight and OWNED + "ConstructorItem.NativeRecursion.dispatcher_recorded_segment" in claims,
            nativeItemPreparationErasureVerified=item_preparation and not args.preflight, auditedDeclarations=len(claims))
    finally:
        write_json(output / "report.json", report)
    print(f"Native host trace {'preflight' if args.preflight else 'acceptance'} passed: {len(claims)} roots, {len(report['controls'])} controls; complete invocation coupling remains open.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--preflight", action="store_true")
    check(parser.parse_args())
