#!/usr/bin/env python3
"""Acceptance for the complete source-bound normalization lifecycle.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import json
import re

import extract_cache
import extract_interner
import check_verification_map
from extract_compiler import Unsupported
from check_argument_memory import ROOT, NS, MEMORY
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
from build_toolchain import digest

MODULE = "Compiler.Extraction.NormalizationMemoryTests"
NORMALIZATION = NS + "Normalization."
FILES = ["NormalizationMemory" + suffix + ".lean" for suffix in (
    "", "Contracts", "Init", "Lifetime", "Proofs", "Settles", "Frame", "Caller", "Tests")]
CLAIMS = [NORMALIZATION + name for name in (
    "Injected.fresh", "Injected.retained", "Injected.extended", "Injected.published", "Injected.erased",
    "persistent_cleanup", "Injected.cleanup", "related_cleanup", "Valid.cleanup",
    "represented_frame", "related_frame", "free_valid", "duplication_valid",
    "prepare_ready", "prepare_failure", "scratch_destination", "allocated_destination", "reserve_refines", "prepare_classified", "init_refines",
    "released_source", "take_refines", "released_consumed", "deinit_refines", "continue_refines",
    "closed_result", "run_refines", "run_result", "prepare_settles", "init_settles", "run_settles",
    "reserve_shape", "prepare_footprint", "prepare_initial_frame", "init_frame", "closed_frame", "run_verified",
    "caller_buffer", "normalized_projection", "transferred_word", "production_verified")]
CLAIMS += [NORMALIZATION + "Tests." + name for name in (
    "external_admitted", "original_valid", "actual_caller_allocation", "ready_caller", "allocated_transfer",
    "allocated_lookup_cleanup", "allocated_caller_cleanup", "transferred_buffer_live", "noncommutative_borrows",
    "noncommutative_duplicate_exact", "singleton_borrows", "exact_fit_scratch_lookup", "scratch_duplicate_after_sort",
    "scratch_caller_retains_buffer", "empty_dead_sentinel", "temporary_oom_retains_effects", "duplicate_oom_after_scratch",
    "suspension_retains_allocation", "semantic_stack_exhaustion_is_not_oom", "full_contract", "complete_frame",
    "original_and_other_preserved", "production_add", "production_add_observed", "all_exits_settle")]


def bindings():
    coverage = check_verification_map.check(json.loads(check_verification_map.MAP.read_bytes()))
    source = extract_cache.SOURCE.read_bytes()
    arguments = [source, extract_cache.SEMANTICS.read_bytes(), extract_cache.ITEMS.read_bytes(), extract_cache.OPCODES.read_bytes()]
    if extract_cache.extract(*arguments) != extract_cache.OUTPUT.read_bytes():
        raise ValueError("normalization body extraction is stale")
    if extract_interner.extract(source) != extract_interner.OUTPUT.read_bytes():
        raise ValueError("normalization caller extraction is stale")
    controls = []
    for name, before, after, exporter in (
        ("scratch-size", b"var argument_buffer: [2]Id = undefined;", b"var argument_buffer: [3]Id = undefined;", extract_interner.extract),
        ("caller-alias", b"item, arguments, &argument_buffer", b"item, arguments, @constCast(arguments)", extract_interner.extract),
        ("caller-loses-defer", b"defer lookup.deinit(self.allocator);", b"", extract_interner.extract),
        ("reversed-copy", b"@memcpy(normalized, arguments);", b"@memcpy(arguments, normalized);", lambda data: extract_cache.extract(data, *arguments[1:])),
        ("descending-sort", b"std.sort.asc(Id)", b"std.sort.desc(Id)", lambda data: extract_cache.extract(data, *arguments[1:])),
        ("dupe-alias", b"return allocator.dupe(Id, self.items);", b"return @constCast(self.items);", lambda data: extract_cache.extract(data, *arguments[1:])),
    ):
        if before not in source:
            raise ValueError("source binding control lost its target: " + name)
        try:
            exporter(source.replace(before, after))
        except Unsupported as error:
            controls.append({"name": name, "status": "passed", "expectedAdmission": False, "admitted": False, "reason": str(error)})
        else:
            raise ValueError("unmodeled normalization/caller source was admitted: " + name)
    return {"sourceSha256": digest(extract_cache.SOURCE), "cacheProgramSha256": digest(extract_cache.OUTPUT),
            "internerProgramSha256": digest(extract_interner.OUTPUT), "callerScratchWords": 2,
            "trustBoundaryVersion": coverage["boundaryVersion"], "trustBoundarySha256": coverage["boundarySha256"],
            "entryPoints": ["NormalizedArguments.init", "NormalizedArguments.takeOwned", "NormalizedArguments.deinit"],
            "callers": ["ExpressionClasses.find", "ExpressionClasses.forceEqual"], "controls": controls,
            "boundary": "Reviewed complete-body admission and checked generated freshness; exporter and native external contracts remain trusted. Caller admission does not prove its intervening graph operations."}


def audit(output):
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_text())["claims"]}
    required = {
        NORMALIZATION + "production_verified": {NORMALIZATION + name for name in (
            "run_verified", "caller_buffer", "transferred_word", "normalized_projection", "Post", "Closed", "Result", "Admitted",
            "init_refines", "continue_refines", "run", "init", "takeOwned", "deinitialize", "free", "Frame")}
            | {NS + "Allocation.reserve_admitted", NS + "Duplication.run_total", NS + "release_refines",
               "Compiler.Extraction.InsertionSort.Copied.run_result", "Compiler.Extraction.Cache.normalizationOwnershipCode",
               "Compiler.Extraction.InsertionSort.normalize_word"},
        NORMALIZATION + "run_settles": {NORMALIZATION + n for n in ("init_settles", "run_result", "Post")}
            | {"Compiler.Extraction.InsertionSort.Copied.run_refines"},
        NORMALIZATION + "Valid.cleanup": {NORMALIZATION + n for n in ("Injected.cleanup", "related_cleanup", "persistent_cleanup")},
        NORMALIZATION + "Injected.retained": {NORMALIZATION + "Injected", MEMORY + "Allocation.SameShape"},
        NORMALIZATION + "caller_buffer": {MEMORY + "allocate_preserves_valid", MEMORY + "WordArray.writable_fresh", NORMALIZATION + "Injected.fresh"},
        NORMALIZATION + "take_refines": {NS + "Duplication.run_total", NORMALIZATION + "Taken"},
        NORMALIZATION + "deinit_refines": {NS + "release_refines", NORMALIZATION + "Consumed"},
        NORMALIZATION + "Tests.full_contract": {NORMALIZATION + "run_verified", NORMALIZATION + "Tests.external_admitted"},
        NORMALIZATION + "Tests.production_add": {NORMALIZATION + "production_verified", NORMALIZATION + "Tests.external_admitted",
                                                 NORMALIZATION + "Tests.actual_caller_allocation"},
        NORMALIZATION + "Tests.production_add_observed": {NORMALIZATION + "Tests.production_add", NORMALIZATION + "Tests.scratch_duplicate_after_sort"},
        NORMALIZATION + "Tests.all_exits_settle": {NORMALIZATION + "run_settles"},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError("normalization composition lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return {"checkedDependencies": sorted(required), "obligation": "normalization.production",
            "composedTheorem": NORMALIZATION + "production_verified", "recursiveMemoryBridgeVerified": False,
            "trustBoundaryVersion": 1, "completionRoute": "implementationUnderExplicitMemoryContracts",
            "modeledRegistryLifetimeVerified": True, "nativeGraphOwnershipVerified": False}


def controls(output, env, lean):
    imports = "import Compiler.Extraction.ArgumentMemoryDuplicationTests\nimport Compiler.Extraction.InsertionSortNormalization\n"
    bodies = [without_imports((ROOT / "lean/Compiler/Extraction" / name).read_text()) for name in FILES]
    model, clients = bodies[0], "\n".join(bodies[1:])
    source = imports + model + "\n" + clients
    records = [mutation_check(output, "normalization-production-unchanged", source, True, env, lean)]
    for name, before, after, count in (
        ("wrong-allocation-length", "Allocation.reserve before.heap before.memory allocator values", "Allocation.reserve before.heap before.memory allocator []", 1),
        ("borrow-binary-input", "source.length < code.threshold", "source.length ≤ code.threshold", 1),
        ("omit-copy", "let (result, memory) := Copied.run budget before.memory source target", "let (result, memory) := Captured.run budget before.memory target", 1),
        ("sort-input", "let (result, memory) := Copied.run budget before.memory source target", "let (result, memory) := Copied.run budget before.memory source source", 1),
        ("keep-transferred-ownership", "if code.clearOnTake then none else handle.owned", "handle.owned", 1),
        ("free-borrowed-storage", "| none => (.ok (), before)\n\ninductive Outcome", "| none => free external allocator ⟨handle.items.allocation, handle.values⟩ before\n\ninductive Outcome", 1),
        ("lose-preparation-writes", "let reached := { before with memory := memory }", "let reached := before", 1),
        ("oom-is-semantic-fault", "| .ok none => (.error .outOfMemory, after)", "| .ok none => (.error (.allocation (.memory .outOfMemory)), after)", 2),
        ("omit-caller-free", "let (released, after) := free external allocator slice reached", "let (released, after) := (Except.ok (), reached)", 1),
        ("lose-allocation-effects", "effects := effects }", "effects := before.effects }", 2),
    ):
        if model.count(before) != count:
            raise ValueError("ambiguous normalization mutation: " + name + ": " + str(model.count(before)))
        changed = imports + model.replace(before, after) + "\n" + clients
        records.append(mutation_check(output, "normalization-" + name, changed, False, env, lean))
    for record in records:
        diagnostic = (output / (record["name"] + ".stdout")).read_text()
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant", diagnostic, re.I):
            raise ValueError("normalization control hit a resource or syntax failure: " + record["name"])
    definitions = bodies[1][:bodies[1].index("\ntheorem Injected.fresh")]
    definitions += "\nend Compiler.Extraction.Memory.Arguments.Normalization\n"
    tests = (ROOT / "lean/Compiler/Extraction/InternerConstructorFrameTests.lean").read_text()
    witness = "\nnamespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorFrame.Tests\n"
    witness += "open Compiler.ZigAir.Memory.WordArray\n"
    witness += tests[tests.index("\ndef escaping"):]
    # Isolate the invariant counterexample from proofs whose constructor field
    # types change under corruption. The complete unchanged clients above and
    # fresh dependency replay remain mandatory.
    lifetime = "∃ cell, memory.heap.lookup id = some cell ∧ cell.stack = false"
    if definitions.count(lifetime) != 1:
        raise ValueError("ambiguous persistent registry invariant")
    records.append(mutation_check(output, "normalization-registry-witness-unchanged",
        imports + model + "\n" + definitions + witness, True, env, lean))
    record = mutation_check(output, "normalization-stack-backed-registry",
        imports + model + "\n" + definitions.replace(lifetime, "∃ cell, memory.heap.lookup id = some cell ∧ True") + witness,
        False, env, lean)
    diagnostic = (output / (record["name"] + ".stdout")).read_text()
    if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant", diagnostic, re.I):
        raise ValueError("registry lifetime control hit a resource or syntax failure")
    if not re.search(r"error: (?:unsolved goals|Application type mismatch|Type mismatch|Tactic[^\n]*failed)", diagnostic):
        raise ValueError("registry lifetime control lacks a semantic proof failure")
    records.append(record)
    return records
