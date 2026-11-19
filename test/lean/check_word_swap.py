#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Check captured u32 swap admission and the typed-heap entry contract.
// Copyright (C) 2026 OKcontract Pte. Ltd.

The default gate checks entry separation and finite executions. --invocation
also proves complete array-view swap refinement with explicit exhaustion.
--observations additionally proves primitive tracing and dynamic site coverage.
--confinement proves argument-relative data footprints for all execution prefixes.
--regions additionally proves stable modeled allocation metadata and word regions.
--caller composes the captured swap with the source-bound insertion-sort loops.
--copied additionally initializes the selected destination using proved typed copy.
--prepared carries copy/sort effects through the normalization ownership scope.
--storage proves allocation metadata and the initialized ownership projection.
--allocation discharges destination obligations using a checked external allocator contract.
--duplication connects allocation and exact typed copying for the borrowed take contract.
--normalization composes the complete production lifecycle under explicit native contracts.
--resource-adapter interprets the ownership resource protocol by that exact memory execution.
--scope-trace checks physical invocation replay into the recursive resource cursor.
--owned-continuation checks source-bound caller cleanup across graph callbacks.
--interner-callers checks complete find/forceEqual control with physical normalization.
--physical-words composes word preservation for that same complete physical execution.
--physical-dispatch binds the shared extracted dispatcher to physical recursive callbacks.
--dispatcher-preservation proves its universal borrowing and word-transport contracts.
--dispatcher-production composes those contracts into both complete physical callers.
With --proof-component, check only that Lean composition and its semantic controls;
this does not run the native capture gate. --preflight skips its fresh replay.
Native pointer provenance and source/native preservation remain open.
"""
import argparse
import copy
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "lean"))
sys.path.insert(0, str(ROOT / "lean/zig_air"))
import environment as lean_check
import prove
import check_byte_invocation
import check_byte_exchange
import check_insertion_sort
import extract_insertion_sort
import extract_cache
from build_toolchain import digest, run, source_identity, write_json
from capture import capture, read_json
from generate import captured_path
from generate_word_swap import generate, WordSwapDecoder
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

SOURCE = ROOT / "test/lean/zig_air_specialization.zig"
CALLER = "zig_air_specialization.swap_words"
MODULE = "Compiler.ZigAir.MemoryWordSwapTests"
DIRECTORY = ROOT / "lean/Compiler/ZigAir"
PAIR = "Compiler.ZigAir.Memory.WordPair."
PROGRAM = "Compiler.ZigAir.MemoryAir.WordPairProgram."
TESTS = "Compiler.ZigAir.MemoryWordSwap.Tests."
CLAIMS = [PAIR + n for n in ("region_sound", "validate_sound", "validated_bytes_apart", "aliases_rejected", "region_view", "validate_view")]
CLAIMS += [PROGRAM + n for n in ("rejection_retains_state", "accepted_run", "resume_add", "preserves_valid")]
CLAIMS += [TESTS + n for n in ("contract_witness", "preserves_valid", "complete_swap", "reversed_swap", "aliases_reject",
    "unaligned_reject", "uninitialized_reject", "readonly_reject", "dead_reject", "malformed_reject", "allocation_exhausted",
    "suspended_stack", "resumed_swap")]
INVOCATION_MODULE = "Compiler.ZigAir.MemoryWordSwapInvocationTests"
SWAP = "Compiler.ZigAir.MemoryWordSwap."
INVOCATION_CLAIMS = CLAIMS + [SWAP + n for n in (
    "generated_head", "head_shape", "condition_eval", "condition_locals", "lane_locals", "lane_of_effects", "lane_refines",
    "counter_found", "counter_store", "counter_read", "view_older", "counter_writable", "counter_represents", "counter_cleanup",
    "step_prepend", "lane_counter_refines", "generated_loop", "body_enter", "tail_locals", "tail_steps", "loop_stop", "loop_next",
    "lanes_next", "loop_refines", "initialized_swap", "generated_prologue", "bytes_steps", "access_steps", "initialize_counter",
    "stored_locals", "stored_steps", "body_steps", "accepts", "finish_counter", "swap_refines")]
INVOCATION_CLAIMS += ["Compiler.ZigAir.Memory." + n for n in (
    "root_store_total", "fresh_store_total", "WordByteView.read_prepend", "WordByteView.write_prepend", "ByteExchange.step_effects")]
INVOCATION_CLAIMS += [TESTS + n for n in ("total_witness", "exhausted_valid", "exhausted_total_witness")]
OBSERVATION_MODULE = "Compiler.ZigAir.MemoryWordSwapObservationTests"
MACHINE = "Compiler.ZigAir.Control.Machine."
OBSERVATION_CLAIMS = INVOCATION_CLAIMS + [MACHINE + n for n in (
    "trace_erases", "trace_finished", "trace_add", "trace_bind", "trace_bind_fault", "trace_bind_bad_type",
    "trace_reachable", "jump_covered", "backedge_covered", "step_covered", "trace_covered", "root_trace_covered")]
OBSERVATION_CLAIMS += [SWAP + n for n in ("data_sites_checked", "data_sites_complete")]
OBSERVATION_CLAIMS += ["Compiler.ZigAir.MachineObservationTests." + n for n in (
    "repeated_states", "repeated_environments", "failed_attempt_retained", "bad_type_attempt_retained",
    "unselected_branch_absent", "zero_budget_empty", "resumed_observations")]
OBSERVATION_CLAIMS += [TESTS + n for n in (
    "complete_byte_attempts", "complete_binding_count", "exhausted_attempts", "exhausted_no_byte_attempt", "body_observation_erases")]
CONFINEMENT_MODULE = "Compiler.ZigAir.MemoryWordSwapConfinementTests"
CONFINEMENT_CLAIMS = OBSERVATION_CLAIMS + [MACHINE + "GuardedSteps." + n for n in (
    "erases", "trans", "bind_ok", "bind_fault", "control", "terminal_trace")]
CONFINEMENT_CLAIMS += [SWAP + n for n in (
    "Footprint.byte_access", "Footprint.counter_access", "Footprint.allocation", "borrowed_word", "borrowed_bytes_apart",
    "borrowed_counter_apart", "left_borrow", "right_borrow", "lane_guarded_of_effects", "lane_guarded", "condition_guarded",
    "body_enter_guarded", "tail_guarded", "loop_stop_guarded", "loop_next_guarded", "loop_guarded", "initialized_guarded",
    "bytes_guarded", "access_guarded", "stored_guarded", "body_guarded", "observed_valid", "captured_confinement", "counter_region_separate")]
CONFINEMENT_CLAIMS += ["Compiler.ZigAir.MachineGuardedTests." + n for n in (
    "failing_path", "failing_prefixes", "unchecked_attempt_rejected", "suspension_is_not_terminal_evidence")]
CONFINEMENT_CLAIMS += [TESTS + n for n in (
    "all_caller_prefixes", "all_exhausted_prefixes", "all_byte_prefixes", "next_word_not_borrowed")]
REGION_MODULE = "Compiler.ZigAir.MemoryWordSwapRegionTests"
MEMORY = "Compiler.ZigAir.Memory."
MEMORY_AIR = "Compiler.ZigAir.MemoryAir."
REGION_CLAIMS = CONFINEMENT_CLAIMS + [MEMORY + n for n in (
    "Allocation.SameShape.refl", "Allocation.SameShape.trans", "Allocation.SameShape.address",
    "Heap.RetainsShape.refl", "Heap.RetainsShape.trans", "Heap.RetainsShape.writable",
    "store_retains_shape", "allocate_retains_shape", "cleanup_lookup_older", "cleanup_retains_shape", "valid_regions_separated")]
REGION_CLAIMS += [MEMORY_AIR + n for n in (
    "Prim.transition_retains_shape", "Prim.retains_shape", "machine_steps_retain_shape",
    "observed_retains_shape", "machine_steps_cleanup_retain_shape")]
REGION_CLAIMS += [SWAP + n for n in ("captured_retains_shape", "captured_regions", "captured_byte_regions")]
REGION_CLAIMS += [MEMORY + "ShapeTests." + n for n in (
    "contents_can_change", "base_cannot_change", "type_cannot_change", "permission_cannot_change", "lifetime_cannot_change",
    "deletion_not_retained", "caller_valid", "allocated_valid", "allocate_witness", "allocation_retains_caller",
    "cleanup_retains_caller", "cleanup_removes_fresh", "cleanup_does_not_retain_fresh", "live_regions_separate")]
REGION_CLAIMS += [TESTS + n for n in (
    "all_prefix_shapes", "exhausted_prefix_shapes", "all_prefix_writable", "fixed_argument_regions", "actual_byte_regions")]
CALLER_MODULE = "Compiler.Extraction.InsertionSortCapturedTests"
SORT = "Compiler.Extraction.InsertionSort.Captured."
SORT_TESTS = "Compiler.Extraction.InsertionSort.CapturedTests."
CALLER_CLAIMS = REGION_CLAIMS + [MEMORY + "WordArray." + n for n in (
    "HeapFrame.refl", "HeapFrame.trans", "Frame.heapFrame", "HeapFrame.heap_eq")]
CALLER_CLAIMS += [SORT + n for n in (
    "exchange_of_view", "invocation_settles", "exchange_refines", "insert_head", "insert_refines", "passes_refines", "run_refines",
    "exchange_stable", "insert_stable", "passes_stable", "run_stable", "run_result")]
CALLER_CLAIMS += [SORT_TESTS + n for n, _ in check_insertion_sort.CASES]
CALLER_CLAIMS += [SORT_TESTS + n for n in (
    "allocations_advance", "one_swap_room_valid", "later_exhaustion_retains_prefix", "exhausted_prefix_observations",
    "suspension_retains_prefix", "suspension_keeps_partial_write", "zero_budget_is_incomplete", "width_rejects",
    "empty_skips_reads", "alias_rejects", "outside_view_rejects", "total_witness", "every_success")]


def inputs(normalization=False):
    result = check_byte_invocation.inputs()
    result[str(SOURCE.relative_to(ROOT))] = digest(SOURCE)
    for path in (extract_insertion_sort.SOURCE, ROOT / "test/lean/zig_insertion_sort.zig", ROOT / "test/lean/zig_copy_sort.zig",
                 extract_cache.SEMANTICS, extract_cache.ITEMS, extract_cache.OPCODES):
        result[str(path.relative_to(ROOT))] = digest(path)
    if normalization:
        for name in ("docs/compiler-verification-map.json", "docs/compiler-verification-boundary.md"):
            result[name] = digest(ROOT / name)
    return result


def audit(output, env, lean, module=MODULE, roots=CLAIMS):
    source = "import " + module + '''
import Contract.Check.Declarations
import Lean.Elab.Command
open Lean Elab Command Contract.Check in
run_cmd do
  let mut claims := #[]
  for root in #[
''' + ",\n".join("    ``" + name for name in roots) + '''] do
    let .ok dependencies := Declarations.closure (← getEnv) #[root] | throwError "invalid closure: {root}"
    let .ok axioms := Declarations.axioms dependencies | throwError "disallowed axiom: {root}"
    let some info := (← getEnv).find? root | throwError "missing theorem: {root}"
    unless info matches .thmInfo _ do throwError "not a theorem: {root}"
    claims := claims.push <| Json.mkObj [
      ("theorem", .str root.toString), ("statement", Declarations.expression info.type),
      ("axioms", toJson axioms), ("dependencies", toJson (dependencies.map (·.name.toString)))]
  liftIO <| IO.println (Json.mkObj [("claims", .arr claims)]).compress
'''
    (output / "audit.lean").write_text(source)
    run(output, "audit", [lean, "-DwarningAsError=true", output / "audit.lean"], cwd=ROOT / "lean", env=env)
    raw = (output / "audit.stdout").read_bytes()
    (output / "audit.json").write_bytes(raw)
    claims = json.loads(raw)["claims"]
    if [c["theorem"] for c in claims] != roots:
        raise ValueError("unexpected word-pair claims")
    requirements = {
        PAIR + "validated_bytes_apart": {PAIR + n for n in ("validate", "region", "validate_sound")},
        PAIR + "validate_view": {"Compiler.ZigAir.Memory.WordArray." + n for n in ("Writable", "Represents", "element_regions")},
        TESTS + "complete_swap": {"Compiler.ZigAir.GeneratedMemory.fn_swap_u32", PROGRAM + "runFuel", PAIR + "validate",
                                  "Compiler.ZigAir.Memory.ByteAccess.write", "Compiler.ZigAir.Memory.cleanup"}}
    requirements[SWAP + "swap_refines"] = {
        "Compiler.ZigAir.GeneratedMemory.fn_swap_u32", PROGRAM + "runFuel", PAIR + "validate_view",
        *[SWAP + n for n in ("generated_prologue", "body_steps", "initialize_counter", "initialized_swap",
                            "loop_refines", "loop_next", "counter_store", "step_prepend", "counter_cleanup")],
        *["Compiler.ZigAir.Memory." + n for n in ("allocate_fault_of_layout", "root_store_total", "State.valid", "WordArray.Writable",
                                                "WordArray.Represents", "WordArray.Frame", "ByteExchange.step_refines", "cleanup")],
        "Compiler.ZigAir.WordBytes.exchange_four"}
    # The shape theorem for the projected loop is checked separately; the
    # whole-body equality used by body_steps also includes the entire loop.
    requirements[TESTS + "total_witness"] = {SWAP + "swap_refines"}
    requirements[TESTS + "exhausted_total_witness"] = {SWAP + "swap_refines"}
    requirements[MACHINE + "trace_erases"] = {MACHINE + n for n in ("trace", "advance", "step")}
    requirements[MACHINE + "trace_covered"] = {
        *[MACHINE + n for n in ("trace", "observe", "step_covered", "jump_covered", "backedge_covered")],
        "Compiler.ZigAir.Control.Code.bindings"}
    requirements[SWAP + "data_sites_complete"] = {
        "Compiler.ZigAir.GeneratedMemory.fn_swap_u32", MACHINE + "trace_covered", SWAP + "data_sites_checked", SWAP + "dataSite"}
    requirements[TESTS + "body_observation_erases"] = {MACHINE + "trace_erases", "Compiler.ZigAir.GeneratedMemory.fn_swap_u32"}
    requirements[SWAP + "captured_confinement"] = {
        "Compiler.ZigAir.GeneratedMemory.fn_swap_u32", PAIR + "validate_view", MACHINE + "GuardedSteps.terminal_trace",
        *[SWAP + n for n in ("Footprint", "ByteBorrow", "body_guarded", "loop_guarded", "lane_guarded_of_effects",
                            "initialize_counter", "observed_valid")],
        "Compiler.ZigAir.MemoryAir.machine_steps_preserve_valid"}
    requirements[TESTS + "all_byte_prefixes"] = {SWAP + "captured_confinement", SWAP + "Footprint.byte_access"}
    requirements[SWAP + "borrowed_word"] = {SWAP + "ByteBorrow", "Compiler.ZigAir.Memory.ByteAccess.wordAddress_atByte"}
    requirements[MEMORY_AIR + "machine_steps_retain_shape"] = {
        MACHINE + "Steps.preserves", MEMORY_AIR + "Prim.retains_shape", MEMORY + "Heap.RetainsShape.trans",
        MEMORY + "store_retains_shape", MEMORY + "allocate_retains_shape", MEMORY + "ByteAccess.write_store"}
    requirements[MEMORY_AIR + "machine_steps_cleanup_retain_shape"] = {
        MEMORY_AIR + "machine_steps_retain_shape", MEMORY + "cleanup_retains_shape", MEMORY + "cleanup_lookup_older"}
    requirements[SWAP + "captured_regions"] = {
        "Compiler.ZigAir.GeneratedMemory.fn_swap_u32", MEMORY + "WordArray.element_regions",
        SWAP + "captured_retains_shape", MEMORY_AIR + "observed_retains_shape", MACHINE + "trace_reachable"}
    requirements[SWAP + "captured_byte_regions"] = {
        SWAP + "captured_confinement", SWAP + "borrowed_word", SWAP + "captured_retains_shape", MEMORY + "Allocation.SameShape"}
    requirements[TESTS + "actual_byte_regions"] = {SWAP + "captured_byte_regions"}
    requirements[SORT + "run_refines"] = {
        *[SORT + n for n in ("run", "operations", "exchange", "outcome", "Settles", "exchange_refines", "insert_refines", "passes_refines")],
        *["Compiler.Extraction.InsertionSort." + n for n in ("runUsing", "passesUsing", "insertUsing", "run_sortIds", "Heap.read")],
        SWAP + "swap_refines", "Compiler.ZigAir.GeneratedMemory.fn_swap_u32", MEMORY + "WordArray.HeapFrame"}
    requirements[SORT + "run_result"] = {SORT + n for n in ("run_refines", "run_stable", "exchange_stable", "invocation_settles")}
    requirements[SORT_TESTS + "every_success"] = {SORT + "run_result"}
    for claim in claims:
        if not set(claim["axioms"]) <= {"propext", "Quot.sound", "Classical.choice"}:
            raise ValueError("unexpected word-pair axiom")
        if not requirements.get(claim["theorem"], set()) <= set(claim["dependencies"]):
            raise ValueError("word-pair proof lost an entry, body or memory dependency")
    return {"claims": len(roots), "sha256": digest(output / "audit.json")}


def invocation_controls(output, env, lean, record, sources):
    generated = "namespace Compiler.ZigAir.GeneratedMemory\nopen MemoryAir\ndef fn_swap_u32 : WordPairProgram :=\n"
    generated += WordSwapDecoder(record, sources).program(record) + "\nend Compiler.ZigAir.GeneratedMemory\n"
    prefix = "import Compiler.ZigAir.MemoryByteInvocation\nimport Compiler.ZigAir.MemoryWordPair\n"
    prefix += "import Compiler.ZigAir.MemoryByteExchangeTests\n"
    proofs = "".join(without_imports((DIRECTORY / name).read_text()) for name in (
        "MemoryWordSwapBody.lean", "MemoryWordSwapCounter.lean", "MemoryWordSwapLoop.lean",
        "MemoryWordSwapPrologue.lean", "MemoryWordSwapInvocation.lean"))
    original = prefix + generated + proofs
    result = [mutation_check(output, "invocation-unchanged", original, True, env, lean)]
    for name, before, after in (
        ("counter-does-not-advance", "(.constant (.int false 64 (1)))", "(.constant (.int false 64 (0)))"),
        ("loop-guard-reversed", "(.comparison .lt (.local 15) (.local 16))", "(.comparison .lt (.local 16) (.local 15))"),
    ):
        if generated.count(before) != 1:
            raise ValueError("ambiguous captured counter mutation: " + name)
        result.append(mutation_check(output, name, prefix + generated.replace(before, after) + proofs, False, env, lean))
    before = "prepend caller.nextId (counterCell base index) (caller.nextId + 1) (base + 8) caller"
    if proofs.count(before) != 1:
        raise ValueError("ambiguous counter-prefix mutation")
    result.append(mutation_check(output, "counter-prefix-resets-value", prefix + generated + proofs.replace(
        before, "prepend caller.nextId (counterCell base 0) (caller.nextId + 1) (base + 8) caller"), False, env, lean))
    result += check_byte_exchange.controls(output, env, lean)
    for item in result:
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant",
                     (output / (item["name"] + ".stdout")).read_text(), re.I):
            raise ValueError("invocation control hit a resource or syntax failure")
    return result


def observation_controls(output, env, lean):
    prefix = "import Compiler.ZigAir.MachineProofs\nimport Compiler.ZigAir.ControlTests\n"
    prefix += "import Compiler.ZigAir.GeneratedWordSwap\n"
    original = prefix + "".join(without_imports((DIRECTORY / name).read_text()) for name in (
        "MachineObservations.lean", "MachineCoverage.lean", "MachineObservationTests.lean", "MemoryWordSwapSites.lean"))
    result = [mutation_check(output, "observations-unchanged", original, True, env, lean)]
    for name, before, after in (
        ("observations-omitted", "(observe config ++ next.1, next.2)", "(next.1, next.2)"),
        ("observations-reversed", "(observe config ++ next.1, next.2)", "(next.1 ++ observe config, next.2)"),
        ("observation-environment-lost", "config.env, config.state", "(fun _ => none), config.state"),
        ("coverage-branch-omitted", "yes.bindings ++ no.bindings", "no.bindings"),
        ("coverage-loop-omitted", ".loop _ _ body => body.bindings", ".loop _ _ body => []"),
        ("wrong-write-site", "site = (23, .scalar .unit, .wordByteStore .little (.local 19) (.local 20))",
         "site = (23, .scalar .unit, .wordByteStore .little (.local 19) (.local 21))"),
    ):
        if original.count(before) != 1:
            raise ValueError("ambiguous observation mutation: " + name)
        result.append(mutation_check(output, name, original.replace(before, after), False, env, lean))
    for item in result:
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant",
                     (output / (item["name"] + ".stdout")).read_text(), re.I):
            raise ValueError("observation control hit a resource or syntax failure")
    return result


def confinement_controls(output, env, lean):
    prefix = "import Compiler.ZigAir.MemoryWordSwapObservationTests\n"
    original = prefix + "".join(without_imports((DIRECTORY / name).read_text()) for name in (
        "MachineGuarded.lean", "MemoryWordSwapFootprint.lean", "MemoryWordSwapLaneGuarded.lean",
        "MemoryWordSwapControlGuarded.lean", "MemoryWordSwapLoopGuarded.lean", "MemoryWordSwapPrologueGuarded.lean",
        "MemoryWordSwapConfinement.lean", "MachineGuardedTests.lean", "MemoryWordSwapConfinementTests.lean"))
    result = [mutation_check(output, "confinement-unchanged", original, True, env, lean)]
    for name, before, after in (
        ("unchecked-path-attempt", "(checked : ∀ event ∈ observe config, allowed event)",
         "(checked : ∀ event ∈ ([] : List (Observation Ty Prim Value State)), allowed event)"),
        ("left-origin-next-word",
         "(pointer = .local 18 ∧ pointer.eval env = .ok (ByteAccess.pointer true false (ByteAccess.atByte (view.address left) index)))",
         "(pointer = .local 18 ∧ pointer.eval env = .ok (ByteAccess.pointer true false (ByteAccess.atByte (view.address (left + 1)) index)))"),
        ("right-origin-left-word",
         "(pointer = .local 19 ∧ pointer.eval env = .ok (ByteAccess.pointer true false (ByteAccess.atByte (view.address right) index)))",
         "(pointer = .local 19 ∧ pointer.eval env = .ok (ByteAccess.pointer true false (ByteAccess.atByte (view.address left) index)))"),
        ("counter-origin-shifted",
         "| .load pointer | .store pointer _ => pointer.eval event.env = .ok (counter slot)",
         "| .load pointer | .store pointer _ => pointer.eval event.env = .ok (counter { slot with offset := slot.offset + 8 })"),
        ("allocation-origin-omitted", "| .alloc child => child = usize ∧ event.state.nextId = slot.allocation", "| .alloc _ => True"),
        ("byte-store-origin-omitted",
         "| .wordByteLoad _ pointer | .wordByteStore _ pointer _ => ByteBorrow view left right event.env pointer",
         "| .wordByteLoad _ pointer => ByteBorrow view left right event.env pointer\n  | .wordByteStore .. => True"),
        ("counter-store-origin-omitted",
         "| .load pointer | .store pointer _ => pointer.eval event.env = .ok (counter slot)",
         "| .load pointer => pointer.eval event.env = .ok (counter slot)\n  | .store .. => True"),
    ):
        if original.count(before) != 1:
            raise ValueError("ambiguous confinement mutation: " + name)
        result.append(mutation_check(output, name, original.replace(before, after), False, env, lean))
    for item in result:
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant",
                     (output / (item["name"] + ".stdout")).read_text(), re.I):
            raise ValueError("confinement control hit a resource or syntax failure")
    return result


def region_controls(output, env, lean):
    prefix = "import Compiler.ZigAir.MemoryWordSwapConfinementTests\n"
    original = prefix + "".join(without_imports((DIRECTORY / name).read_text()) for name in (
        "MemoryAllocationShape.lean", "MemoryShapePreservation.lean", "MemoryShapeRegions.lean",
        "MemoryShapeTests.lean", "MemoryWordSwapRegions.lean", "MemoryWordSwapRegionTests.lean"))
    result = [mutation_check(output, "regions-unchanged", original, True, env, lean)]
    for name, before, after in (
        ("base-stability-omitted", "after.base = before.base ∧", "True ∧"),
        ("layout-stability-omitted", "after.type = before.type ∧", "True ∧"),
        ("permission-stability-omitted", "after.writable = before.writable ∧", "True ∧"),
        ("lifetime-stability-omitted", "after.stack = before.stack\n", "True\n"),
        ("caller-cleanup-mark-lost", "caller.heap.RetainsShape (cleanup caller.nextId after).heap",
         "caller.heap.RetainsShape (cleanup 0 after).heap"),
        ("last-byte-region-omitted",
         "current.base + address.offset < original.base + (view.address word).offset + 4 := by",
         "current.base + address.offset < original.base + (view.address word).offset + 3 := by"),
    ):
        if original.count(before) != 1:
            raise ValueError("ambiguous region mutation: " + name)
        result.append(mutation_check(output, name, original.replace(before, after), False, env, lean))
    for item in result:
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant",
                     (output / (item["name"] + ".stdout")).read_text(), re.I):
            raise ValueError("region control hit a resource or syntax failure")
    return result


def caller_controls(output, env, lean):
    original = "import Compiler.ZigAir.MemoryWordSwapRegionTests\n"
    original += without_imports((DIRECTORY / "MemoryWordCallFrame.lean").read_text())
    original += "".join(without_imports((ROOT / "lean/Compiler/Extraction" / name).read_text()) for name in (
        "InsertionSortCaptured.lean", "InsertionSortCapturedProofs.lean", "InsertionSortCapturedResults.lean",
        "InsertionSortCapturedTests.lean"))
    result = [mutation_check(output, "caller-unchanged", original, True, env, lean)]
    for name, before, after in (
        ("caller-bypasses-captured-swap", "| .ok b => outcome (GeneratedMemory.fn_swap_u32.runFuel budget [a, b] state)",
         "| .ok b => (.ok (), state)"),
        ("caller-aliases-swap-operands", "| .ok b => outcome (GeneratedMemory.fn_swap_u32.runFuel budget [a, b] state)",
         "| .ok b => outcome (GeneratedMemory.fn_swap_u32.runFuel budget [a, a] state)"),
        ("caller-resource-fault-becomes-success", "| .finished (.error reason) after => (.error (.memory reason), after)",
         "| .finished (.error reason) after => (.ok (), after)"),
        ("caller-fault-loses-prefix", "| .finished (.error reason) after => (.error (.memory reason), after)",
         "| .finished (.error reason) after => (.error (.memory reason), { after with heap := [] })"),
        ("caller-cleans-suspended-stack", "| .suspended _ _ _ config => (.error .incomplete, config.state)",
         "| .suspended _ mark _ config => (.error .incomplete, cleanup mark config.state)"),
    ):
        if original.count(before) != 1:
            raise ValueError("ambiguous caller mutation: " + name)
        result.append(mutation_check(output, name, original.replace(before, after), False, env, lean))
    for item in result:
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant",
                     (output / (item["name"] + ".stdout")).read_text(), re.I):
            raise ValueError("caller control hit a resource or syntax failure")
    return result


def caller_binding(output, env, lean, lib):
    run(output, "caller-python-tests", [sys.executable, "-m", "unittest", "discover", "-s", "test/lean",
                                       "-p", "test_insertion_sort.py"], cwd=ROOT, env=env)
    generated = extract_insertion_sort.extract((lib / "std/sort.zig").read_bytes(), extract_insertion_sort.SOURCE.read_bytes())
    (output / "InsertionSortProgram.lean").write_text(generated)
    if generated != extract_insertion_sort.OUTPUT.read_text():
        raise ValueError("committed insertion control differs from current production/library source")
    bindings = "import " + CALLER_MODULE + "\nopen Compiler.Extraction.InsertionSort.CapturedTests Compiler.ZigAir.Memory.WordArray\n"
    for name, values in check_insertion_sort.CASES:
        words = ", ".join(f".ok (number {n})" for n in [0xDEADBEEF, *sorted(values), 0xBAADF00D, 99])
        bindings += f"example : observe 160 {values} = (.ok (), [{words}]) := {name}\n"
    return {"sourceSha256": digest(extract_insertion_sort.SOURCE), "librarySha256": digest(lib / "std/sort.zig"),
            "generatedSha256": digest(output / "InsertionSortProgram.lean"),
            "nativeModelBinding": mutation_check(output, "caller-native-binding", bindings, True, env, lean),
            "nativeObservationProjection": "sorted input and both sentinels; unrelated modeled allocation additionally remains 99"}


def controls(output, env, lean, record, sources):
    pair = "import Compiler.ZigAir.MemoryExecutionProofs\nimport Compiler.ZigAir.MemoryWordExchange\n"
    pair += without_imports((DIRECTORY / "MemoryWordPair.lean").read_text())
    result = [mutation_check(output, "pair-unchanged", pair, True, env, lean)]
    for name, before, after in (
        ("overlap-accepted", "if a + 4 ≤ b ∨ b + 4 ≤ a then", "if a ≤ b ∨ b ≤ a then"),
        ("missing-initialization", "let _ ← load state pointer", "let _ ← (Except.ok (.scalar .unit) : Except Fault Value)"),
        ("bypassed-entry-contract", "| .error fault => .finished (.error fault) state", "| .error _ => program.program.start args state"),
    ):
        if pair.count(before) != 1:
            raise ValueError("ambiguous entry-contract mutation: " + name)
        result.append(mutation_check(output, name, pair.replace(before, after), False, env, lean))
    prefix = "import Compiler.ZigAir.MemoryWordPair\nimport Compiler.ZigAir.MemoryByteExchangeTests\n"
    prefix += "namespace Compiler.ZigAir.GeneratedMemory\nopen MemoryAir\ndef fn_swap_u32 : WordPairProgram :=\n"
    suffix = '''
end Compiler.ZigAir.GeneratedMemory
open Compiler.ZigAir.Memory Compiler.ZigAir.GeneratedMemory in
example : fn_swap_u32.runFuel 160 [ByteExchange.Tests.view.pointer 0, ByteExchange.Tests.view.pointer 1]
    ByteExchange.Tests.caller = .finished (.ok (.scalar .unit))
      { ByteExchange.Tests.expected with nextId := 2, nextAddress := 40 } := by rfl'
'''
    original = prefix + WordSwapDecoder(record, sources).program(record) + suffix
    result.append(mutation_check(output, "captured-loop-unchanged", original, True, env, lean))
    for name, index, key, value in (
        ("wrong-second-byte", 23, "rhs", {"kind": "instruction", "index": 21}),
        ("missing-last-byte", 16, "operand", {"kind": "constant", "type": {"kind": "int", "bits": 64, "signedness": "unsigned"}, "value": 3}),
    ):
        changed = copy.deepcopy(record)
        changed["instructions"][index][key] = value
        altered = prefix + WordSwapDecoder(changed, sources).program(changed) + suffix
        if altered == original:
            raise ValueError("captured swap mutation was erased")
        result.append(mutation_check(output, name, altered, False, env, lean))
    for item in result:
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant",
                     (output / (item["name"] + ".stdout")).read_text(), re.I):
            raise ValueError("word-swap control hit a resource or syntax failure")
    return result


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.word-swap-entry-acceptance.v1", "status": "failed", "jobs": 4,
              "proofScope": "typedHeapWordPairEntryAndFiniteCapturedSwapObservations",
              "capturedSwapLoopVerified": False, "bodyFootprintVerified": False, "specializationSemanticsVerified": False,
              "nativeNoaliasVerified": False, "sourceSafetyVerified": False, "nativeBackendVerified": False, "wholeCompilerVerified": False}
    dispatcher_production = getattr(args, "dispatcher_production", False)
    dispatcher_preservation = getattr(args, "dispatcher_preservation", False) or dispatcher_production
    physical_dispatch = getattr(args, "physical_dispatch", False) or dispatcher_preservation
    physical_words = getattr(args, "physical_words", False) or physical_dispatch
    interner_callers = getattr(args, "interner_callers", False) or physical_words
    owned_continuation = getattr(args, "owned_continuation", False) or interner_callers
    scope_trace = getattr(args, "scope_trace", False) or owned_continuation
    resource_adapter = getattr(args, "resource_adapter", False) or scope_trace
    normalization = getattr(args, "normalization", False) or resource_adapter
    duplication = getattr(args, "duplication", False) or normalization
    allocation = getattr(args, "allocation", False) or duplication
    storage = getattr(args, "storage", False) or allocation
    prepared = getattr(args, "prepared", False) or storage
    copied = getattr(args, "copied", False) or prepared
    caller = getattr(args, "caller", False) or copied
    regions = getattr(args, "regions", False) or caller
    confinement = getattr(args, "confinement", False) or regions
    observations = getattr(args, "observations", False) or confinement
    invocation = getattr(args, "invocation", False) or observations
    module, roots = (INVOCATION_MODULE, INVOCATION_CLAIMS) if invocation else (MODULE, CLAIMS)
    if invocation:
        report.update(schema="oksolc.word-swap-invocation-acceptance.v1", proofScope="zigFreshAirInitializedWritableU32ArrayView",
                      allWordPairInputsVerified=False,
                      assumptions=["valid caller heap", "initialized writable u32 array view", "distinct contained indices",
                                   "sequential nonvolatile storage", "captured aarch64 macos ReleaseFast LLVM configuration"])
    if observations:
        module, roots = OBSERVATION_MODULE, OBSERVATION_CLAIMS
        report.update(schema="oksolc.word-swap-observations-acceptance.v1", primitiveObservationsVerified=False,
                      dataOperationSitesVerified=False, dynamicAddressConfinementVerified=False)
    if confinement:
        module, roots = CONFINEMENT_MODULE, CONFINEMENT_CLAIMS
        report.update(schema="oksolc.word-swap-confinement-acceptance.v1",
                      footprintScope="typedHeapArgumentRelativeDataPrimitiveAttempts",
                      nativePointerProvenanceVerified=False, physicalAddressPreservationVerified=False)
    if regions:
        module, roots = REGION_MODULE, REGION_CLAIMS
        report.update(schema="oksolc.word-swap-regions-acceptance.v1",
                      regionScope="typedHeapStableCallerAllocationsAndArgumentWordIntervals",
                      modeledAllocationStabilityVerified=False, modeledArgumentRegionsVerified=False)
    if caller:
        module, roots = CALLER_MODULE, CALLER_CLAIMS
        report.update(schema="oksolc.captured-swap-caller-acceptance.v1",
                      callerScope="restrictedSourceInsertionControlWithCapturedTypedHeapSwap",
                      capturedSwapCallerModelVerified=False, callerAllBudgetsClassified=False,
                      sourceTranslatorVerified=False, callerAirVerified=False, callerAllocationAndCopyVerified=False)
    if copied:
        import copied_sort_checks
        module, roots = copied_sort_checks.MODULE, CALLER_CLAIMS + copied_sort_checks.CLAIMS
        report.update(schema="oksolc.copied-sort-caller-acceptance.v1",
                      swapProofScope=report["proofScope"], proofScope="typedHeapSelectedDestinationCopySort",
                      swapAssumptions=report["assumptions"],
                      callerScope="restrictedSourceCopySortControlWithTypedCopyAndCapturedSwap",
                      typedCopySortVerified=False, typedCopyVerified=False, copyAirVerified=False,
                      nativeCopyVerified=False, callerAllocationVerified=False,
                      assumptions=["valid heap", "initialized readonly source view", "writable contained target view",
                                           "equal lengths", "non-overlapping logical views", "sequential nonvolatile storage"])
    if prepared:
        import prepared_normalization_checks
        module, roots = prepared_normalization_checks.MODULE, roots + prepared_normalization_checks.CLAIMS
        report.update(schema="oksolc.prepared-normalization-acceptance.v1",
                      selectedDestinationProofScope=report["proofScope"],
                      proofScope="typedHeapNormalizationPreparationAndLogicalOwnership",
                      normalizationOwnershipWithPreparationVerified=False,
                      normalizationInitializationMemoryVerified=False, normalizationDuplicationMemoryVerified=False,
                      normalizationReleaseMemoryVerified=False, nativeAllocatorVerified=False,
                      preparationFaultClosesOwnership=False,
                      preparationScope="normalReturnsCloseLogicalScope;semanticFaultsRetainLiveTokenAndReachedEffects",
                      allocatorBoundary="stateful external allocation/release; freshness, pairing and destination validity remain obligations")
    if storage:
        import storage_normalization_checks
        module, roots = storage_normalization_checks.MODULE, roots + storage_normalization_checks.CLAIMS
        report.update(schema="oksolc.normalization-storage-acceptance.v1",
                      proofScope="typedHeapNormalizationStorageAndOwnershipProjection",
                      allBudgetsStorageMetadataVerified=False, preparedOwnershipProjectionVerified=False,
                      preparedBufferReleaseContractVerified=False,
                      storageAssumptions=["valid typed heap", "registered full writable nonstack destination allocation",
                          "other logical argument allocations represented", "initialized readonly source with equal disjoint view",
                          "same allocation lifetime IDs across heaps"],
                      storageBoundary="selected destination already allocated; private payload unobserved until terminal projection; semantic faults never trigger invented cleanup")
    if allocation:
        import allocation_normalization_checks
        module, roots = allocation_normalization_checks.MODULE, roots + allocation_normalization_checks.CLAIMS
        report.update(schema="oksolc.normalization-allocation-contract-acceptance.v1",
                      proofScope="checkedExternalPersistentAllocationAndCapturedPreparation",
                      persistentAllocationContractVerified=False, allocatedPreparationVerified=False,
                      allocationAssumptions=["valid initial typed heap", "same logical/typed lifetime IDs",
                          "other nonempty argument allocations represented", "initialized readonly source",
                          "external allocator returns a disjoint aligned bounded region or OOM",
                          "fresh logical registry ID for admitted registration; collisions remain semantic faults"],
                      allocationBoundary="external native allocator framing, effects and pointer injection unproved; new payload unobserved until copy; collision retains accepted typed allocation and effects; no automatic fault cleanup")
    if duplication:
        import duplication_normalization_checks
        module, roots = duplication_normalization_checks.MODULE, roots + duplication_normalization_checks.CLAIMS
        report.update(schema="oksolc.normalization-duplication-contract-acceptance.v1",
                      proofScope="checkedPersistentAllocationAndExactTypedDuplication",
                      borrowedDuplicateContractVerified=False, normalizationProductionPathVerified=False,
                      duplicationBoundary="checked external allocation and typed memcpy contracts; logical descriptor length checked; exact contents and independent ownership on success; partial copy faults retain buffer and effects; production takeOwned integration still open")
    if normalization:
        import production_normalization_checks
        module, roots = production_normalization_checks.MODULE, roots + production_normalization_checks.CLAIMS
        report.update(schema="oksolc.normalization-production-acceptance.v1",
                      proofScope="sourceBoundNormalizationLifecycleUnderMemoryContracts",
                      trustBoundaryVersion=1, recursiveNormalizationMemoryBridgeVerified=False,
                      callerScratchContractDerived=False, modeledRegistryLifetimeVerified=False,
                      duplicationBoundary="exact typed duplication composed into production takeOwned under native external contracts",
                      normalizationAssumptions=["valid typed heap and allocator-owned persistent registry", "represented readonly source",
                          "successful fresh two-word caller stack allocation", "decoded commutativity agrees with the production item",
                          "native allocator supplies an aligned disjoint bounded region or ordinary OOM",
                          "native copy/free/layout and host execution satisfy version 1 contracts",
                          "reviewed complete-body source admission and generated freshness"],
                      normalizationBoundary="complete init/takeOwned/deinit lifecycle; ordinary OOM cleanup preserves effects; semantic faults retain reached state and are rejected; intervening caller graph operations and recursive resource projection remain open")
    if resource_adapter:
        import resource_normalization_checks
        module, roots = resource_normalization_checks.MODULE, roots + resource_normalization_checks.CLAIMS
        report.update(schema="oksolc.normalization-resource-adapter-acceptance.v1",
                      proofScope="sourceBoundNormalizationPhysicalOwnershipAdapterUnderMemoryContracts",
                      physicalOwnershipAdapterVerified=False,
                      resourceAdapterBoundary="exact PreparedPrimitives interpretation including semantic faults and partial effects; cursor/graph integration requires separate evidence")
    if scope_trace:
        import trace_normalization_checks
        module, roots = trace_normalization_checks.MODULE, roots + trace_normalization_checks.CLAIMS
        report.update(schema="oksolc.normalization-scope-trace-acceptance.v1",
                      proofScope="sourceBoundNormalizationPhysicalScopeReplayUnderMemoryContracts",
                      localPhysicalScopeReplayVerified=False,
                      scopeTraceBoundary="exact local physical transcript to Scoped.initScope/take/close with equal transferred contents; semantic faults reject before total projection; global recursive/graph execution binding remains open")
    if owned_continuation:
        import owned_interner_checks
        module, roots = owned_interner_checks.MODULE, roots + owned_interner_checks.CLAIMS
        report.update(schema="oksolc.interner-owned-continuation-acceptance.v1",
                      proofScope="sourceBoundOwnedCallerMemoryUnderGraphContracts",
                      ownedContinuationMemoryVerified=False, completeFindMemoryVerified=False, graphCallbackContractsVerified=False,
                      ownedContinuationBoundary="actual controlOwned/controlMiss with reached-state deferred cleanup; graph ownership contracts are pending compiler obligations; complete recursive/Scoped execution binding remains open")
    if interner_callers:
        import interner_caller_checks
        module, roots = interner_caller_checks.MODULE, roots + interner_caller_checks.CLAIMS
        report.update(schema="oksolc.interner-caller-memory-acceptance.v1",
                      proofScope="completeSourceBoundInternerControlUnderMemoryAndGraphContracts",
                      completeCallerControlMemoryVerified=False, queryImplementationsVerified=False,
                      completeCallerBoundary="actual find/forceEqual control with physical normalization and deferred cleanup; graph implementation, query refinement and same recursive execution remain open")
    if physical_words:
        import interner_physical_checks
        module, roots = interner_physical_checks.MODULE, roots + interner_physical_checks.CLAIMS
        report.update(schema="oksolc.interner-physical-words-acceptance.v1",
                      proofScope="sameCompletePhysicalInternerExecutionUnderMemoryAndSemanticGraphContracts",
                      samePhysicalCallerWordPreservationVerified=False,
                      physicalWordsBoundary="word preservation and memory cleanup for the same actual caller execution; native graph/query refinement and physical recursive simplifier induction remain open")
    if physical_dispatch:
        import physical_dispatch_checks
        module, roots = physical_dispatch_checks.MODULE, roots + physical_dispatch_checks.CLAIMS
        report.update(schema="oksolc.physical-dispatch-binding-acceptance.v1",
                      physicalDispatcherBindingVerified=False, physicalRecursivePreservationVerified=False,
                      physicalDispatchBoundary="one extracted dispatcher for logical and physical effects; recursive word/borrow induction and native argument/graph refinement remain open")
    if dispatcher_preservation:
        import physical_dispatch_preservation_checks
        module, roots = physical_dispatch_preservation_checks.MODULE, roots + physical_dispatch_preservation_checks.CLAIMS
        report.update(schema="oksolc.dispatcher-preservation-acceptance.v1",
                      physicalDispatcherPreservationVerified=False,
                      dispatcherPreservationBoundary="universal complete dispatcher borrowing and word transport under constructor contracts; native recursive constructor simulation, argument preparation and complete physical caller induction remain open")
    if dispatcher_production:
        import physical_dispatch_production_checks
        module, roots = physical_dispatch_production_checks.MODULE, roots + physical_dispatch_production_checks.CLAIMS
        report.update(schema="oksolc.dispatcher-production-acceptance.v1",
                      physicalDispatcherCallerCompositionVerified=False,
                      borrowedConstructorFrameVerified=False, completeRecursiveConstructorsVerified=False,
                      dispatcherProductionBoundary="same complete physical find/forceEqual execution derives dispatcher ownership and word preservation; native recursive constructor simulation, argument preparation, recursive induction and graph/query implementation remain open")
    try:
        report["inputs"], report["leanInputs"] = inputs(normalization), lean_check.source_inputs()
        report["toolchainReportSha256"] = digest(args.toolchain)
        toolchain = read_json(args.toolchain)
        report["toolchainBuildStatus"] = toolchain["status"]
        exporter = [p for p in toolchain["freshAirCapturePatch"] if p["file"] == "src/SemanticExport.zig"]
        if len(exporter) != 1 or exporter[0]["afterSha256"] != digest(ROOT / "lean/zig_air/SemanticExport.zig"):
            raise ValueError("capturing toolchain has different exporter bytes")
        env, _, tools = lean_check.toolchain(args.lean_bin, 4)
        if normalization:
            report["normalizationSourceBinding"] = production_normalization_checks.bindings()
            run(output, "normalization-python-tests", [sys.executable, "-m", "unittest",
                "test_compiler_cache", "test_compiler_interner"], cwd=ROOT / "test/lean", env=env)
        if owned_continuation:
            report["ownedSourceBinding"] = owned_interner_checks.bindings()
        if interner_callers:
            report["callerSourceBinding"] = interner_caller_checks.bindings()
        if physical_dispatch:
            report["physicalDispatchSourceBinding"] = physical_dispatch_checks.bindings()
            run(output, "physical-dispatch-python-tests", [sys.executable, "-m", "unittest",
                *["test_compiler_" + name for name in physical_dispatch_checks.GENERATORS]], cwd=ROOT / "test/lean", env=env)
        if dispatcher_production:
            report["recursiveConstructorPremiseInventory"] = physical_dispatch_production_checks.constructor_inventory.check()
            report["constructorFrameSourceBinding"] = physical_dispatch_production_checks.constructor_frame_checks.bindings()
            report["borrowedConstructorSourceBinding"] = physical_dispatch_production_checks.borrowed_constructor_checks.bindings()
            report["borrowedQuerySourceBinding"] = physical_dispatch_production_checks.borrowed_query_checks.bindings()
            run(output, "constructor-python-tests", [sys.executable, "-m", "unittest", "test_compiler_constructor", "test_constructor_inventory"],
                cwd=ROOT / "test/lean", env=env)
        compiler, lib = Path(toolchain["compiler"]["path"]), Path(toolchain["compiler"]["zigLibDir"])
        run(output, "python-tests", [sys.executable, "-m", "unittest", "discover", "-s", "test/lean", "-p", "test_zig_air_*.py"], cwd=ROOT, env=env)
        clients = [module]
        if invocation:
            clients += ["Compiler.ZigAir.MemoryExpSafetyTests", "Compiler.ZigAir.MemoryFillInvocationTests",
                        "Compiler.Extraction.InsertionSortHeapTests"]
        run(output, "preflight", [tools["lake"]["path"], "build", *clients], cwd=ROOT / "lean", env=env)
        capture(argparse.Namespace(toolchain=args.toolchain, source=SOURCE, output=output / "capture", root=[CALLER], mode="ReleaseFast"))
        path = output / "capture/report.json"
        generated = output / "GeneratedWordSwap.lean"
        manifest = generate(path, CALLER, lib / "std/mem.zig", generated, output / "generation.json")
        report["generationSha256"] = digest(output / "generation.json")
        if generated.read_bytes() != (DIRECTORY / generated.name).read_bytes():
            raise ValueError("committed word-swap body differs from fresh captured AIR")
        if (manifest["bodyInstructions"] != 30 or manifest["sourceGuards"] != 0 or manifest["loops"] != [12] or
                manifest["repeatTargets"] != [12] or manifest["runtimeParameterIndices"] != [1, 2]):
            raise ValueError("captured word-swap body inventory changed")
        captured = read_json(path)
        record = read_json(captured_path(path, captured["functions"][manifest["selectedCall"]["callee"]]))
        if caller:
            report["callerBinding"] = caller_binding(output, env, tools["lean"]["path"], lib)
        report["audit"] = audit(output, env, tools["lean"]["path"], module, roots)
        if copied:
            report["copySortDependencies"] = copied_sort_checks.audit(output)
            report["copyControls"] = copied_sort_checks.check_word_copy.controls(output, env, tools["lean"]["path"])
            report["copySortControls"] = copied_sort_checks.controls(output, env, tools["lean"]["path"])
            report["copySortNativeBinding"] = copied_sort_checks.bindings(output, env, tools["lean"]["path"])
        if prepared:
            report["preparedSourceBinding"] = prepared_normalization_checks.source_binding(output)
            report["preparedDependencies"] = prepared_normalization_checks.audit(output)
            report["preparedControls"] = prepared_normalization_checks.controls(output, env, tools["lean"]["path"])
        if storage:
            report["storageDependencies"] = storage_normalization_checks.audit(output)
            report["storageControls"] = storage_normalization_checks.controls(output, env, tools["lean"]["path"])
        if allocation:
            report["allocationDependencies"] = allocation_normalization_checks.audit(output)
            report["allocationControls"] = allocation_normalization_checks.controls(output, env, tools["lean"]["path"])
        if duplication:
            report["duplicationDependencies"] = duplication_normalization_checks.audit(output)
            report["duplicationControls"] = duplication_normalization_checks.controls(output, env, tools["lean"]["path"])
        if normalization:
            report["normalizationDependencies"] = production_normalization_checks.audit(output)
            report["normalizationControls"] = production_normalization_checks.controls(output, env, tools["lean"]["path"])
        if resource_adapter:
            report["resourceAdapterDependencies"] = resource_normalization_checks.audit(output)
            report["resourceAdapterControls"] = resource_normalization_checks.controls(output, env, tools["lean"]["path"])
        if scope_trace:
            report["scopeTraceDependencies"] = trace_normalization_checks.audit(output)
            report["scopeTraceControls"] = trace_normalization_checks.controls(output, env, tools["lean"]["path"])
        if owned_continuation:
            report["ownedContinuationDependencies"] = owned_interner_checks.audit(output)
            report["ownedContinuationControls"] = owned_interner_checks.controls(output, env, tools["lean"]["path"])
        if interner_callers:
            report["completeCallerDependencies"] = interner_caller_checks.audit(output)
            report["completeCallerControls"] = interner_caller_checks.controls(output, env, tools["lean"]["path"])
        if physical_words:
            report["physicalWordsDependencies"] = interner_physical_checks.audit(output)
            report["physicalWordsControls"] = interner_physical_checks.controls(output, env, tools["lean"]["path"])
        if physical_dispatch:
            report["physicalDispatchDependencies"] = physical_dispatch_checks.audit(output)
            report["physicalDispatchControls"] = physical_dispatch_checks.controls(output, env, tools["lean"]["path"])
        if dispatcher_preservation:
            report["dispatcherPreservationDependencies"] = physical_dispatch_preservation_checks.audit(output)
            report["dispatcherPreservationControls"] = physical_dispatch_preservation_checks.controls(output, env, tools["lean"]["path"])
        if dispatcher_production:
            report["dispatcherProductionDependencies"] = physical_dispatch_production_checks.audit(output)
            report["dispatcherProductionControls"] = physical_dispatch_production_checks.controls(output, env, tools["lean"]["path"])
        report["controls"] = controls(output, env, tools["lean"]["path"], record, manifest["links"]["sources"])
        if invocation:
            report["invocationControls"] = invocation_controls(output, env, tools["lean"]["path"], record, manifest["links"]["sources"])
        if observations:
            report["observationControls"] = observation_controls(output, env, tools["lean"]["path"])
        if confinement:
            report["confinementControls"] = confinement_controls(output, env, tools["lean"]["path"])
        if regions:
            report["regionControls"] = region_controls(output, env, tools["lean"]["path"])
        if caller:
            report["callerControls"] = caller_controls(output, env, tools["lean"]["path"])
            native_output = output / "caller-native"
            native_output.mkdir()
            report["callerNative"] = check_insertion_sort.native(native_output, compiler, lib.parent, env)
        if copied:
            copy_native_output = output / "copy-sort-native"
            copy_native_output.mkdir()
            report["copySortNative"] = copied_sort_checks.native(copy_native_output, compiler, lib.parent, env)
        proof, artifacts = prove.check_module(module, roots, lean_bin=args.lean_bin, jobs=4, fresh=True)
        directory = output / "proof"
        directory.mkdir()
        for name, data in artifacts.items():
            (directory / name).write_bytes(data)
        write_json(directory / "report.json", proof)
        report["proofReportSha256"] = digest(directory / "report.json")
        if (proof.get("status") != "passed" or proof.get("freshKernelReplay") is not True or
                proof.get("replayIncludesImports") is not True or proof.get("auditedDeclarations") != roots):
            raise ValueError("word-swap fresh kernel replay failed")
        # Shared signature/argument decoding also governs ordinary byte AIR.
        # Re-capture it and replay its complete invocation proofs and native cases.
        check_byte_invocation.check(argparse.Namespace(toolchain=args.toolchain, lean_bin=args.lean_bin,
                                                       output=output / "byte-invocation-regression"))
        regression = output / "byte-invocation-regression/report.json"
        report["byteInvocationRegressionSha256"] = digest(regression)
        if read_json(regression)["status"] != "passed":
            raise ValueError("ordinary byte invocation regression failed")
        if (inputs(normalization) != report["inputs"] or lean_check.source_inputs() != report["leanInputs"] or
                digest(args.toolchain) != report["toolchainReportSha256"] or digest(compiler) != toolchain["compiler"]["sha256"] or
                source_identity(lib.parent) != toolchain["sourceTree"]):
            raise ValueError("word-swap acceptance inputs changed")
        report.update(status="passed", entrySeparationVerified=True, capturedBodyDecoded=True, auditedDeclarations=len(roots))
        if invocation:
            report.update(capturedSwapLoopVerified=True, capturedArraySwapVerified=True)
        if observations:
            report.update(primitiveObservationsVerified=True, dataOperationSitesVerified=True)
        if confinement:
            report.update(dynamicAddressConfinementVerified=True, bodyFootprintVerified=True)
        if regions:
            report.update(modeledAllocationStabilityVerified=True, modeledArgumentRegionsVerified=True)
        if caller:
            report.update(capturedSwapCallerModelVerified=True, callerAllBudgetsClassified=True)
        if copied:
            report.update(typedCopySortVerified=True, typedCopyVerified=True)
        if prepared:
            report.update(normalizationOwnershipWithPreparationVerified=True)
        if storage:
            report.update(allBudgetsStorageMetadataVerified=True, preparedOwnershipProjectionVerified=True,
                          preparedBufferReleaseContractVerified=True)
        if allocation:
            report.update(persistentAllocationContractVerified=True, allocatedPreparationVerified=True)
        if duplication:
            report.update(borrowedDuplicateContractVerified=True)
        if normalization:
            report.update(normalizationProductionPathVerified=True, normalizationInitializationMemoryVerified=True,
                          normalizationDuplicationMemoryVerified=True, normalizationReleaseMemoryVerified=True,
                          callerScratchContractDerived=True, modeledRegistryLifetimeVerified=True)
        if resource_adapter:
            report.update(physicalOwnershipAdapterVerified=True)
        if scope_trace:
            report.update(localPhysicalScopeReplayVerified=True)
        if owned_continuation:
            report.update(ownedContinuationMemoryVerified=True)
        if interner_callers:
            report.update(completeCallerControlMemoryVerified=True)
        if physical_words:
            report.update(samePhysicalCallerWordPreservationVerified=True)
        if physical_dispatch:
            report.update(physicalDispatcherBindingVerified=True)
        if dispatcher_preservation:
            report.update(physicalDispatcherPreservationVerified=True)
        if dispatcher_production:
            report.update(physicalDispatcherCallerCompositionVerified=True, borrowedConstructorFrameVerified=True)
    finally:
        write_json(output / "report.json", report)
    print("Complete physical callers compose dispatcher preservation; native recursive simulation and induction remain open." if dispatcher_production else
          "Universal dispatcher preservation passed under constructor contracts; complete physical recursion remains open." if dispatcher_preservation else
          "Physical dispatcher binding passed; universal physical recursive preservation remains open." if physical_dispatch else
          "Same physical caller word/memory preservation passed under graph contracts; native and recursive integration remain open." if physical_words else
          "Complete interner caller control passed under memory/graph contracts; native queries and recursive integration remain open." if interner_callers else
          "Owned caller memory continuation passed under graph contracts; complete recursive integration remains open." if owned_continuation else
          "Local physical scope replay passed; complete recursive/graph execution binding remains open." if scope_trace else
          "Physical normalization ownership adapter passed; recursive cursor and graph integration remain open." if resource_adapter else
          "Complete normalization lifecycle passed under version 1 memory contracts; recursive integration remains open." if normalization else
          "Borrowed duplication contract passed; complete normalization production integration remains open." if duplication else
          "Persistent allocation contract and captured preparation passed; native allocator and normalization integration remain open." if allocation else
          "Preparation storage and ownership projection passed; allocation and native integration remain open." if storage else
          "Preparation-aware ownership passed; native allocator and memory integration remain open." if prepared else
          "Selected-destination copy/sort passed; native preservation remains open." if copied else
          "Captured array swap invocation passed; native preservation remains open." if invocation else
          "Word-pair entry and captured swap observations passed; universal loop and native preservation remain open.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", type=Path)
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--invocation", action="store_true", help="audit complete captured array-view swap refinement")
    parser.add_argument("--observations", action="store_true", help="also audit primitive observations and complete data-operation sites")
    parser.add_argument("--confinement", action="store_true", help="also prove bounded data operands for every execution prefix")
    parser.add_argument("--regions", action="store_true", help="also prove stable caller allocation metadata and modeled word regions")
    parser.add_argument("--caller", action="store_true", help="compose captured swap with source-bound insertion control, retaining OOM and suspension")
    parser.add_argument("--copied", action="store_true", help="also prove readonly copy into the selected destination before captured-swap sorting")
    parser.add_argument("--prepared", action="store_true", help="carry captured copy/sort effects through normalization ownership and distinguish semantic faults")
    parser.add_argument("--storage", action="store_true", help="also prove storage metadata at every budget and establish the initialized ownership/release contract")
    parser.add_argument("--allocation", action="store_true", help="derive captured preparation's destination from a checked external persistent allocation contract")
    parser.add_argument("--duplication", action="store_true", help="check exact owned duplication for normalization's borrowed take path, preserving partial copy faults")
    parser.add_argument("--normalization", action="store_true", help="verify the complete source-bound normalization lifecycle under version 1 memory contracts")
    parser.add_argument("--resource-adapter", action="store_true", help="connect the source-bound ownership protocol to exact physical normalization execution, including faults")
    parser.add_argument("--scope-trace", action="store_true", help="check exact physical invocation replay into Scoped normalization resources, retaining rejected faults")
    parser.add_argument("--owned-continuation", action="store_true", help="check actual owned interner control with physical take, graph callbacks and reached-state deferred cleanup")
    parser.add_argument("--interner-callers", action="store_true", help="check complete extracted find/forceEqual control with physical normalization and cleanup")
    parser.add_argument("--physical-words", action="store_true", help="compose word preservation and cleanup for the same complete physical interner execution")
    parser.add_argument("--physical-dispatch", action="store_true", help="check the complete shared dispatcher with physical recursive constructor effects")
    parser.add_argument("--dispatcher-preservation", action="store_true", help="prove universal shared dispatcher borrowing and word transport under explicit recursive constructor contracts")
    parser.add_argument("--dispatcher-production", action="store_true", help="compose the actual dispatcher proofs into complete physical find/forceEqual preservation")
    parser.add_argument("--proof-component", action="store_true", help="check only --dispatcher-production's proof component; no native source capture")
    parser.add_argument("--preflight", action="store_true", help="cached proof-component audit and controls, without fresh replay")
    parser.add_argument("--zig-lib-dir", type=Path, help="pin Zig library inputs for the proof-component report")
    args = parser.parse_args()
    if args.proof_component:
        if not args.dispatcher_production or not args.zig_lib_dir or args.toolchain:
            parser.error("--proof-component requires --dispatcher-production and --zig-lib-dir, without --toolchain")
        if any(value is True for name, value in vars(args).items()
               if name not in {"proof_component", "dispatcher_production", "preflight"}):
            parser.error("--proof-component cannot be combined with other native gate modes")
        import physical_dispatch_production_checks
        physical_dispatch_production_checks.check_component(args)
    else:
        if not args.toolchain or args.preflight or args.zig_lib_dir:
            parser.error("native gates require --toolchain; --preflight and --zig-lib-dir require --proof-component")
        check(args)
