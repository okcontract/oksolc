#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Check pinned insertion control and its recursive normalization composition.
// Copyright (C) 2026 OKcontract Pte. Ltd.

Restricted source translation and native byte exchange remain trusted boundaries.
Native cases are finite regression evidence, never a backend preservation proof.
"""

import argparse
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "lean"))
sys.path.insert(0, str(ROOT / "lean/zig_air"))
import environment as lean_check
import prove
import extract_insertion_sort as extraction
from build_toolchain import REVISION, check_checkout, digest, run, source_identity, write_json
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
from zig_insertion_sort_native import CASES, EXCHANGES
import recursive_preparation_checks

LAWS = ["adjacent_exchange", "insert_total", "passes_total", "run_total", "run_sortIds",
        "sortIds_perm", "checked_total", "iteration_indices", "normalize_word", "unfold_safe", "detailed_verified"]
TESTS = [name for name, _ in CASES] + ["exhausted", "exhausted_keeps_exchange", "invalid_inner",
        "invalid_stop", "zero_guard_skips_reads", "native_max_counter", "checked_small"]
CLAIMS = ["Compiler.Extraction.InsertionSort." + name for name in LAWS]
CLAIMS += ["Compiler.Extraction.InsertionSort.Tests." + name for name in TESTS]
ARRAY_LAWS = ["number_valid", "number_typed", "array_layout", "writable_fresh", "allocation_fault",
              "array_access", "element_access", "view_width", "element_pointer", "array_view", "array_leaf",
              "writable_store", "write_total", "write_offset_frame", "write_frame", "write_represents",
              "write_allocation_frame", "exchange_of_effects", "exchange_refines", "element_regions"]
CLAIMS += ["Compiler.ZigAir.Memory.WordArray." + name for name in ARRAY_LAWS]
CLAIMS += ["Compiler.Extraction.InsertionSort." + name for name in
           ("adjacent_memory_access", "adjacent_memory_exchange", "view_counter_bounds")]
MEMORY_TESTS = [name for name, _, _ in EXCHANGES] + ["valid_caller", "writable_caller", "represented_caller",
    "larger_allocation_not_view", "empty_view_rejects", "over_extent_rejects", "uninitialized_valid", "uninitialized_rejects",
    "readonly_rejects", "dead_rejects", "misalignment_rejects", "alias_not_disjoint", "alias_typed_observation",
    "typed_exchange_witness"]
CLAIMS += ["Compiler.Extraction.InsertionSort.MemoryTests." + name for name in MEMORY_TESTS]
PROJECTION_LAWS = ["insert_zero", "insert_succ", "passes_zero", "passes_succ", "run_passes"]
CLAIMS += ["Compiler.Extraction.InsertionSort." + name for name in PROJECTION_LAWS]
CLAIMS += ["Compiler.ZigAir.Memory.WordArray." + name for name in
           ("Frame.refl", "Frame.trans", "frame_store", "exchange_frame")]
CLAIMS += ["Compiler.Extraction.InsertionSort.Heap." + name for name in
           ("read_represents", "exchange_refines", "insert_refines", "passes_refines", "run_refines", "run_result")]
HEAP_TESTS = [name for name, _ in CASES] + ["full_run_witness", "readonly_rejects", "dead_rejects", "width_rejects",
    "empty_skips_reads", "partial_valid", "partial_keeps_exchange", "partial_values", "exhausted_keeps_exchange"]
CLAIMS += ["Compiler.Extraction.InsertionSort.HeapTests." + name for name in HEAP_TESTS]
CLAIMS += recursive_preparation_checks.CLAIMS
MODULE = "Compiler.Extraction.InternerPreparationTests"


def inputs():
    # Includes transitive Python imports and all Lean files via source_inputs.
    paths = list((ROOT / "lean").rglob("*.py")) + list((ROOT / "test/lean").glob("*.py"))
    paths += [extraction.SOURCE, ROOT / "test/lean/zig_insertion_sort.zig"]
    return {str(p.relative_to(ROOT)): digest(p) for p in sorted(paths) if ".lake" not in p.parts}


def controls(output, env, lean, generated):
    witnesses = '''
namespace Compiler.Extraction.InsertionSort
example : run [3, 2, 1] = .ok [1, 2, 3] := by rfl
example : passes 1 2 1 [2, 1] = .fault .incomplete [1, 2] := by rfl
example : insert 2 [2, 1] = .fault .bounds [2, 1] := by rfl
end Compiler.Extraction.InsertionSort
'''
    base = "import Compiler.Extraction.Builder\nimport Init.Data.List.Nat.Perm\n"
    base += without_imports((ROOT / "lean/Compiler/Extraction/InsertionSortModel.lean").read_text())
    base += without_imports(generated)
    original = base + witnesses
    result = [mutation_check(output, "unchanged-control", original, True, env, lean)]
    for name, before, after in (
        ("duplicated-exchange-value", ".set right current", ".set right previous"),
        ("lost-exchange", "(items.set left previous).set right current", "items"),
        ("wrong-outer-guard", "if i < stop then", "if i > stop then"),
        ("skip-first-pass", "length 1 state", "length 2 state"),
        ("lost-fault-effects", ".fault reason after", ".fault reason []"),
        ("fault-becomes-success", ".fault reason after", ".ok after"),
        ("reversed-comparator", "a.toNat < b.toNat", "a.toNat > b.toNat"),
    ):
        if original.count(before) != 1:
            raise ValueError("ambiguous control mutation: " + name)
        result.append(mutation_check(output, name, original.replace(before, after), False, env, lean))
    # The universal theorem itself rejects an exchange that duplicates an ID.
    proof = base + without_imports((ROOT / "lean/Compiler/Extraction/InsertionSortProjection.lean").read_text())
    proof += without_imports((ROOT / "lean/Compiler/Extraction/InsertionSortProofs.lean").read_text())
    result.append(mutation_check(output, "unchanged-universal-proof", proof, True, env, lean))
    result.append(mutation_check(output, "universal-duplicated-id",
                                 proof.replace(".set right current", ".set right previous"), False, env, lean))
    # Reject resource/parser accidents as purported semantic negative evidence.
    for record in result:
        stream = (output / (record["name"] + ".stdout")).read_text()
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant", stream, re.I):
            raise ValueError("control hit a resource or syntax failure: " + record["name"])
    return result


def closure_audit(output, env, lean):
    source = '''import Compiler.Extraction.InternerPreparationTests
import Contract.Check.Declarations
import Lean.Elab.Command
open Lean Elab Command Contract.Check in
run_cmd do
  let roots := #[
''' + ",\n".join("    ``" + name for name in CLAIMS) + ''']
  let mut claims := #[]
  for root in roots do
    let .ok dependencies := Declarations.closure (← getEnv) #[root]
      | throwError "invalid dependency closure: {root}"
    let .ok axioms := Declarations.axioms dependencies
      | throwError "disallowed axiom: {root}"
    let some info := (← getEnv).find? root | throwError "missing theorem: {root}"
    unless info matches .thmInfo _ do throwError "not a theorem: {root}"
    claims := claims.push <| Json.mkObj [
      ("theorem", .str root.toString), ("statement", Declarations.expression info.type),
      ("axioms", toJson axioms), ("dependencies", toJson (dependencies.map (·.name.toString)))]
  liftIO <| IO.println (Json.mkObj [("claims", .arr claims)]).compress
'''
    (output / "closure-audit.lean").write_text(source)
    run(output, "closure-audit", [lean, "-DwarningAsError=true", output / "closure-audit.lean"],
        cwd=ROOT / "lean", env=env)
    raw = (output / "closure-audit.stdout").read_bytes()
    # Retain large JSON as structured evidence, not a giant log line.
    (output / "closure-audit.json").write_bytes(raw)
    audit = json.loads(raw)
    if [claim["theorem"] for claim in audit["claims"]] != CLAIMS:
        raise ValueError("unexpected theorem dependency audit")
    for claim in audit["claims"]:
        if not set(claim["axioms"]) <= {"propext", "Quot.sound", "Classical.choice"}:
            raise ValueError("unexpected theorem axiom")
        name = claim["theorem"].removeprefix("Compiler.Extraction.InsertionSort.")
        if name in ("sortIds_perm", "normalize_word", "unfold_safe", "detailed_verified"):
            required = {"insert", "passes", "run", "insertUsing", "passesUsing", "runUsing", "listOperations",
                        "insert_total", "passes_total", "run_total"}
            if name != "sortIds_perm":
                required.add("sortIds_perm")
            if not {"Compiler.Extraction.InsertionSort." + n for n in required} <= set(claim["dependencies"]):
                raise ValueError("theorem lost its generated insertion dependency: " + name)
        if name in ("adjacent_memory_access", "adjacent_memory_exchange", "view_counter_bounds"):
            required = {"Compiler.ZigAir.Memory.State.valid", "Compiler.ZigAir.Memory.WordArray.Writable"}
            if name == "adjacent_memory_exchange":
                required |= {"Compiler.ZigAir.Memory.store", "Compiler.ZigAir.Memory.WordArray.write_total",
                             "Compiler.ZigAir.Memory.WordArray.exchange", "Compiler.Extraction.InsertionSort.adjacent_exchange"}
            if not required <= set(claim["dependencies"]):
                raise ValueError("theorem lost its checked memory dependency: " + name)
        if name in ("Heap.run_refines", "Heap.run_result"):
            required = {"Compiler.Extraction.InsertionSort." + n for n in
                        ("insertUsing", "passesUsing", "runUsing", "sortIds", "Heap.operations", "Heap.read",
                         "Heap.exchange", "Heap.Related", "Heap.insert_refines", "Heap.passes_refines")}
            required |= {"Compiler.ZigAir.Memory.WordArray." + n for n in
                         ("Writable", "Represents", "Frame", "element_pointer", "view_width", "write_total", "exchange_frame")}
            if not required <= set(claim["dependencies"]):
                raise ValueError("heap theorem lost its control or memory dependency: " + name)
    return {"sha256": digest(output / "closure-audit.json"), "claims": len(CLAIMS)}


def memory_controls(output, env, lean):
    base = ROOT / "lean/Compiler/ZigAir"
    original = "import Compiler.ZigAir.MemoryAllocationLaws\nimport Compiler.ZigAir.MemoryPointers\n"
    original += "".join(without_imports((base / name).read_text()) for name in
                       ("MemoryWordArray.lean", "MemoryWordArrayWrites.lean", "MemoryWordExchange.lean"))
    original += '''
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray in
example : exchange {} ⟨0, 0, 0⟩ 0 0 = (.error .sourceBounds, {}) := by rfl
'''
    result = [mutation_check(output, "memory-unchanged", original, True, env, lean)]
    views = "import Compiler.ZigAir.MemoryAllocationLaws\nimport Compiler.ZigAir.MemoryPointers\n"
    definitions = without_imports((base / "MemoryWordArrayTypes.lean").read_text())
    definitions = definitions.replace("end Compiler.ZigAir.Memory.WordArray", "")
    definitions = definitions.replace("Compiler.ZigAir.Memory.WordArray", "Compiler.ZigAir.Memory.WordArrayControl")
    views += definitions + '''
example : (View.mk 0 1 2).address 0 = ⟨0, 4⟩ := by rfl
example : ¬Writable ⟨[(0, ⟨16, .array 1 word, [], false, false⟩)], 1, 20⟩ ⟨0, 0, 1⟩ := by
  simp [Writable, Heap.lookup]
end Compiler.ZigAir.Memory.WordArrayControl
'''
    result.append(mutation_check(output, "memory-view-unchanged", views, True, env, lean))
    for name, before, after in (
        ("memory-wrong-stride", "⟨view.allocation, (view.first + index) * 4⟩", "⟨view.allocation, (view.first + index) * 8⟩"),
        ("memory-readonly-capability", "cell.type = .array extent word ∧ cell.writable = true ∧", "cell.type = .array extent word ∧ cell.writable = false ∧"),
        ("memory-lost-source-bound", "if left < view.length ∧ right < view.length then", "if left ≤ view.length ∧ right ≤ view.length then"),
        ("memory-duplicates-right", "match store middle (view.pointer right) a with", "match store middle (view.pointer right) b with"),
    ):
        # View controls isolate the definitions: a changed stride can cause
        # cascading elaboration limits in the full symbolic proof clients.
        # Resource failures are not accepted as semantic rejection evidence.
        client = views if name in ("memory-wrong-stride", "memory-readonly-capability") else original
        if client.count(before) != 1:
            raise ValueError("ambiguous memory control: " + name)
        result.append(mutation_check(output, name, client.replace(before, after), False, env, lean))
    for record in result:
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant",
                     (output / (record["name"] + ".stdout")).read_text(), re.I):
            raise ValueError("memory control hit a resource or syntax failure: " + record["name"])
    return result


def heap_controls(output, env, lean):
    base = ROOT / "lean/Compiler/Extraction"
    original = "import Compiler.Extraction.InsertionSortMemory\nimport Compiler.ZigAir.MemoryWordFrame\n"
    original += "".join(without_imports((base / name).read_text()) for name in
                        ("InsertionSortHeap.lean", "InsertionSortHeapProofs.lean"))
    result = [mutation_check(output, "heap-unchanged", original, True, env, lean)]
    for name, before, after in (
        ("heap-wrong-read", "elementPointer state view.buffer index", "elementPointer state view.buffer 0"),
        ("heap-lost-exchange", "WordArray.exchange state view left right", "WordArray.exchange state view left left"),
    ):
        if original.count(before) != 1:
            raise ValueError("ambiguous heap control: " + name)
        result.append(mutation_check(output, name, original.replace(before, after), False, env, lean))
    for record in result:
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant",
                     (output / (record["name"] + ".stdout")).read_text(), re.I):
            raise ValueError("heap control hit a resource or syntax failure: " + record["name"])
    return result


def native(output, zig, tree, env):
    wrapper = ROOT / "test/lean/zig_insertion_sort.zig"
    result = {}
    for mode in ("ReleaseFast", "ReleaseSafe", "Debug"):
        directory = output / mode
        directory.mkdir()
        library = directory / "insertion.dylib"
        run(directory, "build", [zig, "build-lib", wrapper, "--zig-lib-dir", tree / "lib",
            "-dynamic", "-fllvm", "-fno-incremental", "-O" + mode, "-femit-bin=" + str(library),
            "--cache-dir", directory / "cache", "--global-cache-dir", directory / "global-cache"], env=env)
        run(directory, "native", [sys.executable, ROOT / "test/lean/zig_insertion_sort_native.py",
            "--library", library, "--output", directory / "observations.json"], env=env)
        all_observations = json.loads((directory / "observations.json").read_text())
        observations = all_observations["cases"]
        expected = [{"case": name, "input": values, "expected": [0xDEADBEEF, *sorted(values), 0xBAADF00D],
                     "actual": [0xDEADBEEF, *sorted(values), 0xBAADF00D]} for name, values in CASES]
        if observations != expected:
            raise ValueError("native observations do not match the checked model case inputs")
        expected_exchanges = [{"case": name, "input": [a, b], "left": 2, "right": 1,
            "expected": [0xDEADBEEF, b, a, 0xBAADF00D], "actual": [0xDEADBEEF, b, a, 0xBAADF00D]}
            for name, a, b in EXCHANGES]
        if all_observations["exchanges"] != expected_exchanges:
            raise ValueError("native exchange observations do not match checked memory-model inputs")
        result[mode] = {"status": "passed", "cases": len(observations), "librarySha256": digest(library),
                        "exchanges": len(expected_exchanges),
                        "observationsSha256": digest(directory / "observations.json")}
    return result


def check(args):
    output, tree, zig = args.output.resolve(), args.zig_tree.resolve(), args.zig.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.insertion-sort-acceptance.v1", "status": "failed", "jobs": 4,
              "proofScope": "restrictedZigSourceControl", "sourceTranslatorVerified": False,
              "nativeMemoryRefinementVerified": False, "nativeBackendVerified": False,
              "wholeCompilerVerified": False,
              "preparationResourceEffectsVerified": False, "normalizationMemoryResourceBridgeVerified": False,
              "memoryScope": {
                  "model": "existing typed AIR heap; u32 array sub-slices",
                  "assumptions": ["valid incoming heap", "live writable typed array and contained slice",
                                  "initialized slice contents for complete heap-sort refinement"],
                  "claims": ["successful element pointers and stores", "distinct element regions are disjoint",
                             "typed exchange refines generated list updates", "heap validity and views preserved",
                             "unchanged allocation counters and unrelated allocations",
                             "terminating shared heap loops agree with sortIds", "word loads outside the slice preserved"],
                  "excluded": ["native std.mem.swap byte-loop refinement", "memcpy correctness",
                               "native allocator and pointer correspondence",
                               "frontend/backend preservation", "whole compiler"]}}
    try:
        check_checkout(output, tree, "zig-before")
        report["zigRevision"] = REVISION
        report["pythonInputs"], report["leanInputs"] = inputs(), lean_check.source_inputs()
        report["zigLibrary"] = source_identity(tree / "lib")
        report["zig"] = {"path": str(zig), "sha256": digest(zig)}
        env, _, tools = lean_check.toolchain(args.lean_bin, 4)
        env["INSERTION_ZIG_TREE"] = str(tree)
        run(output, "zig-version", [zig, "version"], env=env)
        if (output / "zig-version.stdout").read_text().strip() != "0.17.0":
            raise ValueError("Zig must be version 0.17.0")
        run(output, "format", [zig, "fmt", "--check", ROOT / "test/lean/zig_insertion_sort.zig"], env=env)
        run(output, "python-tests", [sys.executable, "-m", "unittest", "discover", "-s", "test/lean",
                                    "-p", "test_insertion_sort.py"], cwd=ROOT, env=env)
        generated = extraction.extract((tree / "lib/std/sort.zig").read_bytes(), extraction.SOURCE.read_bytes())
        (output / "InsertionSortProgram.lean").write_text(generated)
        if generated != extraction.OUTPUT.read_text():
            raise ValueError("committed sort program is stale")
        report["generatedSha256"] = digest(extraction.OUTPUT)
        # Cached checks precede expensive fresh kernel replay and native builds.
        run(output, "preflight", [tools["lake"]["path"], "build", MODULE],
            cwd=ROOT / "lean", env=env)
        report["closureAudit"] = closure_audit(output, env, tools["lean"]["path"])
        report["preparationDependencies"] = recursive_preparation_checks.audit(output)
        report["preparationControls"] = recursive_preparation_checks.controls(output, env, tools["lean"]["path"])
        bindings = "import Compiler.Extraction.InsertionSortTests\nopen Compiler.Extraction.InsertionSort\n"
        for name, values in CASES:
            bindings += "example : run " + str(values) + " = .ok " + str(sorted(values)) + " := Tests." + name + "\n"
        report["nativeModelBinding"] = mutation_check(output, "native-model-binding", bindings, True, env, tools["lean"]["path"])
        bindings = "import " + MODULE + "\nopen Compiler.Extraction.InsertionSort.MemoryTests Compiler.ZigAir.Memory.WordArray\n"
        for name, a, b in EXCHANGES:
            words = ", ".join(f".ok (number {n})" for n in (0xDEADBEEF, b, a, 0xBAADF00D, 99))
            bindings += f"example : pairObservation {a} {b} = (.ok (), [{words}]) := {name}\n"
        report["nativeMemoryModelBinding"] = mutation_check(output, "native-memory-model-binding", bindings, True, env, tools["lean"]["path"])
        report["nativeMemoryObservationProjection"] = {"modelWordsComparedToNative": [0, 1, 2, 3],
            "additionalModelOnlyWords": 1, "modelOnlyPurpose": "unrelated allocation remains 99"}
        bindings = "import " + MODULE + "\nopen Compiler.Extraction.InsertionSort.HeapTests Compiler.ZigAir.Memory.WordArray\n"
        for name, values in CASES:
            words = ", ".join(f".ok (number {n})" for n in [0xDEADBEEF, *sorted(values), 0xBAADF00D, 99])
            bindings += f"example : sortObservation {values} = (.ok (), [{words}]) := {name}\n"
        report["nativeHeapSortBinding"] = mutation_check(output, "native-heap-sort-binding", bindings, True, env, tools["lean"]["path"])
        report["nativeHeapSortObservationProjection"] = {"nativeWords": "all input words plus both sentinels",
            "additionalModelOnlyWords": 1, "modelOnlyPurpose": "unrelated allocation remains 99"}
        report["controls"] = controls(output, env, tools["lean"]["path"], generated)
        report["memoryControls"] = memory_controls(output, env, tools["lean"]["path"])
        report["heapControls"] = heap_controls(output, env, tools["lean"]["path"])
        report["modes"] = native(output, zig, tree, env)
        proof, artifacts = prove.check_module(MODULE, CLAIMS,
            lean_bin=args.lean_bin, jobs=4, fresh=True)
        proof_dir = output / "proof"
        proof_dir.mkdir()
        for name, data in artifacts.items():
            (proof_dir / name).write_bytes(data)
        write_json(proof_dir / "report.json", proof)
        report["proofReportSha256"] = digest(proof_dir / "report.json")
        if (proof.get("status") != "passed" or proof.get("freshKernelReplay") is not True or
                proof.get("replayIncludesImports") is not True or proof.get("auditedDeclarations") != CLAIMS):
            raise ValueError("sort theorem audit or fresh kernel replay failed")
        if (inputs() != report["pythonInputs"] or lean_check.source_inputs() != report["leanInputs"] or
                source_identity(tree / "lib") != report["zigLibrary"] or digest(zig) != report["zig"]["sha256"]):
            raise ValueError("verification inputs changed during acceptance")
        check_checkout(output, tree, "zig-after")
        report.update(status="passed", universalPermutationVerified=True, modelTerminationVerified=True,
                      preparationResourceEffectsVerified=True,
                      recursiveCompositionVerified=True, typedExchangeRefinementVerified=True,
                      modelArrayAccessVerified=True, completeHeapSortRefinementVerified=True, auditedDeclarations=len(CLAIMS))
    finally:
        write_json(output / "report.json", report)
    print("Insertion-sort acceptance passed; restricted source model, not whole-compiler verification.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--zig-tree", type=Path, required=True)
    parser.add_argument("--zig", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    check(parser.parse_args())
