#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Audit production exp256 AIR, including its complete checked invocation.
// Copyright (C) 2026 OKcontract Pte. Ltd.

Zig source validity, AIR decoding and native refinement remain open.
"""

import argparse
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "lean"))
sys.path.insert(0, str(ROOT / "lean/zig_air"))
import environment as lean_check
import prove
import check_zig_air_exp
from build_toolchain import digest, run, source_identity, write_json
from capture import read_json
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import inputs, mutation_check
from generate_memory import generate

BIT_LAWS = ["unsigned_nat_valid", "bitAnd_eval", "bitAnd_valid", "shiftRight_eval", "shiftRight_valid",
            "bitAnd_one", "shiftRight_one", "shiftRight_one_decreases", "exponent_decomposition"]
BIT_TESTS = ["unsigned_high_bit", "shift_high_bit", "shift_zero", "shift_single_bit", "shift_count_width_rejects",
             "shift_zero_width_rejects", "shift_past_width_is_illegal", "invalid_count_rejects", "signed_count_rejects",
             "signed_left_rejects", "and_mismatched_width_rejects", "and_signed_rejects", "invalid_left_rejects",
             "dead_shift_still_faults"]
# This explicit subset binds the eight closed model results to native cases.
# The six additional native observations remain regression evidence only.
MODEL_CASES = [(0, 0, 1, "zero_zero"), (0, 1, 0, "zero_one"), (2, 10, 1024, "power_ten"),
               (2, 255, 2**255, "highest_bit"), (2, 256, 0, "wrapping_power"),
               (2**255, 1, 2**255, "wide_identity"), (2**255, 2, 0, "wide_square"),
               (2**128+1, 2, 2**129+1, "mixed_square")]
EXP_TESTS = [c[3] for c in MODEL_CASES] + ["first_allocation_oom", "second_allocation_oom", "third_allocation_oom",
                                         "invalid_argument_no_allocation", "heap_valid"]
CLAIMS = (["Compiler.ZigAir.Scalar." + n for n in BIT_LAWS] +
          ["Compiler.ZigAir.Scalar.BitwiseTests." + n for n in BIT_TESTS] +
          ["Compiler.ZigAir.ExpTests." + n for n in EXP_TESTS])
LOOP_LAWS = ["number_valid", "number_typed", "multiply_eval", "parity_eval", "halve_eval", "nonzero_eval",
             "halve_decreases", "power_step", "step_select", "select_reads", "step_reads", "generated_head",
             "head_shape", "head_continue", "head_stop", "generated_loop_body", "effects_result", "loop_effects",
             "entry_shape", "initialized_steps", "initialized_terminates", "initialized_result",
             "initialized_return", "initialized_power"]
LOOP_TESTS = ["nonempty_witness", "result_write_fault", "base_write_fault_keeps_result",
              "exponent_write_fault_keeps_result_and_base", "zero_exponent_needs_no_writes", "aliased_slots_change_exponent"]
CLAIMS += ["Compiler.ZigAir.MemoryExp." + n for n in LOOP_LAWS]
CLAIMS += ["Compiler.ZigAir.MemoryExp.Tests." + n for n in LOOP_TESTS]

INVOCATION_LAWS = ["generated_prologue", "result_store_steps", "result_allocate_steps", "exponent_store_steps",
                   "exponent_allocate_steps", "base_store_steps", "base_allocate_steps", "exp_body_steps",
                   "exp_accepts", "exp_terminates", "exp_result", "prepared_finish_power", "exp_power",
                   "specification_cleanup", "exp_rejected"]
INVOCATION_TESTS = ["nonempty_witness", "full_width_witness", "zero_exponent_still_allocates",
                    "first_allocation_oom", "second_allocation_oom", "third_allocation_oom", "invalid_heap_rejected"]
CLAIMS += ["Compiler.ZigAir.MemoryExp." + n for n in INVOCATION_LAWS]
CLAIMS += ["Compiler.ZigAir.MemoryExp.InvocationTests." + n for n in INVOCATION_TESTS]

MEMORY_LAWS = [
    "valid_lookup", "store_of_access", "Heap.older_replace", "Heap.StackSince.replace", "cleanup_eq_older",
    "valid_initial_frame", "allocate_frame", "store_frame"]
SAFETY_LAWS = [
    "writable_fresh", "writable_allocate", "writable_store", "write_total", "allocate_fault", "Progress.refl",
    "Progress.trans", "store_progress", "Capabilities.store", "halve_total", "square_total", "step_total",
    "effects_total", "writable_older", "initialize_safe", "prepare_safe",
    "Progress.cleanup_heap", "prepared_safe_result", "specification_safe", "exp_safe_terminates",
    "exp_safe_result", "exp_fault_is_oom", "exp_preserves_caller_heap"]
SAFETY_TESTS = [
    "invalid_alignment_needs_heap_invariant", "readonly_is_not_writable", "nonzero_offset_is_not_writable",
    "cleanup_revokes_scratch", "older_write_changes_caller", "new_nonstack_survives_cleanup"]
CLAIMS += ["Compiler.ZigAir.Memory." + n for n in MEMORY_LAWS]
CLAIMS += ["Compiler.ZigAir.MemoryExp." + n for n in SAFETY_LAWS]
CLAIMS += ["Compiler.ZigAir.MemoryExp.SafetyTests." + n for n in SAFETY_TESTS]

INITIALIZED_SCOPE = {
    "root": "numeric.exp256", "phase": "initialized-loop-through-return",
    "inputs": "arbitrary 256-bit base, exponent and accumulator",
    "assumptions": ["initialized readable scratch words", "pairwise distinct scratch allocation identities",
                    "matching scratch pointers in the captured SSA environment"],
    "claims": ["sufficient fuel exists", "all terminal observations equal ordered checked effects",
               "ordinary result equals accumulator times modular power", "write faults retain preceding effects"],
    "excluded": ["argument/allocation prologue", "invocation cleanup", "Zig source validity", "AIR decoder",
                 "native allocator and backend", "whole compiler"],
}


INVOCATION_SCOPE = {
    "root": "numeric.exp256", "phase": "complete-checked-AIR-invocation",
    "inputs": "arbitrary 256-bit base and exponent, arbitrary valid incoming heap",
    "assumptions": ["incoming heap satisfies Memory.State.valid"],
    "claims": ["sufficient fuel exists", "all terminal observations equal ordered checked effects",
               "successful result equals mathematical modular power", "cleanup uses original allocation mark",
               "rejected inputs leave state unchanged"],
    "excluded": ["universal exclusion of memory-validity faults", "Zig source validity", "AIR decoder",
                 "native allocator and backend", "whole compiler"],
}


MEMORY_SCOPE = {
    "root": "numeric.exp256", "phase": "complete-checked-AIR-invocation-memory-safety",
    "inputs": "arbitrary 256-bit base and exponent, arbitrary valid incoming heap",
    "assumptions": ["incoming heap satisfies Memory.State.valid"],
    "claims": ["sufficient fuel exists", "result is modular power or modeled OOM",
               "every completed invocation preserves the entire incoming heap",
               "completed heap remains valid", "scratch capabilities derived from fresh allocations"],
    "excluded": ["Zig source validity", "AIR decoder", "native allocator and backend", "whole compiler"],
}


def controls(output, env, lean, generated):
    tests = without_imports((ROOT / "lean/Compiler/ZigAir/ExpTests.lean").read_text())
    original = "import Compiler.ZigAir.MemoryExecutionProofs\n" + without_imports(generated) + tests
    result = [mutation_check(output, "exp-unchanged", original, True, env, lean)]
    for name, before, after in (
        ("exp-wrong-shift", "(.shiftRight (.local 32) (.constant (.int false 8 (1))))",
         "(.shiftRight (.local 32) (.constant (.int false 8 (2))))"),
        ("exp-wrong-parity", "(.bitAnd (.local 17) (.constant (.int false 256 (1))))",
         "(.bitAnd (.local 17) (.constant (.int false 256 (2))))"),
        ("exp-wrong-initial-result", "(.store (.local 8) (.constant (.scalar (.int false 256 (1)))))",
         "(.store (.local 8) (.constant (.scalar (.int false 256 (0)))))"),
        ("exp-nonwrapping-square", "(.arithmetic .mul .wrapping (.local 27) (.local 28))",
         "(.arithmetic .mul .unchecked (.local 27) (.local 28))"),
        ("exp-wrong-return-slot", "(.load (.local 8))\n  (.ret (.local 39))",
         "(.load (.local 2))\n  (.ret (.local 39))")):
        if original.count(before) != 1:
            raise ValueError("exp mutation is not bound to the generated program: " + name)
        result.append(mutation_check(output, name, original.replace(before, after), False, env, lean))
    base = ROOT / "lean/Compiler/ZigAir"
    scalar = "import Compiler.ZigAir.Control\nimport Init.Data.Nat.Bitwise.Lemmas\n" + "".join(
        without_imports((base / file).read_text()) for file in ("Scalar.lean", "BitwiseProofs.lean", "BitwiseTests.lean"))
    result.append(mutation_check(output, "bits-unchanged", scalar, True, env, lean))
    for name, before, after in (
        ("bits-and-becomes-or", "x.toNat &&& y.toNat", "x.toNat ||| y.toNat"),
        ("bits-shift-becomes-left", "x.toNat >>> y.toNat", "x.toNat <<< y.toNat"),
        ("bits-wide-count-silently-zero", "else .error .illegalBehavior", "else .ok (.int false n 0)")):
        if scalar.count(before) != 1:
            raise ValueError("bit mutation is not unique: " + name)
        result.append(mutation_check(output, name, scalar.replace(before, after), False, env, lean))
    return result


def proof_clients(generated, additional=()):
    prefix = "".join("import " + name + "\n" for name in (
        "Compiler.ZigAir.BitwiseProofs", "Compiler.ZigAir.MemoryExecutionProofs",
        "Compiler.ZigAir.ControlProjection", "Compiler.ZigAir.MemoryAirLaws",
        "Compiler.ZigAir.MemoryEffects", "Compiler.ZigAir.MemoryAllocationLaws",
        "Compiler.ZigAir.MachineRefinement", "Contract.Interaction.WordPower"))
    clients = "".join(without_imports((ROOT / "lean/Compiler/ZigAir" / name).read_text()) for name in (
        "MemoryExpWords.lean", "MemoryExpStep.lean", "MemoryExpHead.lean", "MemoryExpLoop.lean", "MemoryExpLoopTests.lean") + additional)
    return prefix + without_imports(generated) + clients


def loop_controls(output, env, lean, generated):
    original = proof_clients(generated)
    result = [mutation_check(output, "initialized-exp-unchanged", original, True, env, lean)]
    for name, before, after in (
        ("initialized-exp-wrong-backedge", "  (.repeat rfl 11)))\n", "  (.repeat rfl 10)))\n"),
        ("initialized-exp-wrong-return", "(.load (.local 8))\n  (.ret (.local 39))",
         "(.load (.local 2))\n  (.ret (.local 39))"),
        ("initialized-exp-wrong-source-condition", "(.comparison .ne (.local 13) (.constant (.int false 256 (0))))",
         "(.comparison .eq (.local 13) (.constant (.int false 256 (0))))"),
        ("initialized-exp-wrong-entry", "(GeneratedMemory.fn_exp256.body.block? 10)", "(GeneratedMemory.fn_exp256.body.block? 12)"),
        ("initialized-exp-loses-fault-prefix", "| .error fault => (.error fault, state)\n  | .ok after => halve after exponentSlot exponent",
         "| .error fault => (.error fault, {})\n  | .ok after => halve after exponentSlot exponent")):
        if original.count(before) != 1:
            raise ValueError("initialized exponentiation mutation is not unique: " + name)
        result.append(mutation_check(output, name, original.replace(before, after), False, env, lean))
    # Isolate the effect definitions for these two controls. Substituting a
    # different wide-word expression throughout the symbolic clients can hit
    # Lean's defeq recursion bound; that is not a semantic rejection witness.
    # The complete unmodified clients above still elaborate and are audited.
    definitions = without_imports((ROOT / "lean/Compiler/ZigAir/MemoryExpStep.lean").read_text()).split("theorem step_select", 1)[0]
    witnesses = """
private def diagnosticState (b e r : Word) : State :=
  ⟨[(0, ⟨16, wordType, [(0, number b)], true, true⟩),
    (1, ⟨48, wordType, [(0, number e)], true, true⟩),
    (2, ⟨80, wordType, [(0, number r)], true, true⟩)], 3, 112⟩
example : halve (diagnosticState 2 3 1) ⟨1, 0⟩ 3 = (.ok (), diagnosticState 2 1 1) := by rfl'
example : square (diagnosticState 3 4 1) ⟨0, 0⟩ ⟨1, 0⟩ 3 4 = (.ok (), diagnosticState 9 2 1) := by rfl'
end Compiler.ZigAir.MemoryExp
"""
    specification = "import Compiler.ZigAir.MemoryExpWords\n" + definitions + witnesses
    scoped = [mutation_check(output, "exp-effect-specification-unchanged", specification, True, env, lean)]
    for name, before, after in (
        ("initialized-exp-wrong-square-spec", "afterSquare state exponentSlot exponent (store state (slot baseSlot) (number (base * base)))",
         "afterSquare state exponentSlot exponent (store state (slot baseSlot) (number (base + base)))"),
        ("initialized-exp-wrong-half-spec", "finishWrite state (store state (slot exponentSlot) (number (exponent >>> 1)))",
         "finishWrite state (store state (slot exponentSlot) (number (exponent >>> 2)))")):
        if specification.count(before) != 1:
            raise ValueError("effect-specification mutation is not unique: " + name)
        scoped.append(mutation_check(output, name, specification.replace(before, after), False, env, lean))
    for control in result:
        control["scope"] = "complete-initialized-loop-proof-clients"
    for control in scoped:
        control["scope"] = "ordered-effect-specification-witnesses"
    result.extend(scoped)
    arithmetic = ("import Compiler.ZigAir.BitwiseProofs\nimport Compiler.ZigAir.MemoryAirLaws\n"
                  "import Contract.Interaction.WordPower\n" +
                  without_imports((ROOT / "lean/Compiler/ZigAir/MemoryExpWords.lean").read_text()))
    before = "if exponent &&& 1 ≠ 0 then result * base else result"
    after = "if exponent &&& 1 ≠ 0 then result else result * base"
    if arithmetic.count(before) != 1:
        raise ValueError("word recurrence mutation is not unique")
    for name, source, expected in (("exp-word-recurrence-unchanged", arithmetic, True),
                                   ("initialized-exp-wrong-result-invariant", arithmetic.replace(before, after), False)):
        control = mutation_check(output, name, source, expected, env, lean)
        control["scope"] = "universal-word-operation-and-recurrence-proofs"
        result.append(control)
    return result


def invocation_controls(output, env, lean, generated):
    original = proof_clients(generated, ("MemoryExpPrologue.lean", "MemoryExpInvocation.lean", "MemoryExpInvocationTests.lean"))
    result = [mutation_check(output, "exp-invocation-unchanged", original, True, env, lean)]
    for name, before, after in (
        ("exp-invocation-wrong-base-argument", "(.bind 3 (.scalar .unit)\n  (.store (.local 2) (.local 0))",
         "(.bind 3 (.scalar .unit)\n  (.store (.local 2) (.local 1))"),
        ("exp-invocation-wrong-exponent-argument", "(.bind 6 (.scalar .unit)\n  (.store (.local 5) (.local 1))",
         "(.bind 6 (.scalar .unit)\n  (.store (.local 5) (.local 0))"),
        ("exp-invocation-wrong-cleanup-mark", "Program.finish wordType state.nextId", "Program.finish wordType (state.nextId + 1)"),
        ("exp-invocation-loses-allocation-fault-prefix", "| .error reason => .fault reason state\n  | .ok (pointer, after) => resultStored",
         "| .error reason => .fault reason {}\n  | .ok (pointer, after) => resultStored")):
        if original.count(before) != 1:
            raise ValueError("invocation mutation is not unique: " + name)
        result.append(mutation_check(output, name, original.replace(before, after), False, env, lean))
    for control in result:
        control["scope"] = "complete-invocation-proof-clients"
    return result


def safety_controls(output, env, lean, generated):
    original = proof_clients(generated, (
        "MemoryExpPrologue.lean", "MemoryExpInvocation.lean", "MemoryExpInvocationTests.lean",
        "MemoryHeapFrame.lean", "MemoryExpScratch.lean", "MemoryExpSafety.lean",
        "MemoryExpPreparationSafety.lean", "MemoryExpInvocationSafety.lean", "MemoryExpSafetyTests.lean"))
    result = [mutation_check(output, "exp-memory-safety-unchanged", original, True, env, lean)]
    for name, before, after in (
        ("exp-scratch-wrong-permission", "cell.type = wordType ∧ cell.writable = true", "cell.type = wordType ∧ cell.writable = false"),
        ("exp-frame-includes-fresh-id", "heap.filter (fun entry => entry.1 < mark)", "heap.filter (fun entry => entry.1 ≤ mark)"),
        ("exp-frame-allows-older-write", "(fresh : mark ≤ id) :", "(fresh : mark ≤ id + 1) :"),
        ("exp-frame-wrong-stack-kind", "mark ≤ entry.1 → entry.2.stack = true", "mark ≤ entry.1 → entry.2.stack = false"),
        ("exp-safe-result-wrong-fault", "result.1 = .error .outOfMemory", "result.1 = .error .memoryValidity")):
        if original.count(before) != 1:
            raise ValueError("memory safety mutation is not unique: " + name)
        result.append(mutation_check(output, name, original.replace(before, after), False, env, lean))
    for control in result:
        control["scope"] = "complete-invocation-memory-safety-proof-clients"
    # Changing the view offset throughout wide-word store proofs can hit the
    # defeq recursion limit. Check this definition with direct view witnesses;
    # retain the complete unmodified clients and reject resource diagnostics.
    definitions = without_imports((ROOT / "lean/Compiler/ZigAir/MemoryExpScratch.lean").read_text()).split("theorem writable_fresh", 1)[0]
    views = "import Compiler.ZigAir.MemoryExpWords\n" + definitions + """
private def diagnosticCell : Allocation := ⟨16, wordType, [], true, true⟩
private def diagnosticState : State := ⟨[(0, diagnosticCell)], 1, 48⟩
example : Writable diagnosticState ⟨0, 0⟩ := ⟨rfl, diagnosticCell, rfl, rfl, rfl⟩
example : ¬ Writable diagnosticState ⟨0, 16⟩ := by simp [Writable]
end Compiler.ZigAir.MemoryExp
"""
    before, after = "address.offset = 0 ∧ ∃ cell", "address.offset = 16 ∧ ∃ cell"
    if views.count(before) != 1:
        raise ValueError("writable-view mutation is not unique")
    for name, source, expected in (("exp-writable-view-unchanged", views, True),
                                   ("exp-scratch-wrong-offset", views.replace(before, after), False)):
        control = mutation_check(output, name, source, expected, env, lean)
        control["scope"] = "writable-view-definition-witnesses"
        result.append(control)
    return result


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.exp-air-model-acceptance.v1", "status": "failed", "proofScope": "zigFreshAir",
              "decodedModes": ["ReleaseFast"], "jobs": 4, "sourceSafetyVerified": False, "decoderVerified": False,
              "universalExpPreservationVerified": False, "nativeBackendVerified": False, "wholeCompilerVerified": False}
    report.update(universalInitializedExpVerified=False, initializedExpScope=INITIALIZED_SCOPE,
                  universalExpInvocationVerified=False, invocationScope=INVOCATION_SCOPE,
                  universalExpMemorySafetyVerified=False, memorySafetyScope=MEMORY_SCOPE)
    try:
        report["pythonInputs"], report["leanInputs"] = inputs(), lean_check.source_inputs()
        report["toolchainReportSha256"] = digest(args.toolchain)
        run(output, "python-tests", [sys.executable, "-m", "unittest", "discover", "-s", "test/lean", "-p", "test_zig_air_*.py"], cwd=ROOT)
        captures = output / "captures"
        check_zig_air_exp.check(argparse.Namespace(toolchain=args.toolchain, output=captures))
        report["captureReportSha256"] = digest(captures / "report.json")
        target = output / "GeneratedExp.lean"
        report["generation"] = generate(captures / "ReleaseFast/report.json", check_zig_air_exp.ROOTS,
                                         target, output / "generation.json", loops=True)
        if target.read_bytes() != (ROOT / "lean/Compiler/ZigAir/GeneratedExp.lean").read_bytes():
            raise ValueError("generated production exponentiation changed")
        env, _, tools = lean_check.toolchain(args.lean_bin, 4)
        run(output, "cached-build", [tools["lake"]["path"], "build", "Compiler.ZigAir.ExpAudit"], cwd=ROOT / "lean", env=env)
        run(output, "closure-audit", [tools["lean"]["path"], "-DwarningAsError=true", "Compiler/ZigAir/ExpAudit.lean"],
            cwd=ROOT / "lean", env=env)
        audit = read_json(output / "closure-audit.stdout")
        if (audit.get("schema") != "oksolc.exp-air-audit.v1" or audit.get("scope") != "zigFreshAir" or
                [claim["theorem"] for claim in audit["claims"]] != CLAIMS):
            raise ValueError("unexpected exponentiation declaration audit")
        negatives = output / "mutation-controls"
        negatives.mkdir()
        report["mutationControls"] = controls(negatives, env, tools["lean"]["path"], target.read_text())
        report["initializedMutationControls"] = loop_controls(negatives, env, tools["lean"]["path"], target.read_text())
        report["invocationMutationControls"] = invocation_controls(negatives, env, tools["lean"]["path"], target.read_text())
        report["safetyMutationControls"] = safety_controls(negatives, env, tools["lean"]["path"], target.read_text())
        all_controls = (report["mutationControls"] + report["initializedMutationControls"] +
                        report["invocationMutationControls"] + report["safetyMutationControls"])
        for control in all_controls:
            diagnostic = (negatives / (control["name"] + ".stdout")).read_text()
            if re.search(r"maximum recursion|deep recursion|maximum number of heartbeats|unknown identifier|unexpected token|timeout",
                         diagnostic, re.IGNORECASE):
                raise ValueError("mutation contains a resource or parser failure: " + control["name"])
        report["nativeModelComparisons"] = {}
        for mode in ("ReleaseFast", "ReleaseSafe", "Debug"):
            path = captures / mode / "native-observations.json"
            cases = read_json(path)["cases"]
            observed = {(int(c["base"]), int(c["exponent"])): c for c in cases}
            compared = []
            for base, exponent, expected, theorem in MODEL_CASES:
                case = observed[(base, exponent)]
                if case["actual"] != case["expected"] or case["actual"] != str(expected):
                    raise ValueError("native/model exponentiation mismatch: " + theorem)
                compared.append({"base": str(base), "exponent": str(exponent), "result": str(expected),
                                 "theorem": "Compiler.ZigAir.ExpTests." + theorem})
            report["nativeModelComparisons"][mode] = {"sha256": digest(path), "cases": compared,
                                                     "additionalNativeOnlyCases": len(cases) - len(compared)}
        proof, artifacts = prove.check_module("Compiler.ZigAir.ExpAudit", CLAIMS, lean_bin=args.lean_bin, jobs=4, fresh=True)
        proofs = output / "proofs"
        proofs.mkdir()
        for name, data in artifacts.items():
            (proofs / name).write_bytes(data)
        report["proofReportSha256"] = digest(proofs / "report.json")
        if (proof["status"] != "passed" or not proof["freshKernelReplay"] or not proof["replayIncludesImports"] or
                proof["auditedDeclarations"] != CLAIMS):
            raise ValueError("exponentiation audit or fresh kernel replay failed")
        if report["pythonInputs"] != inputs() or report["leanInputs"] != lean_check.source_inputs():
            raise ValueError("exponentiation acceptance inputs changed")
        if digest(args.toolchain) != report["toolchainReportSha256"] or digest(captures / "report.json") != report["captureReportSha256"]:
            raise ValueError("exponentiation capture/toolchain report changed")
        toolchain = read_json(args.toolchain)
        if (digest(Path(toolchain["compiler"]["path"])) != toolchain["compiler"]["sha256"] or
                source_identity(Path(toolchain["compiler"]["zigLibDir"]).parent) != toolchain["sourceTree"]):
            raise ValueError("exponentiation toolchain changed")
        report.update(status="passed", auditedDeclarations=CLAIMS, freshKernelReplay=True,
                      unsignedBitLawsVerified=True, finiteExpModelChecksVerified=True, universalInitializedExpVerified=True,
                      universalExpInvocationVerified=True, universalExpMemorySafetyVerified=True)
    except BaseException as error:
        report["error"] = str(error) or type(error).__name__
        raise
    finally:
        write_json(output / "report.json", report)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    check(parser.parse_args())
