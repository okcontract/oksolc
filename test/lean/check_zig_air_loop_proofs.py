#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Bind decoded loop observations to fresh captures and kernel-checked proofs.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""

import argparse
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "lean"))
sys.path.insert(0, str(ROOT / "lean/zig_air"))
import environment as lean_check
import prove
import check_zig_air_loops
from build_toolchain import digest, run, source_identity, write_json
from capture import read_json
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import inputs, mutation_check
from generate_memory import generate

NATIVE_THEOREMS = {case: "Compiler.ZigAir.MemoryLoopTests." + theorem for case, theorem in (
    ("fill-0", "fill_zero"), ("fill-1", "fill_one"), ("fill-5", "fill_all"),
    ("copy-zero", "copy_zero"), ("copy-same", "copy_same"),
    ("copy-forward-overlap", "copy_forward_overlap"), ("copy-backward-overlap", "copy_backward_overlap"),
    ("nested-no-rows", "nested_no_rows"), ("nested-no-columns", "nested_no_columns"),
    ("nested-immediate", "nested_immediate"), ("nested-continue", "nested_continue"), ("nested-full", "nested_full"))}

CLAIMS = list(NATIVE_THEOREMS.values()) + ["Compiler.ZigAir.MemoryLoopTests." + name for name in (
    "fill_fault_keeps_prefix", "indexed_pointer_requires_complete_element", "indexed_pointer_preserves_readonly",
    "fill_zero_does_not_dereference", "fill_dead_pointer_fault_cleans_stack", "fill_suspends_with_stack", "fill_resumes")]
CLAIMS += ["Compiler.ZigAir.Memory.elementPointer_address", "Compiler.ZigAir.MemoryAir.Program.runFuel_preserves_valid"]
CLAIMS += ["Compiler.ZigAir.Control.Code.finite_" + name for name in ("enableLoops", "sound")]
CLAIMS += ["Compiler.ZigAir.MemoryFill." + name for name in (
    "generated_loop_body", "generated_head", "head_continue", "step_reads", "loop_effects", "entry_shape",
    "initialized_fill_steps", "initialized_fill_terminates", "initialized_fill_result")]
CLAIMS += ["Compiler.ZigAir.Memory." + name for name in (
    "allocate_shape", "allocate_pointer", "load_after_allocate", "store_keeps_counters", "pointerCast_readonly_of_load")]
CLAIMS += ["Compiler.ZigAir.Control.Machine.Steps." + name for name in ("bind_ok", "bind_fault")]
CLAIMS += ["Compiler.ZigAir.MemoryFill." + name for name in (
    "generated_prologue", "fill_body_steps", "fill_accepts", "fill_terminates", "fill_result", "specification_cleanup",
    "fill_nonempty_witness", "fill_first_allocation_oom", "fill_second_allocation_oom")]

FILL_SCOPE = {
    "root": "zig_air_loops.fill", "phase": "initialized-loop", "length": "arbitrary-u64",
    "specification": "ordered checked buffer writes and scratch-counter updates, including fault prefixes",
    "assumptions": ["typed u32 value", "initialized counter and saved-buffer slots",
                    "pairwise distinct buffer and scratch allocation identities"],
    "excluded": ["allocation prologue", "invocation cleanup", "Zig source validity", "AIR decoder", "native backend"],
}

FILL_INVOCATION_SCOPE = {
    "root": "zig_air_loops.fill", "phase": "whole-invocation", "length": "arbitrary-u64",
    "specification": "checked allocation and initialization, ordered fill effects, and cleanup at the entry mark",
    "assumptions": ["valid initial modeled heap", "typed u32 value", "buffer lifetime predates the invocation"],
    "includedFailures": ["allocation exhaustion", "checked memory faults with exact partial effects"],
    "excluded": ["Zig source validity", "AIR decoder", "native allocator and backend", "production compiler routines"],
}


def controls(output, env, lean, generated):
    tests = without_imports((ROOT / "lean/Compiler/ZigAir/MemoryLoopTests.lean").read_text())
    original = "import Compiler.ZigAir.MemoryExecutionProofs\n" + without_imports(generated) + tests
    results = [mutation_check(output, "loops-unchanged", original, True, env, lean)]
    for name, before, after in (
        ("fill-loses-index", "(.elementPointer (.local 17) (.local 16))",
         "(.elementPointer (.local 17) (.constant (.scalar (.int false 64 (0)))))"),
        ("fill-loses-value", "(.store (.local 18) (.local 2))",
         "(.store (.local 18) (.constant (.scalar (.int false 32 (0)))))"),
        ("copy-loses-source-index", "(.elementPointer (.local 23) (.local 22))",
         "(.elementPointer (.local 23) (.constant (.scalar (.int false 64 (0)))))"),
        ("nested-repeat-wrong-loop", "(.repeat rfl 22)", "(.repeat rfl 13)"),
        ("fill-reverses-condition", "(.comparison .lt (.local 12) (.local 13))",
         "(.comparison .gt (.local 12) (.local 13))")):
        if generated.count(before) != 1 or original.count(before) != 1:
            raise ValueError("loop mutation is not bound to generated AIR: " + name)
        results.append(mutation_check(output, name, original.replace(before, after), False, env, lean))
    return results


def functional_controls(output, env, lean, generated):
    """Check source binding and the effects specification against universal proofs."""
    prefix = "".join("import Compiler.ZigAir." + name + "\n" for name in (
        "ControlProjection", "MemoryPointers", "MemoryAirLaws", "MachineRefinement",
        "MemoryAllocationLaws", "MemoryExecutionProofs"))
    clients = "".join(without_imports((ROOT / "lean/Compiler/ZigAir" / name).read_text())
                      for name in ("MemoryFill.lean", "MemoryFillLoop.lean", "MemoryFillPrologue.lean",
                                   "MemoryFillInvocation.lean", "MemoryFillInvocationTests.lean"))
    original = prefix + without_imports(generated) + clients
    results = [mutation_check(output, "fill-functional-unchanged", original, True, env, lean)]
    for name, before, after in (
        ("fill-functional-wrong-value", "(.store (.local 18) (.local 2))",
         "(.store (.local 18) (.constant (.scalar (.int false 32 (0)))))"),
        ("fill-functional-wrong-backedge", "(.repeat rfl 9)", "(.repeat rfl 8)"),
        ("fill-functional-reversed-condition", "(.comparison .lt (.local 12) (.local 13))",
         "(.comparison .gt (.local 12) (.local 13))"),
        ("fill-prologue-nonzero-counter", "(.store (.local 6) (.constant (.scalar (.int false 64 (0)))))",
         "(.store (.local 6) (.constant (.scalar (.int false 64 (1)))))"),
        ("fill-prologue-loses-buffer", "(.store (.local 3) (.local 0))\n  (.bind 5",
         "(.store (.local 3) (.local 2))\n  (.bind 5")):
        # The same setup sequence can occur in other captured functions.
        fill, rest = generated.split("def fn_copy_forward", 1)
        if fill.count(before) != 1:
            raise ValueError("functional mutation is not bound to generated AIR: " + name)
        mutant = prefix + without_imports(fill.replace(before, after) + "def fn_copy_forward" + rest) + clients
        results.append(mutation_check(output, name, mutant, False, env, lean))
    before = "(.ret (.constant (.scalar .unit)))"
    fill, rest = generated.split("def fn_copy_forward", 1)
    if fill.count(before) != 1:
        raise ValueError("fill continuation mutation is ambiguous")
    mutant = prefix + without_imports(fill.replace(before, "(.ret (.local 2))") + "def fn_copy_forward" + rest) + clients
    results.append(mutation_check(output, "fill-functional-wrong-continuation", mutant, False, env, lean))
    before = "elementResult state indexSlot index value (elementPointer state (buffer address) index)"
    after = "elementResult state indexSlot index value (elementPointer state (buffer address) (index + 1))"
    if clients.count(before) != 1:
        raise ValueError("fill effects specification mutation is ambiguous")
    mutant = prefix + without_imports(generated) + clients.replace(before, after)
    results.append(mutation_check(output, "fill-specification-off-by-one", mutant, False, env, lean))
    for name, before, after in (
        ("fill-specification-wrong-cleanup-mark", "Program.finish (.scalar .unit) state.nextId (preparedOutcome",
         "Program.finish (.scalar .unit) (state.nextId + 2) (preparedOutcome"),
        ("fill-specification-oom-rewinds-lifetime",
         "def indexAllocated (pointerSlot : Address) (state : State) : Except Fault (Value × State) → Preparation\n"
         "  | .error fault => .fault fault state",
         "def indexAllocated (pointerSlot : Address) (state : State) : Except Fault (Value × State) → Preparation\n"
         "  | .error fault => .fault fault { state with nextId := state.nextId - 1 }")):
        if clients.count(before) != 1:
            raise ValueError("fill invocation specification mutation is ambiguous: " + name)
        mutant = prefix + without_imports(generated) + clients.replace(before, after)
        results.append(mutation_check(output, name, mutant, False, env, lean))
    return results


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.air-loop-proof-acceptance.v1", "status": "failed", "proofScope": "zigFreshAir",
              "decodedModes": ["ReleaseFast"], "sourceSafetyVerified": False, "decoderVerified": False,
              "universalLoopFunctionalityVerified": False, "universalInitializedFillVerified": False,
              "universalFillInvocationVerified": False, "fillInvocationScope": FILL_INVOCATION_SCOPE,
              "initializedFillScope": FILL_SCOPE, "nativeBackendVerified": False,
              "wholeCompilerVerified": False, "jobs": 4}
    try:
        report["pythonInputs"], report["leanInputs"] = inputs(), lean_check.source_inputs()
        report["toolchainReportSha256"] = digest(args.toolchain)
        run(output, "python-tests", [sys.executable, "-m", "unittest", "discover", "-s", "test/lean", "-p", "test_zig_air_*.py"], cwd=ROOT)
        captures = output / "captures"
        check_zig_air_loops.check(argparse.Namespace(toolchain=args.toolchain, output=captures))
        report["captureReportSha256"] = digest(captures / "report.json")
        target = output / "GeneratedMemoryLoops.lean"
        report["generation"] = generate(captures / "ReleaseFast/report.json", check_zig_air_loops.ROOTS,
                                         target, output / "generation.json", loops=True)
        if target.read_bytes() != (ROOT / "lean/Compiler/ZigAir/GeneratedMemoryLoops.lean").read_bytes():
            raise ValueError("generated loop programs changed")
        env, _, tools = lean_check.toolchain(args.lean_bin, 4)
        run(output, "cached-build", [tools["lake"]["path"], "build", "Compiler.ZigAir.MemoryLoopAudit"], cwd=ROOT / "lean", env=env)
        run(output, "closure-audit", [tools["lean"]["path"], "-DwarningAsError=true", "Compiler/ZigAir/MemoryLoopAudit.lean"],
            cwd=ROOT / "lean", env=env)
        audit = read_json(output / "closure-audit.stdout")
        if (audit.get("schema") != "oksolc.air-loop-audit.v1" or audit.get("scope") != "zigFreshAir" or
                [claim["theorem"] for claim in audit["claims"]] != CLAIMS):
            raise ValueError("unexpected loop declaration audit")
        negatives = output / "mutation-controls"
        negatives.mkdir()
        report["mutationControls"] = controls(negatives, env, tools["lean"]["path"], target.read_text())
        report["functionalMutationControls"] = functional_controls(negatives, env, tools["lean"]["path"], target.read_text())
        report["nativeObservations"] = {}
        for mode in ("ReleaseFast", "ReleaseSafe", "Debug"):
            path = captures / mode / "native-observations.json"
            observations = read_json(path)
            cases = observations["cases"]
            if (observations["schema"] != "oksolc.native-loop-cases.v1" or
                    {case["case"] for case in cases} != set(NATIVE_THEOREMS) or len(cases) != len(NATIVE_THEOREMS) or
                    any(case["actual"] != case["expected"] for case in cases)):
                raise ValueError("native observations lack matching model cases: " + mode)
            report["nativeObservations"][mode] = {"sha256": digest(path), "modelTheorems": NATIVE_THEOREMS}
        proof, artifacts = prove.check_module("Compiler.ZigAir.MemoryLoopAudit", CLAIMS, lean_bin=args.lean_bin, jobs=4, fresh=True)
        proofs = output / "proofs"
        proofs.mkdir()
        for name, data in artifacts.items():
            (proofs / name).write_bytes(data)
        report["proofReportSha256"] = digest(proofs / "report.json")
        if (proof["status"] != "passed" or not proof["freshKernelReplay"] or not proof["replayIncludesImports"] or
                proof["auditedDeclarations"] != CLAIMS):
            raise ValueError("loop proof audit or fresh kernel replay failed")
        if report["pythonInputs"] != inputs() or report["leanInputs"] != lean_check.source_inputs():
            raise ValueError("loop acceptance inputs changed")
        if digest(args.toolchain) != report["toolchainReportSha256"] or digest(captures / "report.json") != report["captureReportSha256"]:
            raise ValueError("loop capture/toolchain report changed")
        toolchain = read_json(args.toolchain)
        if (digest(Path(toolchain["compiler"]["path"])) != toolchain["compiler"]["sha256"] or
                source_identity(Path(toolchain["compiler"]["zigLibDir"]).parent) != toolchain["sourceTree"]):
            raise ValueError("loop toolchain changed")
        report.update(status="passed", auditedDeclarations=CLAIMS, freshKernelReplay=True,
                      universalInitializedFillVerified=True, universalFillInvocationVerified=True)
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
