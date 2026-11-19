#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Audit resumable AIR control laws; this does not certify captured loop artifacts.
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
from build_toolchain import digest, run, write_json
from capture import read_json
from check_zig_air_proofs import inputs, mutation_check


CLAIMS = ["Compiler.ZigAir.Control.Machine." + name for name in (
    "advance_finished", "advance_add", "finished_stable", "Steps.trans", "advance_steps",
    "steps_iff_fuel", "finished_unique", "jump_state", "backedge_state", "step_preserves",
    "Steps.preserves", "run_preserves", "finite_steps", "finite_run", "finite_result")]
CLAIMS += ["Compiler.ZigAir.MemoryAir." + name for name in (
    "machine_preserves_valid", "machine_steps_preserve_valid")]
CLAIMS += ["Compiler.ZigAir.MachineTests." + name for name in (
    "zero_fuel_suspends", "repeated_effects_are_retained", "backedge_keeps_frame",
    "repeat_unwinds_inner_frames", "jump_exits_loop", "loop_return_skips_frames",
    "loop_fault_keeps_effects", "missing_repeat_target_rejects", "repeat_cannot_target_block",
    "jump_cannot_target_loop", "unselected_repeat_does_not_execute",
    "repeated_binding_observes_current_state", "resumed_loop_matches_uninterrupted")]

CLAIMS += [
    "Compiler.ZigAir.MemoryAir.Invocation.resume_zero",
    "Compiler.ZigAir.MemoryAir.Invocation.resume_finished",
    "Compiler.ZigAir.MemoryAir.Invocation.resume_add",
    "Compiler.ZigAir.MemoryAir.Invocation.finished_unique",
    "Compiler.ZigAir.MemoryAir.Invocation.finish_state",
    "Compiler.ZigAir.MemoryAir.Invocation.finish_preserves_valid",
    "Compiler.ZigAir.MemoryAir.Invocation.resume_preserves_valid",
    "Compiler.ZigAir.MemoryAir.Program.enableLoops_accepts",
    "Compiler.ZigAir.MemoryAir.Program.start_state",
    "Compiler.ZigAir.MemoryAir.Program.runFuel_preserves_valid",
    "Compiler.ZigAir.MemoryAir.Program.runFuel_finite",
    "Compiler.ZigAir.MemoryAir.Program.runFuel_finite_result",
    "Compiler.ZigAir.MemoryExecutionTests.zero_budget_retains_valid_entry",
    "Compiler.ZigAir.MemoryExecutionTests.zero_budget_rejects_bad_arguments",
    "Compiler.ZigAir.MemoryExecutionTests.invalid_heap_rejects_before_execution",
    "Compiler.ZigAir.MemoryExecutionTests.suspension_keeps_stack_allocation",
    "Compiler.ZigAir.MemoryExecutionTests.return_cleans_only_current_invocation",
    "Compiler.ZigAir.MemoryExecutionTests.resumption_keeps_original_mark",
    "Compiler.ZigAir.MemoryExecutionTests.return_type_failure_cleans_stack",
    "Compiler.ZigAir.MemoryExecutionTests.escaping_jump_cleans_stack",
    "Compiler.ZigAir.MemoryExecutionTests.resumption_keeps_arguments",
    "Compiler.ZigAir.MemoryExecutionTests.fault_keeps_prior_effects_and_cleans_current_stack",
    "Compiler.ZigAir.MemoryExecutionTests.loop_suspension_keeps_stack",
    "Compiler.ZigAir.MemoryExecutionTests.loop_budget_is_not_a_fault"]


def controls(output, env, lean):
    source = ROOT / "lean/Compiler/ZigAir"
    core = (source / "Machine.lean").read_text()
    clients = "\n".join("\n".join(line for line in (source / (name + ".lean")).read_text().splitlines()
                                  if not line.startswith("import ")) for name in
                        ("MachineProofs", "MachineRefinement", "MachineTests"))
    original = "import Compiler.ZigAir.ControlTests\n" + core + clients
    results = [mutation_check(output, "machine-unchanged", original, True, env, lean)]
    for name, before, after in (
        ("fuel-is-not-fault", "| 0, execution => execution",
         "| 0, execution => .finished (.fault sem.malformed execution.state)"),
        ("finished-is-stable", "| _ + 1, .finished outcome => .finished outcome",
         "| _ + 1, .finished outcome => .finished (.fault sem.malformed outcome.state)"),
        ("failed-primitive-keeps-state", ".error reason => .finished (.fault reason after)",
         ".error reason => .finished (.fault reason state)"),
        ("backedge-keeps-loop", ".suspended ⟨body, env, state, .loop id body :: frames⟩\n    else backedge",
         ".suspended ⟨body, env, state, frames⟩\n    else backedge"),
        ("backedge-keeps-locals", ".suspended ⟨body, env, state, .loop id body :: frames⟩\n    else backedge",
         ".suspended ⟨body, (fun _ => none), state, .loop id body :: frames⟩\n    else backedge"),
        ("block-result-binds", ".suspended ⟨next, env.set id value, state, frames⟩",
         ".suspended ⟨next, env, state, frames⟩"),
        ("repeat-checks-label", "if target = id then .suspended ⟨body, env, state, .loop id body :: frames⟩",
         "if target != id then .suspended ⟨body, env, state, .loop id body :: frames⟩")):
        if core.count(before) != 1 or original.count(before) != 1:
            raise ValueError("machine mutation is not bound to the current semantics: " + name)
        results.append(mutation_check(output, name, original.replace(before, after), False, env, lean))
    return results



def invocation_controls(output, env, lean):
    source = ROOT / "lean/Compiler/ZigAir"
    core = (source / "MemoryExecution.lean").read_text()
    clients = "\n".join("\n".join(line for line in (source / (name + ".lean")).read_text().splitlines()
                                  if not line.startswith("import ")) for name in
                        ("MemoryExecutionProofs", "MemoryExecutionTests"))
    original = "import Compiler.ZigAir.MemoryMachine\nimport Compiler.ZigAir.MachineRefinement\n" + core + clients
    results = [mutation_check(output, "invocation-unchanged", original, True, env, lean)]
    for name, before, after in (
        ("invocation-no-suspension-cleanup", ".suspended returnType mark args next",
         ".suspended returnType mark args { next with state := cleanup mark next.state }"),
        ("invocation-original-mark", ".suspended returnType mark args next",
         ".suspended returnType next.state.nextId args next"),
        ("invocation-original-arguments", ".suspended returnType mark args next",
         ".suspended returnType mark [] next"),
        ("invocation-terminal-cleanup", ".finished result.1 result.2",
         ".finished result.1 outcome.state"),
        ("invocation-caller-stack", ".suspended program.returnType state.nextId args ⟨program.body, fun _ => none, state, []⟩",
         ".suspended program.returnType 0 args ⟨program.body, fun _ => none, state, []⟩"),
        ("invocation-entry-validation", "if program.accepts args state then", "if true then"),
        ("invocation-return-check", ".finished result.1 result.2",
         ".finished (.ok (.scalar .unit)) result.2")):
        if core.count(before) != 1 or original.count(before) != 1:
            raise ValueError("invocation mutation is not bound to current semantics: " + name)
        results.append(mutation_check(output, name, original.replace(before, after), False, env, lean))
    return results


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.air-machine-acceptance.v1", "status": "failed",
              "proofScope": "zigAirControlModel", "capturedLoopsVerified": False,
              "sourceSafetyVerified": False, "nativeBackendVerified": False,
              "wholeCompilerVerified": False, "jobs": 4}
    try:
        report["pythonInputs"], report["leanInputs"] = inputs(), lean_check.source_inputs()
        env, _, tools = lean_check.toolchain(args.lean_bin, 4)
        run(output, "cached-build", [tools["lake"]["path"], "build", "Compiler.ZigAir.MachineAudit"],
            cwd=ROOT / "lean", env=env)
        run(output, "closure-audit", [tools["lean"]["path"], "-DwarningAsError=true", "Compiler/ZigAir/MachineAudit.lean"],
            cwd=ROOT / "lean", env=env)
        audit = read_json(output / "closure-audit.stdout")
        if (audit.get("schema") != "oksolc.air-machine-audit.v1" or audit.get("scope") != "zigAirControlModel" or
                [claim["theorem"] for claim in audit["claims"]] != CLAIMS):
            raise ValueError("unexpected machine declaration audit")
        negatives = output / "mutation-controls"
        negatives.mkdir()
        report["mutationControls"] = controls(negatives, env, tools["lean"]["path"])
        report["mutationControls"].extend(invocation_controls(negatives, env, tools["lean"]["path"]))
        proof, artifacts = prove.check_module("Compiler.ZigAir.MachineAudit", CLAIMS,
                                              lean_bin=args.lean_bin, jobs=4, fresh=True)
        proofs = output / "proofs"
        proofs.mkdir()
        for name, data in artifacts.items():
            (proofs / name).write_bytes(data)
        report["proofReportSha256"] = digest(proofs / "report.json")
        if (proof["status"] != "passed" or not proof["freshKernelReplay"] or not proof["replayIncludesImports"] or
                proof["auditedDeclarations"] != CLAIMS):
            raise ValueError("machine proof audit or fresh kernel replay failed")
        if report["pythonInputs"] != inputs() or report["leanInputs"] != lean_check.source_inputs():
            raise ValueError("machine acceptance inputs changed")
        report.update(status="passed", auditedDeclarations=CLAIMS, freshKernelReplay=True)
    except BaseException as error:
        report["error"] = str(error) or type(error).__name__
        raise
    finally:
        write_json(output / "report.json", report)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    check(parser.parse_args())
