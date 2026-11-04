#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Capture, regenerate, audit and replay production numeric AIR proofs.
// Copyright (C) 2026 OKcontract Pte. Ltd.

This gate establishes the stated fresh-AIR fragment only. Source validity,
the trusted exporter/decoder and native backend preservation remain open.
"""

import argparse
import copy
from pathlib import Path
import subprocess
import sys
import time
from lean_control_matrix import ControlPlan

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "lean"))
sys.path.insert(0, str(ROOT / "lean/zig_air"))
import prove
import environment as lean_check
from build_toolchain import digest, run, source_identity, write_json
from capture import read_json
from generate import Decoder, captured_path, generate
import check_zig_air_numeric


CLAIMS = ["Compiler.ZigAir." + name for name in (
    "u2s_correct", "s2u_correct", "u2s_word", "s2u_word", "unsigned_roundtrip", "signed_roundtrip")]
CLAIMS += ["Compiler.ZigAir.ScalarTests." + name for name in (
    "dead_unchecked_overflow", "dead_checked_overflow", "dead_wrapping_continues",
    "unsigned_wrap", "signed_wrap", "zero_width_wrap", "checked_cast_negative",
    "unchecked_cast_negative", "signed_bitcast", "signed_truncation",
    "unselected_fault_is_not_executed", "return_skips_continuation",
    "outer_jump_propagates_and_binds", "unmatched_jump_rejects", "wrong_block_value_rejects",
    "wrong_return_type_rejects", "missing_argument_rejects", "invalid_argument_rejects",
    "wrong_argument_type_rejects", "missing_local_rejects")]
CLAIMS += ["Compiler.ZigAir.Scalar.ControlRefinement.eval_eq_embed",
           "Compiler.ZigAir.Scalar.ControlRefinement.eval_eq_reference", "Compiler.ZigAir.Control.Code.preserves"]
CLAIMS += ["Compiler.ZigAir.ControlTests." + name for name in (
    "failed_primitive_keeps_effects", "type_failure_keeps_effects", "unselected_branch_has_no_effects",
    "outer_jump_keeps_state_and_environment", "returned_state_skips_continuation", "branch_reads_effectful_binding",
    "invalid_block_result_keeps_effects", "reference_failure_keeps_prefix")]


def inputs():
    paths = list((ROOT / "lean").rglob("*.py"))
    paths += list((ROOT / "test/lean").glob("*zig_air*.py"))
    paths.append(ROOT / "test/lean/lean_control_matrix.py")
    return {str(p.relative_to(ROOT)): digest(p) for p in sorted(paths) if ".lake" not in p.parts}


def kernel_rejection(proposition):
    """A semantic negative witness without elaborator re-evaluation of a large false goal.

    The kernel first proves the complete comparison false. Only then does a
    trivial Boolean goal reject. If the mutation preserves the proposition,
    that first proof cannot succeed. Resource/syntax failures still reject the
    control through its required diagnostic validator.
    """
    return f'''
namespace Compiler.ZigAir.MutationComparison
def resultMatches : Bool := decide ({proposition})
set_option maxRecDepth 8192 in
theorem differs : resultMatches = false := by decide +kernel
example : resultMatches = true := by rw [differs]; decide
end Compiler.ZigAir.MutationComparison
'''


def mutation_check(output, name, text, expected, env, lean):
    """Retain diagnostic-only mutated programs and actual terminal statuses."""
    if isinstance(lean, ControlPlan):
        return lean.add(output, name, text, expected, env, mutation_check)
    source = output / (name + ".lean")
    source.write_text(text)
    record = {"name": name, "expectedAcceptance": expected, "sourceSha256": digest(source)}
    started = time.monotonic()
    try:
        with source.open("rb") as inp, (output / (name + ".stdout")).open("wb") as out, (output / (name + ".stderr")).open("wb") as err:
            child = subprocess.run([lean, "-DwarningAsError=true", "--stdin"], stdin=inp, stdout=out,
                                   stderr=err, cwd=ROOT / "lean", env=env, timeout=120)
        record["exitCode"] = child.returncode
        record["stdoutSha256"] = digest(output / (name + ".stdout"))
        record["stderrSha256"] = digest(output / (name + ".stderr"))
        stdout = (output / (name + ".stdout")).read_text()
        stderr = (output / (name + ".stderr")).read_text()
        if stderr or (child.returncode == 0) != expected:
            raise ValueError("unexpected mutation proof outcome: " + name)
        if not expected and (child.returncode != 1 or not any(message in stdout for message in (
                "omega could not prove", "unsolved goals", "Type mismatch", "Application type mismatch", "Tactic `rfl` failed",
                "Tactic `decide` proved that the proposition", "Tactic `decide` failed for proposition"))):
            raise ValueError("mutation did not fail with a proof obligation: " + name)
        record["status"] = "passed"
        return record
    finally:
        record["seconds"] = time.monotonic() - started
        write_json(output / (name + ".process.json"), record)


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.scalar-air-acceptance.v1", "status": "failed", "proofScope": "zigFreshAir",
              "sourceSafetyVerified": False, "nativeBackendVerified": False, "wholeCompilerVerified": False,
              "jobs": 4}
    try:
        report["pythonInputs"], report["leanInputs"] = inputs(), lean_check.source_inputs()
        run(output, "python-tests", [sys.executable, "-m", "unittest", "discover", "-s", "test/lean",
                                      "-p", "test_zig_air_*.py"], cwd=ROOT)
        capture_dir = output / "capture"
        check_zig_air_numeric.check(argparse.Namespace(toolchain=args.toolchain, output=capture_dir))
        capture_report = read_json(capture_dir / "report.json")
        report["captureReportSha256"] = digest(capture_dir / "report.json")
        for name, expected in capture_report["objects"].items():
            process = read_json(capture_dir / (name + ".process.json"))
            if process.get("status") != "completed" or process.get("exitCode") != 0:
                raise ValueError("capture process did not complete: " + name)
            if digest(capture_dir / (name + ".o")) != expected:
                raise ValueError("capture object changed: " + name)
        generated = output / "Generated.lean"
        report["generation"] = generate(capture_dir / "report.json", generated, output / "generation.json")
        if generated.read_bytes() != (ROOT / "lean/Compiler/ZigAir/Generated.lean").read_bytes():
            raise ValueError("generated production AIR changed; review and regenerate the proofs")
        env, _, tools = lean_check.toolchain(args.lean_bin, 4)
        run(output, "cached-build", [tools["lake"]["path"], "build", "Compiler.ZigAir.Audit"], cwd=ROOT / "lean", env=env)
        run(output, "closure-audit", [tools["lean"]["path"], "-DwarningAsError=true", "Compiler/ZigAir/Audit.lean"],
            cwd=ROOT / "lean", env=env)
        audit = read_json(output / "closure-audit.stdout")
        if (audit.get("schema") != "oksolc.scalar-air-audit.v1" or audit.get("scope") != "zigFreshAir" or
                [claim["theorem"] for claim in audit["claims"]] != CLAIMS):
            raise ValueError("unexpected declaration audit")
        manual = (ROOT / "lean/Compiler/ZigAir/NumericProofs.lean").read_text().replace(
            "import Compiler.ZigAir.Generated\n", "")
        original = generated.read_text()
        negatives = output / "mutation-controls"
        negatives.mkdir()
        report["mutationControls"] = [mutation_check(negatives, "unchanged", original + manual, True, env, tools["lean"]["path"])]
        # Both branches and arithmetic are decoded from the actual capture.
        mutations = (("unsigned-branch", "numeric.u2s", 2, "cmp_lt", "cmp_gte"),
                     ("unsigned-result", "numeric.u2s", 9, "add", "sub"),
                     ("signed-branch", "numeric.s2u", 2, "cmp_gte", "cmp_lt"),
                     ("signed-result", "numeric.s2u", 11, "add", "sub"))
        for name, root, index, expected, value in mutations:
            record = read_json(captured_path(capture_dir / "report.json", capture_report["functions"][root]))
            before = Decoder(record).program(record)
            selected = record["instructions"][index]
            if selected["index"] != index or selected["tag"] != expected:
                raise ValueError("scalar mutation site changed: " + name)
            changed = copy.deepcopy(record)
            changed["instructions"][index]["tag"] = value
            after = Decoder(changed).program(changed)
            if before == after or original.count(before) != 1:
                raise ValueError("semantic mutation was not bound to generated AIR")
            write_json(negatives / (name + ".air.json"), changed)
            report["mutationControls"].append(mutation_check(negatives, name, original.replace(before, after) + manual,
                                                             False, env, tools["lean"]["path"]))
        core = (ROOT / "lean/Compiler/ZigAir/Control.lean").read_text()
        core_tests = (ROOT / "lean/Compiler/ZigAir/ControlTests.lean").read_text().replace(
            "import Compiler.ZigAir.Control\n", "")
        report["mutationControls"].append(mutation_check(negatives, "control-unchanged", core + core_tests,
                                                         True, env, tools["lean"]["path"]))
        # Unit-state scalar proofs cannot detect discarded memory effects. Bind
        # these mutants to the current shared evaluator and event-trace clients.
        core_mutations = (
            ("control-fault-state", ".error error => .fault error after", ".error error => .fault error state"),
            ("control-bind-state", "next.eval sem args (env.set id value) after", "next.eval sem args (env.set id value) state"),
            ("control-jump-state", "next.eval sem args (afterEnv.set id value) after", "next.eval sem args (afterEnv.set id value) state"),
            ("control-jump-environment", "next.eval sem args (afterEnv.set id value) after", "next.eval sem args (env.set id value) after"))
        for name, before, after in core_mutations:
            if core.count(before) != 1:
                raise ValueError("control mutation is not bound to the current evaluator")
            report["mutationControls"].append(mutation_check(negatives, name, core.replace(before, after) + core_tests,
                                                             False, env, tools["lean"]["path"]))
        proof, artifacts = prove.check_module("Compiler.ZigAir.Audit", CLAIMS, lean_bin=args.lean_bin, jobs=4, fresh=True)
        proofs = output / "proofs"
        proofs.mkdir()
        for name, data in artifacts.items():
            (proofs / name).write_bytes(data)
        report["proofReportSha256"] = digest(proofs / "report.json")
        if (proof["status"] != "passed" or not proof["freshKernelReplay"] or
                not proof["replayIncludesImports"] or proof["auditedDeclarations"] != CLAIMS):
            raise ValueError("proof audit or fresh kernel replay failed")
        if report["pythonInputs"] != inputs() or report["leanInputs"] != lean_check.source_inputs():
            raise ValueError("acceptance inputs changed during run")
        if (digest(capture_dir / "report.json") != report["captureReportSha256"] or
                source_identity(ROOT / "src") != capture_report["sourceTree"] or
                digest(generated) != report["generation"]["leanSha256"]):
            raise ValueError("capture source or generated input changed during proof checking")
        report["auditedDeclarations"] = CLAIMS
        report["freshKernelReplay"] = True
        report["status"] = "passed"
    except BaseException as error:
        report["error"] = str(error) or type(error).__name__
        raise
    finally:
        write_json(output / "report.json", report)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    check(parser.parse_args())
