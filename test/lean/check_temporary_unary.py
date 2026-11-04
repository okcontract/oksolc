#!/usr/bin/env python3
"""Check unary preparation and sequential boolean constructor inputs.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

Native callbacks control errors and reached effects; their graph implementation
is a fixture. This gate leaves native correspondence and recursive induction open.
"""
import argparse
import ctypes
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "lean"))
sys.path.insert(0, str(ROOT / "lean/zig_air"))
import environment as lean_check
import constructor_inventory
import extract_temporary_unary as admission
import prove
import check_word_swap
import constructor_frame_checks
from check_temporary_arguments import python_inputs, SOURCES
from constructor_array_checks import array_inventory
from build_toolchain import digest, run, write_json
from capture import capture, read_json, source_files
from generate import captured_path
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

SOURCE = ROOT / "test/lean/constructor_unary.zig"
MODULE = "Compiler.Extraction.InternerTemporaryUnaryTests"
NS = "Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryUnary."
CLAIMS = [NS + name for name in (
    "writeOne_of_store", "prepare_of_store", "prepare_verified", "invoke_of_preparation",
    "invoke_preparation_error", "invoke_verified", "source_projection", "first_error", "first_error_result", "after_first")]
CLAIMS += [NS + "Tests." + name for name in (
    "actual_allocation", "initialized_word", "good_is_derived", "previous_storage_preserved", "no_default_second_word",
    "rejected_store_retains_uninitialized_state", "rejected_store_does_not_initialize",
    "first_ordinary_error_skips_second", "first_rejection_skips_second", "first_error_retains_growth",
    "first_rejection_retains_frame", "second_uses_returned_id_and_world", "both_calls_unwind", "lifetime_identity_advances",
    "second_error_retains_first_growth", "second_rejection_retains_second_input", "older_parent_borrow_survives",
    "stack_limit_is_rejection", "constructor_oom_unwinds", "second_allocator_oom_keeps_first_growth", "second_capacity_keeps_first_growth",
    "outside_family_is_rejected", "nonvacuous_constructor_contract")]


def audit(output, env, lean):
    result = check_word_swap.audit(output, env, lean, MODULE, CLAIMS)
    claims = {record["theorem"]: set(record["dependencies"]) for record in read_json(output / "audit.json")["claims"]}
    memory = "Compiler.ZigAir.Memory."
    normal = "Compiler.Extraction.Memory.Arguments.Normalization."
    requirements = {
        NS + "prepare_verified": {NS + "prepare_of_store", normal + "caller_array_buffer",
            normal + "OwnedCall.TemporaryMemory.stored_valid", memory + "store_preserves_valid",
            memory + "WordArray.write_total", memory + "WordArray.write_allocation_frame", memory + "allocate"},
        NS + "invoke_verified": {NS + "prepare_verified", normal + "OwnedCall.TemporaryArguments.unwind_verified",
            normal + "OwnedCall.ConstructorFrame.operation_verified"},
        NS + "source_projection": {NS + "zigUnary", "Compiler.Algebraic.zigApply", NS + "unaryBuilder"},
        NS + "first_error": {NS + "zigUnary", "Compiler.Algebraic.Effect.bind"},
        NS + "first_error_result": {NS + "first_error"},
        NS + "after_first": {NS + "zigUnary", "Compiler.Algebraic.Effect.bind"},
        NS + "Tests.good_is_derived": {NS + "prepare_verified"},
        NS + "Tests.first_ordinary_error_skips_second": {NS + "first_error_result"},
        NS + "Tests.first_rejection_skips_second": {NS + "first_error_result"},
        NS + "Tests.nonvacuous_constructor_contract": {NS + "invoke_verified"},
    }
    for name, required in requirements.items():
        if not required <= claims[name]:
            raise ValueError("unary argument proof lost dependencies: " + name + ": " + ", ".join(sorted(required - claims[name])))
    return {**result, "checkedDependencies": sorted(requirements)}


def controls(output, env, lean):
    directory = ROOT / "lean/Compiler/Extraction"
    model = without_imports((directory / "InternerTemporaryUnary.lean").read_text())
    program = without_imports(admission.OUTPUT.read_text())
    proofs = without_imports((directory / "InternerTemporaryUnaryProofs.lean").read_text())
    tests = without_imports((directory / "InternerTemporaryUnaryTests.lean").read_text())
    imports = "import Compiler.Extraction.InternerTemporaryArguments\nimport Compiler.Extraction.InternerConstructorFrameTests\nimport Compiler.Extraction.ConstructionProofs\n"
    records = [mutation_check(output, "unary-complete-unchanged", imports + model + program + proofs + tests, True, env, lean)]
    # Labeled diagnostic subset: retain executable bodies and observations,
    # while the unchanged complete universal proof and fresh replay stay required.
    observed = model[:model.index("\ntheorem writeOne_of_store")]
    observed += model[model.index("\ndef invoke"):model.index("\ntheorem invoke_of_preparation")]
    observed += "\nend Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryUnary\n"
    fixtures = tests[:tests.index("\ndef semanticCaller")]
    fixtures = re.sub(r"\ntheorem [\s\S]*?(?=\n(?:def |theorem |end ))", "", fixtures + "\nend ")[:-5]
    # Closed scalar observations keep failure diagnostics bounded; rejected
    # whole-world equality can exhaust pretty printing after a genuine mismatch.
    fixtures += """
example : Compiler.ZigAir.Memory.load prepared.memory.memory (source.pointer 0) = .ok (number 99) := by rfl'
example : (run).1 = .ok 98 := by rfl'
example : (run .iszero_left).1 = .ok 99 := by rfl'
example : (run .iszero_right).1 = .ok 98 := by rfl'
example : (run).2.graph.read 99 = some 0 := by rfl'
example : (run .bool_left (some (.language .outOfMemory))).2.graph.read 99 = some 0 := by rfl'
example : (run .bool_left (some (.language .outOfMemory))).2.memory.memory.nextId =
    (first (some (.language .outOfMemory))).2.memory.memory.nextId := by rfl'
example : (run .bool_left none (some (.language .outOfMemory))).2.graph.read 99 = some 0 := by rfl'
example : first.2.memory.memory.nextId = 7 := by rfl'
example : (run).2.memory.memory.nextId = 11 := by rfl'
example : Compiler.ZigAir.Memory.load nestedCall.2.memory.memory ((⟨3, 0, 2⟩ : View).pointer 1) = .ok (number 1) := by rfl'
"""
    fixtures += "\nend Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryUnary.Tests\n"
    diagnostics = imports + "set_option pp.maxSteps 8\nset_option pp.deepTerms false\nset_option pp.notation false\n"
    records.append(mutation_check(output, "unary-observations-unchanged", diagnostics + observed + program + fixtures, True, env, lean))
    boolean_body = program[program.index("  | .bool_left | .bool_right =>"):program.index("  | _ =>")]
    reached_bind = """  | .bool_left | .bool_right => fun before =>
    match invoke external budget allocator p q (Interner.buildOpcode .ISZERO)
      (if replacement == .bool_left then left else right) before with
"""
    for name, text, before, after in (
        ("wrong-initialized-word", "model", "(source.pointer 0) (number value)", "(source.pointer 0) (number (value + 1))"),
        ("bad-unary-offset", "model", "⟨before.memory.memory.nextId, 0, 1⟩", "⟨before.memory.memory.nextId, 1, 1⟩"),
        ("second-uses-original-id", "program", "(Interner.buildOpcode .ISZERO) first", "(Interner.buildOpcode .ISZERO) left"),
        ("second-uses-original-world", "program", boolean_body, reached_bind +
         "    | (.error fault, reached) => (.error fault, reached)\n    | (.ok first, _) => invoke external budget allocator p q (Interner.buildOpcode .ISZERO) first before\n"),
        ("discard-first-error-state", "program", boolean_body, reached_bind +
         "    | (.error fault, _) => (.error fault, before)\n    | (.ok first, middle) => invoke external budget allocator p q (Interner.buildOpcode .ISZERO) first middle\n"),
        ("continue-after-first-error", "program", boolean_body, reached_bind +
         "    | (.error fault, reached) =>\n      let (_, last) := invoke external budget allocator p q (Interner.buildOpcode .ISZERO) 99 reached\n      (.error fault, last)\n    | (.ok first, middle) => invoke external budget allocator p q (Interner.buildOpcode .ISZERO) first middle\n"),
        ("wrong-iszero-selection", "program", "if replacement == .iszero_left then left else right", "if replacement == .iszero_left then right else left"),
    ):
        target = observed if text == "model" else program
        if target.count(before) != 1:
            raise ValueError("ambiguous unary semantic control: " + name)
        changed = target.replace(before, after)
        if name == "second-uses-original-id":
            changed = changed.replace("let first ← invoke", "let _first ← invoke")
        records.append(mutation_check(output, "unary-" + name,
            diagnostics + (changed if text == "model" else observed) + (changed if text == "program" else program) + fixtures,
            False, env, lean))
    for record in records:
        text = (output / (record["name"] + ".stdout")).read_text()
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant", text, re.I):
            raise ValueError("unary control hit a resource or syntax failure: " + record["name"])
    return records


class Event(ctypes.Structure):
    _fields_ = [("opcode", ctypes.c_uint32), ("operand", ctypes.c_uint32)] + [
        (name, ctypes.c_size_t) for name in ("length", "pointer", "alignment")]


class Observation(ctypes.Structure):
    _fields_ = [(name, ctypes.c_uint32) for name in (
        "fail_at", "first_result", "second_result", "operation_calls", "graph_growth", "returned_error")]
    _fields_ += [("events", Event * 2)]


def native_cases(output, library):
    native = ctypes.CDLL(str(library))
    cases, sentinel = [], 0xA5A5A5A5
    for branch in admission.check()["admittedBranches"]:
        function = getattr(native, branch)
        function.argtypes = [ctypes.POINTER(Observation), ctypes.c_uint32, ctypes.c_uint32]
        function.restype = ctypes.c_uint32
        for first_result, second_result, left, right in ((99, 42, 1, 3), (0, 0xFFFFFFFF, 0xFFFFFFFF, 0), (0xFFFFFFFF, 0, 256, 255)):
            for fail_at in (0, 1, 2):
                observed = Observation(fail_at, first_result, second_result, 0, 0, 0,
                    (Event * 2)(*(Event(*([sentinel] * 5)) for _ in range(2))))
                returned = function(ctypes.byref(observed), left, right)
                boolean = branch.startswith("bool_")
                calls = 1 if not boolean or fail_at == 1 else 2
                failed = 0 < fail_at <= calls
                actual_events = [{name: getattr(event, name) for name, _ in Event._fields_} for event in observed.events]
                actual = {name: getattr(observed, name) for name, _ in Observation._fields_ if name != "events"}
                actual["events"] = [{**event, "pointer": "nonzero" if event["pointer"] > 0 else "zero"}
                    if index < calls else event for index, event in enumerate(actual_events)]
                actual["returned"] = returned
                expected_events = []
                for index in range(2):
                    expected_events.append({"opcode": 25 if branch == "not_right" else 21,
                        "operand": first_result if index == 1 else left if branch.endswith("left") else right,
                        "length": 1, "pointer": "nonzero", "alignment": 0} if index < calls else
                        {name: sentinel for name, _ in Event._fields_})
                expected = {"fail_at": fail_at, "first_result": first_result, "second_result": second_result,
                    "operation_calls": calls, "graph_growth": calls - int(failed), "returned_error": int(failed),
                    "events": expected_events, "returned": 0 if failed else second_result if boolean else first_result}
                cases.append({"branch": branch, "inputs": [first_result, second_result, left, right, fail_at],
                    "rawEvents": actual_events, "actual": actual, "expected": expected})
    write_json(output / "native-observations.json", {"schema": "oksolc.unary-native-controls.v1",
        "librarySha256": digest(library), "cases": cases, "nativeGraphCorrespondenceVerified": False})
    if any(case["actual"] != case["expected"] for case in cases):
        raise ValueError("native unary initializer observation mismatch")
    return {"cases": len(cases), "sha256": digest(output / "native-observations.json"), "librarySha256": digest(library)}


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.unary-temporary-arguments.v1", "status": "failed", "jobs": 4,
        "scope": "Algebraic.apply unary literals and sequential boolean constructor inputs",
        "typedTemporaryInitializationVerified": False, "preparedConstructorInputVerified": False,
        "ordinaryTemporaryCleanupVerified": False, "completeRecursiveConstructorsVerified": False,
        "nativeGraphCorrespondenceVerified": False, "recursiveChildPreservationVerified": False,
        "airControlSemanticsVerified": False, "nativeBackendVerified": False, "wholeCompilerVerified": False}
    try:
        report["pythonInputs"], report["leanInputs"] = python_inputs(), lean_check.source_inputs()
        report["admission"], report["inventory"] = admission.check(), constructor_inventory.check()
        report["constructorBinding"] = constructor_frame_checks.bindings()
        sources = source_files(SOURCE, SOURCES)
        env, _, tools = lean_check.toolchain(args.lean_bin, 4)
        report["tools"] = tools
        run(output, "python-preflight", [sys.executable, "-m", "unittest", "discover", "-s", "test/lean", "-p", "test_temporary_unary.py"], cwd=ROOT)
        run(output, "cached-proof-preflight", [tools["lake"]["path"], "build", MODULE], cwd=ROOT / "lean", env=env)
        report["audit"], report["controls"] = audit(output, env, tools["lean"]["path"]), controls(output, env, tools["lean"]["path"])
        toolchain = read_json(args.toolchain)
        compiler, lib = Path(toolchain["compiler"]["path"]), Path(toolchain["compiler"]["zigLibDir"])
        if (toolchain["compiler"]["version"] != "0.17.0" or digest(compiler) != toolchain["compiler"]["sha256"] or
                digest(lib.parent / "src/SemanticExport.zig") != digest(ROOT / "lean/zig_air/SemanticExport.zig")):
            raise ValueError("native toolchain does not use the pinned compiler and current exporter")
        report["toolchainReportSha256"], report["native"] = digest(args.toolchain), {}
        for mode in ("ReleaseFast", "Debug", "ReleaseSafe"):
            directory = output / mode
            branches = report["admission"]["admittedBranches"]
            capture(argparse.Namespace(toolchain=args.toolchain, source=SOURCE, source_file=SOURCES, output=directory,
                root=["constructor_unary." + branch for branch in branches], mode=mode))
            captured = read_json(directory / "report.json")
            command = read_json(directory / "ordinary.process.json")["command"]
            command[command.index("build-obj")] = "build-lib"
            command.append("-dynamic")
            library = directory / "unary.dylib"
            command[command.index("--cache-dir") + 1] = str(directory / "native-cache")
            command = ["-femit-bin=" + str(library) if item.startswith("-femit-bin=") else item for item in command]
            run(directory, "native-build", command)
            observed = native_cases(directory, library)
            report["native"][mode] = {**observed, "captureReportSha256": digest(directory / "report.json"),
                "objects": captured["objects"], "sourceFiles": captured["sourceFiles"],
                "arrayInventory": {name: array_inventory(captured_path(directory / "report.json", entry), 1,
                    2 if name.rsplit(".", 1)[1].startswith("bool_") else 1)
                    for name, entry in captured["functions"].items() if entry["requested"]}}
        proof, artifacts = prove.check_module(MODULE, CLAIMS, lean_bin=args.lean_bin, jobs=4, fresh=True)
        directory = output / "proof"
        directory.mkdir()
        for name, data in artifacts.items():
            (directory / name).write_bytes(data)
        write_json(directory / "report.json", proof)
        report["proofReportSha256"] = digest(directory / "report.json")
        if (proof.get("status") != "passed" or proof.get("freshKernelReplay") is not True or
                proof.get("replayIncludesImports") is not True or proof.get("auditedDeclarations") != CLAIMS):
            raise ValueError("unary proof or fresh imported-kernel replay failed")
        if (python_inputs() != report["pythonInputs"] or lean_check.source_inputs() != report["leanInputs"] or
                source_files(SOURCE, SOURCES) != sources or digest(args.toolchain) != report["toolchainReportSha256"] or
                digest(compiler) != toolchain["compiler"]["sha256"]):
            raise ValueError("unary acceptance inputs changed")
        report.update(status="passed", typedTemporaryInitializationVerified=True,
            preparedConstructorInputVerified=True, ordinaryTemporaryCleanupVerified=True)
    except BaseException as error:
        report["error"] = str(error)
        raise
    finally:
        write_json(output / "report.json", report)
    print("Unary temporary preparation and sequential boolean inputs passed; native graph correspondence and recursive induction remain open.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    check(parser.parse_args())


if __name__ == "__main__":
    main()
