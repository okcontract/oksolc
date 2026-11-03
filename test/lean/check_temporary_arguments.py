#!/usr/bin/env python3
"""Check the admitted negation initializer, typed preparation and native controls.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

This gate does not close native graph correspondence or recursive induction.
AIR observations inventory array layout only; unsupported payloads stay explicit.
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
import extract_temporary_arguments as admission
import prove
import check_word_swap
import constructor_frame_checks
from constructor_array_checks import array_inventory
from build_toolchain import digest, run, write_json
from capture import capture, read_json, source_files
from generate import captured_path
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

SOURCE = ROOT / "test/lean/constructor_arguments.zig"
SOURCES = [Path(name) for name in (
    "src/libevmasm/algebraic_rules.zig", "src/libevmasm/instruction.zig",
    "src/liblangutil/debug_data.zig", "src/liblangutil/source_location.zig", "src/liblangutil/evm_version.zig")]
MODULE = "Compiler.Extraction.InternerTemporaryArgumentsTests"
NS = "Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryArguments."
CLAIMS = [NS + name for name in (
    "pair_contents", "writePair_of_stores", "prepare_of_stores", "prepare_verified",
    "unwind_keeps_reached", "unwind_verified", "prepared_operation_verified", "first_error", "after_first")]
CLAIMS += [NS + "Tests." + name for name in (
    "ordered_arguments", "good_is_derived", "previous_storage_preserved", "rejected_store_retains_prefix",
    "first_error_skips_temporary_and_outer_call", "first_rejection_keeps_reached_state",
    "success_unwinds_temporary", "nested_parent_borrow_survives", "outer_capacity_unwinds_after_child", "outer_oom_retains_child_growth",
    "rejected_outer_observation_retains_initialized_temporary", "stack_limit_keeps_child_and_rejects",
    "outside_family_is_rejected", "prepared_constructor_contract")]


def python_inputs():
    return {str(path.relative_to(ROOT)): digest(path) for directory in (ROOT / "lean", ROOT / "test/lean")
            for path in sorted(directory.rglob("*.py")) if ".lake" not in path.parts}


def audit(output, env, lean):
    result = check_word_swap.audit(output, env, lean, MODULE, CLAIMS)
    claims = {record["theorem"]: set(record["dependencies"]) for record in read_json(output / "audit.json")["claims"]}
    memory = "Compiler.ZigAir.Memory."
    normal = "Compiler.Extraction.Memory.Arguments.Normalization."
    requirements = {
        NS + "prepare_verified": {NS + "prepare_of_stores", NS + "pair_contents", normal + "caller_buffer",
            normal + "related_frame", memory + "store_preserves_valid", memory + "WordArray.write_total",
            memory + "WordArray.write_allocation_frame", memory + "allocate"},
        NS + "prepared_operation_verified": {NS + "prepare_verified", NS + "unwind_verified",
            normal + "OwnedCall.ConstructorFrame.operation_verified", normal + "OwnedCall.Good"},
        NS + "unwind_verified": {NS + "unwind", normal + "Valid.cleanup", memory + "cleanup"},
        NS + "unwind_keeps_reached": {NS + "unwind", memory + "cleanup"},
        NS + "Tests.good_is_derived": {NS + "prepare_verified"},
        NS + "Tests.success_unwinds_temporary": {NS + "zigNegation", NS + "negate", NS + "unwind"},
    }
    for name, required in requirements.items():
        if not required <= claims[name]:
            raise ValueError("temporary argument proof lost dependencies: " + name + ": " + ", ".join(sorted(required - claims[name])))
    return {**result, "checkedDependencies": sorted(requirements)}


def controls(output, env, lean):
    directory = ROOT / "lean/Compiler/Extraction"
    model = without_imports((directory / "InternerTemporaryArguments.lean").read_text())
    program = without_imports(admission.OUTPUT.read_text())
    tests = without_imports((directory / "InternerTemporaryArgumentsTests.lean").read_text())
    imports = "import Compiler.Extraction.InternerConstructorFrameTests\nimport Compiler.Extraction.InternerTemporaryMemory\n"
    records = [mutation_check(output, "temporary-complete-unchanged", imports + model + program + tests, True, env, lean)]
    # The complete proof remains mandatory above and in fresh replay. Mutated
    # executable observations isolate semantic failures from costly unfolding of
    # a changed universal theorem; this labeled subset never replaces acceptance.
    observed = model[:model.index("\nprivate theorem stored_valid")]
    observed += model[model.index("\ndef unwind"):model.index("\ntheorem unwind_keeps_reached")]
    observed += model[model.index("\ndef invoke "):model.index("\ntheorem invoke_of_preparation")]
    observed += model[model.index("\ndef negate"):model.index("\ntheorem first_error")]
    observed += "\nend Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryArguments\n"
    fixtures = tests[:tests.index("\ntheorem good_is_derived")]
    fixtures += tests[tests.index("\ntheorem previous_storage_preserved"):tests.index("\ntheorem prepared_constructor_contract")]
    fixtures += "\nend Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryArguments.Tests\n"
    records.append(mutation_check(output, "temporary-observations-unchanged", imports + observed + program + fixtures, True, env, lean))
    for name, before, after in (
        ("wrong-first-word", "(source.pointer 0) (number first)", "(source.pointer 0) (number second)"),
        ("overwrite-first-word", "(source.pointer 1) (number second)", "(source.pointer 0) (number second)"),
        ("discard-initialized-prefix", "(.error (.memory (.preparation (.memory fault))), middle)",
         "(.error (.memory (.preparation (.memory fault))), before)"),
        ("erase-parent-storage", "Compiler.ZigAir.Memory.cleanup mark", "Compiler.ZigAir.Memory.cleanup (mark - mark)"),
        ("rewind-lifetime", "memory := Compiler.ZigAir.Memory.cleanup mark ran.2.world.memory.memory",
         "memory := { Compiler.ZigAir.Memory.cleanup mark ran.2.world.memory.memory with nextId := mark }"),
        ("cleanup-rejected-observation", "if ordinary ran.1 then", "if true then"),
        ("discard-child-error-state", "match constant 0 before with\n  | (.error fault, reached) => (.error fault, reached)",
         "match constant 0 before with\n  | (.error fault, _) => (.error fault, before)"),
    ):
        if observed.count(before) != 1:
            raise ValueError("ambiguous temporary argument control: " + name)
        records.append(mutation_check(output, "temporary-" + name,
            imports + observed.replace(before, after) + program + fixtures, False, env, lean))
    for record in records:
        text = (output / (record["name"] + ".stdout")).read_text()
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant", text, re.I):
            raise ValueError("temporary control hit a resource or syntax failure: " + record["name"])
    return records


def array_shape(path):
    """Retain a bounded layout inventory, without interpreting control or calls."""
    result = array_inventory(path, 2, 1)
    arrays = result.pop("arrays")
    return {**arrays[0], **result}


class Observation(ctypes.Structure):
    _fields_ = [(name, ctypes.c_uint32) for name in (
        "fail_constant", "fail_operation", "constant_id", "result_id", "constant_calls", "operation_calls",
        "graph_growth", "returned_error", "opcode")]
    _fields_ += [("length", ctypes.c_size_t), ("alignment", ctypes.c_size_t),
                ("first", ctypes.c_uint32), ("second", ctypes.c_uint32)]


def native_cases(output, library):
    native = ctypes.CDLL(str(library))
    cases = []
    sentinel = 0xA5A5A5A5
    for side in ("left", "right"):
        function = getattr(native, "negate_" + side)
        function.argtypes = [ctypes.POINTER(Observation), ctypes.c_uint32, ctypes.c_uint32]
        function.restype = ctypes.c_uint32
        for constant, result, left, right in ((99, 42, 1, 3), (0, 0, 0xFFFFFFFF, 0), (0xFFFFFFFF, 0xFFFFFFFF, 256, 255)):
            for fail_constant, fail_operation in ((0, 0), (1, 0), (0, 1), (1, 1)):
                observed = Observation(fail_constant, fail_operation, constant, result, 0, 0, 0, 0,
                                       sentinel, sentinel, sentinel, sentinel, sentinel)
                initial = {name: getattr(observed, name) for name, _ in Observation._fields_}
                returned = function(ctypes.byref(observed), left, right)
                actual = {name: getattr(observed, name) for name, _ in Observation._fields_}
                failed = bool(fail_constant or fail_operation)
                expected = {**initial, "constant_calls": 1, "operation_calls": 0 if fail_constant else 1,
                    "graph_growth": 0 if fail_constant else 1, "returned_error": int(failed),
                    "opcode": sentinel if fail_constant else 3, "length": sentinel if fail_constant else 2,
                    "alignment": sentinel if fail_constant else 0, "first": sentinel if fail_constant else constant,
                    "second": sentinel if fail_constant else left if side == "left" else right}
                cases.append({"side": side, "inputs": [constant, result, left, right, fail_constant, fail_operation],
                    "actual": {**actual, "returned": returned}, "expected": {**expected, "returned": 0 if failed else result}})
    write_json(output / "native-observations.json", {"schema": "oksolc.negation-native-controls.v1",
        "librarySha256": digest(library), "cases": cases, "nativeGraphCorrespondenceVerified": False})
    if any(case["actual"] != case["expected"] for case in cases):
        raise ValueError("native negation initializer observation mismatch")
    return {"cases": len(cases), "sha256": digest(output / "native-observations.json"), "librarySha256": digest(library)}


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.negation-temporary-arguments.v1", "status": "failed", "jobs": 4,
        "scope": "Algebraic.apply neg_left and neg_right argument initializer and constructor input",
        "typedTemporaryInitializationVerified": False, "preparedConstructorInputVerified": False,
        "ordinaryTemporaryCleanupVerified": False, "completeRecursiveConstructorsVerified": False,
        "nativeGraphCorrespondenceVerified": False, "recursiveChildPreservationVerified": False,
        "airControlSemanticsVerified": False, "nativeBackendVerified": False, "wholeCompilerVerified": False}
    try:
        report["pythonInputs"], report["leanInputs"] = python_inputs(), lean_check.source_inputs()
        report["admission"] = admission.check()
        report["inventory"] = constructor_inventory.check()
        report["constructorBinding"] = constructor_frame_checks.bindings()
        sources = source_files(SOURCE, SOURCES)
        env, _, tools = lean_check.toolchain(args.lean_bin, 4)
        report["tools"] = tools
        run(output, "python-preflight", [sys.executable, "-m", "unittest", "discover", "-s", "test/lean", "-p", "test_temporary_arguments.py"], cwd=ROOT)
        run(output, "cached-proof-preflight", [tools["lake"]["path"], "build", MODULE], cwd=ROOT / "lean", env=env)
        report["audit"] = audit(output, env, tools["lean"]["path"])
        report["controls"] = controls(output, env, tools["lean"]["path"])
        toolchain = read_json(args.toolchain)
        compiler, lib = Path(toolchain["compiler"]["path"]), Path(toolchain["compiler"]["zigLibDir"])
        if (toolchain["compiler"]["version"] != "0.17.0" or
                digest(lib.parent / "src/SemanticExport.zig") != digest(ROOT / "lean/zig_air/SemanticExport.zig")):
            raise ValueError("native toolchain does not use the pinned version and current exporter")
        report["toolchainReportSha256"] = digest(args.toolchain)
        report["native"] = {}
        for mode in ("ReleaseFast", "Debug", "ReleaseSafe"):
            directory = output / mode
            capture(argparse.Namespace(toolchain=args.toolchain, source=SOURCE, source_file=SOURCES, output=directory,
                root=["constructor_arguments.negate_left", "constructor_arguments.negate_right"], mode=mode))
            capture_report = read_json(directory / "report.json")
            command = read_json(directory / "ordinary.process.json")["command"]
            command[command.index("build-obj")] = "build-lib"
            command.append("-dynamic")
            library = directory / "negation.dylib"
            command[command.index("--cache-dir") + 1] = str(directory / "native-cache")
            command = ["-femit-bin=" + str(library) if item.startswith("-femit-bin=") else item for item in command]
            run(directory, "native-build", command)
            observed = native_cases(directory, library)
            report["native"][mode] = {**observed, "captureReportSha256": digest(directory / "report.json"),
                "objects": capture_report["objects"], "sourceFiles": capture_report["sourceFiles"],
                "arrayInventory": {name: array_shape(captured_path(directory / "report.json", entry))
                    for name, entry in capture_report["functions"].items() if entry["requested"]}}
        proof, artifacts = prove.check_module(MODULE, CLAIMS, lean_bin=args.lean_bin, jobs=4, fresh=True)
        directory = output / "proof"
        directory.mkdir()
        for name, data in artifacts.items():
            (directory / name).write_bytes(data)
        write_json(directory / "report.json", proof)
        report["proofReportSha256"] = digest(directory / "report.json")
        if (proof.get("status") != "passed" or proof.get("freshKernelReplay") is not True or
                proof.get("replayIncludesImports") is not True or proof.get("auditedDeclarations") != CLAIMS):
            raise ValueError("temporary argument proof or fresh imported-kernel replay failed")
        if (python_inputs() != report["pythonInputs"] or lean_check.source_inputs() != report["leanInputs"] or
                source_files(SOURCE, SOURCES) != sources or digest(args.toolchain) != report["toolchainReportSha256"]):
            raise ValueError("temporary argument acceptance inputs changed")
        report.update(status="passed", typedTemporaryInitializationVerified=True,
            preparedConstructorInputVerified=True, ordinaryTemporaryCleanupVerified=True)
    except BaseException as error:
        report["error"] = str(error)
        raise
    finally:
        write_json(output / "report.json", report)
    print("Negation temporary preparation and constructor input passed; native graph correspondence and recursive induction remain open.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    check(parser.parse_args())


if __name__ == "__main__":
    main()
