#!/usr/bin/env python3
"""Check the two three-word RuleList modular literal segments.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
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
import extract_rule_ternary as admission
import prove
import check_word_swap
import constructor_frame_checks
from check_local_arguments import SOURCES
from check_temporary_arguments import python_inputs
from constructor_array_checks import array_inventory
from build_toolchain import digest, run, write_json
from capture import capture, read_json, source_files
from generate import captured_path
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

SOURCE = ROOT / "test/lean/constructor_rule_ternary.zig"
MODULE = "Compiler.Extraction.InternerRuleTernaryTests"
NS = "Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryTernary."
CLAIMS = [NS + name for name in (
    "writeTriple_of_phases", "writeTriple_pair_error", "writeTriple_third_error", "writeTriple_of_stores", "triple_contents",
    "prepare_verified", "invoke_verified", "borrowed_bad_length", "borrowed_first_error", "borrowed_second_error",
    "borrowed_of_loads", "borrowed_verified")]
CLAIMS += [NS + "RuleLiteral." + name for name in ("opcode_binding", "initializer_projection")]
CLAIMS += [NS + "RuleLiteral.Tests." + name for name in (
    "actual_allocation", "initialized_all_three", "good_is_derived", "older_allocations_preserved", "both_literal_results",
    "offset_borrow_succeeds", "success_unwinds", "ordinary_oom_unwinds", "physical_ids_observed", "short_length_rejects_before_allocation",
    "long_length_rejects_before_allocation", "first_load_rejects_before_allocation", "second_load_rejects_before_allocation",
    "stack_limit_remains_rejection", "third_store_rejects_with_pair_prefix", "parent_stack_borrow_survives", "source_represented", "addition_body",
    "nonvacuous_borrowed_constructor_contract")]
CLAIMS += ["Compiler.Algebraic.Effect.bind_success"]


def audit(output, env, lean):
    result = check_word_swap.audit(output, env, lean, MODULE, CLAIMS)
    claims = {record["theorem"]: set(record["dependencies"]) for record in read_json(output / "audit.json")["claims"]}
    requirements = {
        NS + "prepare_verified": {NS + "writeTriple_of_stores", NS + "triple_contents",
            "Compiler.ZigAir.Memory.allocate", "Compiler.ZigAir.Memory.WordArray.write_total"},
        NS + "writeTriple_of_phases": {"Compiler.Algebraic.Effect.bind_success",
            NS.replace("TemporaryTernary.", "TemporaryArguments.writePair"),
            NS.replace("TemporaryTernary.", "TemporaryUnary.writeOne")},
        NS + "borrowed_verified": {NS + "borrowed_of_loads", NS + "invoke_verified", NS + "prepare_verified",
            "Compiler.ZigAir.Memory.load"},
        NS + "RuleLiteral.initializer_projection": {NS + "borrowed_of_loads", NS + "RuleLiteral.constructors"},
        NS + "RuleLiteral.Tests.nonvacuous_borrowed_constructor_contract": {NS + "borrowed_verified"},
    }
    for name, required in requirements.items():
        if not required <= claims[name]:
            raise ValueError("RuleList ternary proof lost dependencies: " + name + ": " + ", ".join(sorted(required - claims[name])))
    return {**result, "checkedDependencies": sorted(requirements)}


def controls(output, env, lean):
    directory = ROOT / "lean/Compiler/Extraction"
    model = without_imports((directory / "InternerTemporaryTernary.lean").read_text())
    program = without_imports(admission.OUTPUT.read_text())
    proofs = without_imports((directory / "InternerRuleTernaryProofs.lean").read_text())
    tests = without_imports((directory / "InternerRuleTernaryTests.lean").read_text())
    imports = "import Compiler.Extraction.InternerTemporaryUnaryTests\nimport Compiler.Extraction.DispatchProgram\n"
    records = [mutation_check(output, "ternary-complete-unchanged", imports + model + program + proofs + tests, True, env, lean)]
    observed = re.sub(r"\ntheorem [\s\S]*?(?=\n(?:def |theorem |end ))", "", model)
    fixtures = re.sub(r"\ntheorem [\s\S]*?(?=\n(?:def |theorem |end ))", "", tests)
    suffix = "\nend Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryTernary.RuleLiteral.Tests"
    fixtures = fixtures[:fixtures.rindex(suffix)] + """
example : observed.1 = .ok 99 := by rfl'
example : Compiler.ZigAir.Memory.load prepared.memory.memory (target.pointer 2) = .ok (number 2) := by rfl'
example : (run .addition ⟨0, 0, 3⟩).1 = .error (.memory (.preparation (.memory .sourceBounds))) := by rfl'
example : (run .addition ⟨0, 2, 2⟩).2.memory.memory.nextId = 3 := by rfl'
example : Compiler.ZigAir.Memory.load prefixReject.2.memory.memory ((⟨3, 0, 2⟩ : View).pointer 0) = .ok (number 3) := by rfl'
example : Compiler.ZigAir.Memory.load prefixReject.2.memory.memory ((⟨3, 0, 2⟩ : View).pointer 1) = .ok (number 1) := by rfl'
""" + suffix + "\n"
    diagnostics = imports + "set_option pp.maxSteps 8\nset_option pp.deepTerms false\nset_option pp.notation false\n"
    records.append(mutation_check(output, "ternary-observations-unchanged", diagnostics + observed + program + fixtures, True, env, lean))
    triple_start = observed.index("def writeTriple ")
    triple_end = observed.index("\ndef prepare ", triple_start)
    rollback = """def writeTriple (source : View) (first second third : NodeId) : GraphAction σ View := fun before =>
  match TemporaryArguments.writePair source first second before with
  | (.error fault, reached) => (.error fault, reached)
  | (.ok _, middle) => match TemporaryUnary.writeOne (tailView source) third middle with
    | (.error fault, _reached) => (.error fault, before)
    | (.ok _, after) => (.ok source, after)
"""
    allocate_on_error = """| .ok first => match TemporaryMemory.readId before.memory.memory source 1 with
      | .error fault =>
        let reached := match Compiler.ZigAir.Memory.allocate before.memory.memory (.array 3 word) with
          | .error _ => before
          | .ok (_, memory) => { before with memory := { before.memory with memory } }
        (.error (.memory (.preparation (.memory fault))), reached)"""
    for name, before, after in (
        ("wrong-third-offset", "source.first + 2, 1", "source.first + 1, 1"),
        ("omitted-third-store", observed[triple_start:triple_end],
            "def writeTriple (source : View) (first second _third : NodeId) : GraphAction σ View := TemporaryArguments.writePair source first second\n"),
        ("repeated-source-index", "readId before.memory.memory source 1 with", "readId before.memory.memory source 0 with"),
        ("manufactured-third-id", "opcode first second third before", "opcode first second (third + 1) before"),
        ("omitted-length-guard", "if source.length = 2 then", "if True then"),
        ("allocation-after-read-rejection", "| .ok first => match TemporaryMemory.readId before.memory.memory source 1 with\n      | .error fault => (.error (.memory (.preparation (.memory fault))), before)", allocate_on_error),
        ("rollback-reached-store-prefix", observed[triple_start:triple_end], rollback),
    ):
        if observed.count(before) != 1:
            raise ValueError("ambiguous RuleList ternary control: " + name)
        records.append(mutation_check(output, "ternary-" + name,
            diagnostics + observed.replace(before, after) + program + fixtures, False, env, lean))
    for record in records:
        text = (output / (record["name"] + ".stdout")).read_text()
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant", text, re.I):
            raise ValueError("RuleList ternary control hit a resource or syntax failure: " + record["name"])
    return records


def literal_inventory(path):
    result = array_inventory(path, 3, 2)
    instructions = {inst["index"]: inst for inst in read_json(path)["instructions"]}
    reference = lambda inst: {"kind": "instruction", "index": inst["index"]}
    for array in result["arrays"]:
        reads, elements, bases = [], [], []
        for index, store_index in enumerate(array["storeInstructions"][:2]):
            stored = instructions[store_index]
            rhs = stored.get("rhs", {})
            loaded = instructions.get(rhs.get("index"), {}) if rhs.get("kind") == "instruction" else {}
            operand = loaded.get("operand", {})
            element = instructions.get(operand.get("index"), {}) if operand.get("kind") == "instruction" else {}
            lhs = element.get("lhs", {})
            base = instructions.get(lhs.get("index"), {}) if lhs.get("kind") == "instruction" else {}
            if (loaded.get("tag") != "load" or loaded.get("type") != {"kind": "int", "bits": 32, "signedness": "unsigned"} or
                    element.get("tag") != "slice_elem_ptr" or element.get("rhs", {}).get("value") != index or
                    element.get("rhs", {}).get("kind") != "constant" or base.get("tag") != "load" or
                    base.get("type", {}).get("flags", {}).get("size") != "slice" or
                    base["type"]["flags"].get("isConst") is not True or
                    base["type"].get("child") != loaded["type"] or loaded.get("operand") != reference(element)):
                raise ValueError("native modular literal readonly source or loaded operand changed")
            reads.append(loaded); elements.append(element); bases.append(base)
        if (bases[0].get("operand") is None or bases[0].get("operand") != bases[1].get("operand") or
                not elements[0]["index"] < reads[0]["index"] < elements[1]["index"] < reads[1]["index"] < array["arrayInstruction"]):
            raise ValueError("native modular literal source identity or read-before-allocation order changed")
        array["initializerReadInstructions"] = [inst["index"] for inst in reads]
        array["retainedThirdOperand"] = instructions[array["storeInstructions"][2]].get("rhs")
    return result


class Observation(ctypes.Structure):
    _fields_ = [(name, ctypes.c_uint32) for name in (
        "site", "for_yul", "fail_operation", "fail_constant", "constant_result", "operation_result",
        "operation_calls", "constant_calls", "graph_growth", "returned_error", "opcode")]
    _fields_ += [(name, ctypes.c_uint64) for name in ("modulus", "constant_value")]
    _fields_ += [(name, ctypes.c_size_t) for name in ("nested_length", "length", "pointer", "alignment")]
    _fields_ += [(name, ctypes.c_uint32 * count) for name, count in (("input_words", 4), ("nested_words", 5), ("observed_words", 3))]


def native_cases(output, library):
    native = ctypes.CDLL(str(library))
    function = native.rule_ternary
    function.argtypes, function.restype = [ctypes.POINTER(Observation)], ctypes.c_uint32
    cases, sentinel = [], 0xA5A5A5A5
    for site in range(2):
        for for_yul in range(2):
            for length in range(4):
                for modulus in (2, 8, 1 << 63, 3):
                    for left, right, first, second, constant, result in (
                            (29, 7, 3, 1, 80, 99), (0xFFFFFFFF, 2, 0, 0xFFFFFFFF, 1, 0), (0, 255, 0xFFFFFFFF, 1, 42, 0xFFFFFFFF)):
                        for fail_operation in range(2):
                            for fail_constant in range(2):
                                observed = Observation(site, for_yul, fail_operation, fail_constant, constant, result,
                                    0, 0, 0, 0, sentinel, modulus, sentinel, length, sentinel, sentinel, sentinel,
                                    (ctypes.c_uint32 * 4)(sentinel, left, right, sentinel),
                                    (ctypes.c_uint32 * 5)(sentinel, first, second, 17, sentinel),
                                    (ctypes.c_uint32 * 3)(sentinel, sentinel, sentinel))
                                initial = {name: getattr(observed, name) for name, _ in Observation._fields_
                                           if name not in ("input_words", "nested_words", "observed_words")}
                                returned = function(ctypes.byref(observed))
                                power = modulus != 3
                                ternary = bool(power and for_yul and length == 2)
                                constants = int(power and not ternary)
                                calls = int(power and not (constants and fail_constant))
                                failed = bool(constants and fail_constant or calls and fail_operation)
                                borrowed = [ctypes.addressof(observed) + getattr(Observation, name).offset + 4
                                            for name in ("input_words", "nested_words")]
                                actual = {name: getattr(observed, name) for name, _ in Observation._fields_
                                          if name not in ("input_words", "nested_words", "observed_words")}
                                raw_pointer = actual["pointer"]
                                if calls:
                                    actual["pointer"] = "separate-live-array" if raw_pointer > 0 and raw_pointer not in borrowed else "invalid-array"
                                actual.update({name: list(getattr(observed, name)) for name in ("input_words", "nested_words", "observed_words")})
                                actual["returned"] = returned
                                expected = {**initial, "operation_calls": calls, "constant_calls": constants,
                                    "graph_growth": constants - int(bool(constants and fail_constant)) + calls - int(bool(calls and fail_operation)),
                                    "returned_error": int(failed), "constant_value": modulus - 1 if constants else sentinel,
                                    "opcode": (9 if site == 0 else 8) if ternary else 22 if calls else sentinel,
                                    "length": 3 if ternary else 2 if calls else sentinel,
                                    "pointer": "separate-live-array" if calls else sentinel, "alignment": 0 if calls else sentinel,
                                    "input_words": [sentinel, left, right, sentinel], "nested_words": [sentinel, first, second, 17, sentinel],
                                    "observed_words": [first, second, right] if ternary else [left, constant, sentinel] if calls else [sentinel] * 3,
                                    "returned": 0 if failed or not calls else result}
                                cases.append({"inputs": {"site": site, "forYul": for_yul, "nestedLength": length, "modulus": modulus,
                                    "ids": [left, right, first, second, constant, result], "failOperation": fail_operation, "failConstant": fail_constant},
                                    "rawPointer": raw_pointer, "rawBorrowedPointers": borrowed, "actual": actual, "expected": expected})
    path = output / "native-observations.json"
    write_json(path, {"schema": "oksolc.rule-ternary-native-controls.v1", "librarySha256": digest(library), "cases": cases,
        "nativeQueryCorrespondenceVerified": False, "completeModularRuleVerified": False})
    if any(case["actual"] != case["expected"] for case in cases):
        raise ValueError("native RuleList ternary literal observation mismatch")
    return {"cases": len(cases), "librarySha256": digest(library), "sha256": digest(path)}


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.rule-ternary-literals.v1", "status": "failed", "jobs": 4,
        "scope": "the two three-word modular literal segments of the complete RuleList dispatcher",
        "typedLiteralPreparationVerified": False, "preparedConstructorInputVerified": False,
        "ordinaryTemporaryCleanupVerified": False, "completeModularRuleVerified": False,
        "nativeQueryCorrespondenceVerified": False, "completeRecursiveConstructorsVerified": False,
        "airControlSemanticsVerified": False, "nativeBackendVerified": False, "wholeCompilerVerified": False}
    try:
        report["pythonInputs"], report["leanInputs"] = python_inputs(), lean_check.source_inputs()
        report["admission"], report["inventory"] = admission.check(), constructor_inventory.check()
        report["constructorBinding"] = constructor_frame_checks.bindings()
        sources = source_files(SOURCE, SOURCES)
        env, _, tools = lean_check.toolchain(args.lean_bin, 4)
        report["tools"] = tools
        run(output, "python-preflight", [sys.executable, "-m", "unittest", "discover", "-s", "test/lean", "-p", "test_rule_ternary.py"], cwd=ROOT)
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
            capture(argparse.Namespace(toolchain=args.toolchain, source=SOURCE, source_file=SOURCES, output=directory,
                root=["constructor_rule_ternary.rule_ternary"], mode=mode))
            captured = read_json(directory / "report.json")
            dispatchers = {name: entry for name, entry in captured["functions"].items()
                           if name.startswith("src.libevmasm.rule_list.simplifyWithOptions__")}
            if len(dispatchers) != 1:
                raise ValueError("native complete-dispatcher capture is absent or ambiguous")
            command = read_json(directory / "ordinary.process.json")["command"]
            command[command.index("build-obj")] = "build-lib"
            command.append("-dynamic")
            library = directory / "rule-ternary.dylib"
            command[command.index("--cache-dir") + 1] = str(directory / "native-cache")
            command = ["-femit-bin=" + str(library) if item.startswith("-femit-bin=") else item for item in command]
            run(directory, "native-build", command)
            observed = native_cases(directory, library)
            report["native"][mode] = {**observed, "captureReportSha256": digest(directory / "report.json"),
                "objects": captured["objects"], "sourceFiles": captured["sourceFiles"],
                "arrayInventory": {name: literal_inventory(captured_path(directory / "report.json", entry))
                                   for name, entry in dispatchers.items()}}
        proof, artifacts = prove.check_module(MODULE, CLAIMS, lean_bin=args.lean_bin, jobs=4, fresh=True)
        directory = output / "proof"
        directory.mkdir()
        for name, data in artifacts.items():
            (directory / name).write_bytes(data)
        write_json(directory / "report.json", proof)
        report["proofReportSha256"] = digest(directory / "report.json")
        if (proof.get("status") != "passed" or proof.get("freshKernelReplay") is not True or
                proof.get("replayIncludesImports") is not True or proof.get("auditedDeclarations") != CLAIMS):
            raise ValueError("RuleList ternary proof or fresh imported-kernel replay failed")
        if (python_inputs() != report["pythonInputs"] or lean_check.source_inputs() != report["leanInputs"] or
                source_files(SOURCE, SOURCES) != sources or admission.check() != report["admission"] or
                digest(args.toolchain) != report["toolchainReportSha256"] or digest(compiler) != toolchain["compiler"]["sha256"]):
            raise ValueError("RuleList ternary acceptance inputs changed")
        report.update(status="passed", typedLiteralPreparationVerified=True,
            preparedConstructorInputVerified=True, ordinaryTemporaryCleanupVerified=True)
    except BaseException as error:
        report["error"] = str(error)
        raise
    finally:
        write_json(output / "report.json", report)
    print("Both RuleList ternary literal segments passed; native prefixes, remaining arrays and recursive induction remain open.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    check(parser.parse_args())


if __name__ == "__main__":
    main()
