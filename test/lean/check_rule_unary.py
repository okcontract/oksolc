#!/usr/bin/env python3
"""Check the three live RuleList unary literal segments.
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
import extract_rule_unary as admission
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

SOURCE = ROOT / "test/lean/constructor_rule_unary.zig"
MODULE = "Compiler.Extraction.InternerRuleUnaryTests"
NS = "Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryUnary."
CLAIMS = [NS + "BorrowedInput." + name for name in ("invoke_of_load", "invoke_read_error", "invoke_verified")]
CLAIMS += [NS + "RuleLiteral." + name for name in (
    "opcode_binding", "nested_initializer_from_load", "exponent_initializer_from_load", "parity_initializer", "child_error", "child_return")]
CLAIMS += [NS + "RuleLiteral.Tests." + name for name in (
    "physical_operand_is_observed", "nested_word_is_loaded", "exponent_word_is_loaded", "parity_id_is_used", "original_borrow_survives",
    "ordinary_success_unwinds", "ordinary_oom_unwinds", "bounds_reject_before_allocation", "missing_memory_rejects_before_allocation",
    "unread_word_rejects_before_allocation", "child_oom_keeps_growth_without_allocation", "child_rejection_keeps_growth_without_allocation",
    "child_success_uses_returned_id_and_world", "later_oom_preserves_growth_and_unwinds", "nested_source_represented",
    "nonvacuous_borrowed_constructor_contract")]
CLAIMS += [NS.rsplit("TemporaryUnary.", 1)[0] + "TemporaryMemory.readId_of_load", NS + "invoke_verified", NS + "prepare_verified"]


def audit(output, env, lean):
    result = check_word_swap.audit(output, env, lean, MODULE, CLAIMS)
    claims = {record["theorem"]: set(record["dependencies"]) for record in read_json(output / "audit.json")["claims"]}
    requirements = {
        NS + "BorrowedInput.invoke_verified": {NS + "BorrowedInput.invoke_of_load", NS + "invoke_verified",
            NS + "prepare_verified", "Compiler.ZigAir.Memory.allocate", "Compiler.ZigAir.Memory.load"},
        NS + "RuleLiteral.nested_initializer_from_load": {NS + "BorrowedInput.invoke_of_load", NS + "unaryBuilder"},
        NS + "RuleLiteral.exponent_initializer_from_load": {NS + "BorrowedInput.invoke_of_load", NS + "unaryBuilder"},
        NS + "RuleLiteral.child_error": {NS + "RuleLiteral.afterParity", "Compiler.Algebraic.Effect.bind"},
        NS + "RuleLiteral.child_return": {NS + "RuleLiteral.afterParity", "Compiler.Algebraic.Effect.bind", NS + "invoke"},
        NS + "RuleLiteral.Tests.nonvacuous_borrowed_constructor_contract": {NS + "BorrowedInput.invoke_verified"},
    }
    for name, required in requirements.items():
        if not required <= claims[name]:
            raise ValueError("RuleList unary proof lost dependencies: " + name + ": " + ", ".join(sorted(required - claims[name])))
    return {**result, "checkedDependencies": sorted(requirements)}


def controls(output, env, lean):
    directory = ROOT / "lean/Compiler/Extraction"
    model = without_imports((directory / "InternerBorrowedUnary.lean").read_text())
    program = without_imports(admission.OUTPUT.read_text())
    proofs = without_imports((directory / "InternerRuleUnaryProofs.lean").read_text())
    tests = without_imports((directory / "InternerRuleUnaryTests.lean").read_text())
    imports = "import Compiler.Extraction.InternerTemporaryUnaryProofs\nimport Compiler.Extraction.InternerTemporaryUnaryTests\nimport Compiler.Extraction.DispatchProgram\n"
    records = [mutation_check(output, "rule-unary-complete-unchanged", imports + model + program + proofs + tests, True, env, lean)]
    observed = re.sub(r"\ntheorem [\s\S]*?(?=\n(?:def |theorem |end ))", "", model)
    fixtures = re.sub(r"\ntheorem [\s\S]*?(?=\n(?:def |theorem |end ))", "", tests)
    suffix = "\nend Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryUnary.RuleLiteral.Tests"
    fixtures = fixtures[:fixtures.rindex(suffix)] + """
example : (run .nestedIszero nestedSource).1 = .ok 99 := by rfl'
example : (run .zeroBaseExponent exponentSource).1 = .ok 99 := by rfl'
example : (observed .nestedIszero nestedSource).1 = .ok 99 := by rfl'
example : (observed .zeroBaseExponent exponentSource).1 = .ok 99 := by rfl'
example : (run .nestedIszero ⟨0, 1, 0⟩).2.memory.memory.nextId = 3 := by rfl'
example : (run .nestedIszero ⟨0, 1, 0⟩).1 = .error (.memory (.preparation (.memory .sourceBounds))) := by rfl'
example : (run .zeroBaseExponent ⟨99, 0, 2⟩).2.memory.memory.nextId = 3 := by rfl'
example : (afterChild (.error (.language .outOfMemory))).2.memory.memory.nextId = 3 := by rfl'
example : (afterChild (.error (.language .outOfMemory))).2.graph.read 98 = some 11 := by rfl'
example : (afterChild).2.graph.read 98 = some 11 := by rfl'
example : (afterChild).1 = .ok 99 := by rfl'
""" + suffix + "\n"
    diagnostics = imports + "set_option pp.maxSteps 8\nset_option pp.deepTerms false\nset_option pp.notation false\n"
    records.append(mutation_check(output, "rule-unary-observations-unchanged", diagnostics + observed + program + fixtures, True, env, lean))
    child_body = program[program.index("def afterParity "):program.rindex("\nend ")]
    child_start = """def afterParity (child : GraphAction σ NodeId) (external : External σ) (budget allocator : Nat)
    (p : Primitives σ) (q : Caller.Queries) : GraphAction σ NodeId := fun before =>
  match child before with
"""
    for name, layer, before, after in (
        ("wrong-nested-source-index", "program", "source 0", "source 1"),
        ("wrong-exponent-source-index", "program", "source 1", "source 0"),
        ("omitted-slice-bounds", "model", "if index < source.length then", "if index < source.length ∨ True then"),
        ("manufactured-initializer-id", "model", "opcode operand before", "opcode (operand + 1) before"),
        ("lost-child-world", "program", child_body, child_start +
            "  | (.error fault, reached) => (.error fault, reached)\n  | (.ok parity, _reached) => zigLiteral .parity external budget allocator p q ⟨0, 0, 0⟩ parity before\n"),
        ("discard-child-error-state", "program", child_body, child_start +
            "  | (.error fault, _reached) => (.error fault, before)\n  | (.ok parity, reached) => zigLiteral .parity external budget allocator p q ⟨0, 0, 0⟩ parity reached\n"),
        ("continue-after-child-error", "program", child_body, child_start +
            "  | (.error fault, reached) =>\n    let (_, last) := zigLiteral .parity external budget allocator p q ⟨0, 0, 0⟩ 1 reached\n    (.error fault, last)\n  | (.ok parity, reached) => zigLiteral .parity external budget allocator p q ⟨0, 0, 0⟩ parity reached\n"),
    ):
        target = observed if layer == "model" else program
        if target.count(before) != 1:
            raise ValueError("ambiguous RuleList unary control: " + name)
        changed = target.replace(before, after)
        records.append(mutation_check(output, "rule-unary-" + name,
            diagnostics + (changed if layer == "model" else observed) + (changed if layer == "program" else program) + fixtures,
            False, env, lean))
    for record in records:
        text = (output / (record["name"] + ".stdout")).read_text()
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant", text, re.I):
            raise ValueError("RuleList unary control hit a resource or syntax failure: " + record["name"])
    return records


class Event(ctypes.Structure):
    _fields_ = [(name, ctypes.c_uint32) for name in ("opcode", "first", "second")]
    _fields_ += [(name, ctypes.c_size_t) for name in ("length", "pointer", "alignment")]


class Observation(ctypes.Structure):
    _fields_ = [(name, ctypes.c_uint32) for name in (
        "site", "fail_operation", "fail_constant", "constant_result", "first_result", "second_result", "third_result",
        "operation_calls", "constant_calls", "graph_growth", "returned_error", "constant_low_word")]
    _fields_ += [(name, ctypes.c_size_t) for name in ("second_length", "third_length")]
    _fields_ += [(name, ctypes.c_uint32 * 4) for name in ("input_words", "second_words", "third_words")]
    _fields_ += [("events", Event * 3)]


def native_cases(output, library):
    native = ctypes.CDLL(str(library))
    function = native.rule_literal
    function.argtypes, function.restype = [ctypes.POINTER(Observation)], ctypes.c_uint32
    cases, sentinel = [], 0xA5A5A5A5
    for site in range(3):
        for operand, constant_id, first, second, third in ((3, 80, 99, 42, 13), (0, 1, 0xFFFFFFFF, 0, 0), (0xFFFFFFFF, 255, 0, 0xFFFFFFFF, 1)):
            for second_length, third_length in (((1, 1), (0, 1), (2, 1), (1, 0), (1, 2)) if site == 0 else ((1, 1),)):
                for fail_operation in (range(4) if site == 2 else range(2)):
                    for fail_constant in ((0, 1) if site == 2 else (0,)):
                        observed = Observation(site, fail_operation, fail_constant, constant_id, first, second, third,
                            0, 0, 0, 0, sentinel, second_length, third_length,
                            (ctypes.c_uint32 * 4)(sentinel, 29 if site == 0 else 7, operand, sentinel),
                            (ctypes.c_uint32 * 4)(sentinel, 17, 18, sentinel),
                            (ctypes.c_uint32 * 4)(sentinel, operand, 19, sentinel),
                            (Event * 3)(*(Event(*([sentinel] * 6)) for _ in range(3))))
                        initial = {name: getattr(observed, name) for name, _ in Observation._fields_ if name not in ("events", "input_words", "second_words", "third_words")}
                        returned = function(ctypes.byref(observed))
                        reached = site != 0 or second_length == third_length == 1
                        total = 3 if site == 2 else 1
                        constant_calls = int(site == 2)
                        calls = 0 if fail_constant or not reached else min(fail_operation, total) if fail_operation else total
                        failed = bool(fail_constant or reached and 0 < fail_operation <= total)
                        actual_events = [{name: getattr(event, name) for name, _ in Event._fields_} for event in observed.events]
                        borrowed = [ctypes.addressof(observed) + getattr(Observation, name).offset + 4
                                    for name in ("input_words", "second_words", "third_words")]
                        actual = {name: getattr(observed, name) for name, _ in Observation._fields_ if name not in ("events", "input_words", "second_words", "third_words")}
                        actual.update({name: list(getattr(observed, name)) for name in ("input_words", "second_words", "third_words")})
                        actual["events"] = [{**event, "pointer": "separate-live-array" if event["pointer"] > 0 and event["pointer"] not in borrowed else "invalid-array"}
                                            if index < calls else event for index, event in enumerate(actual_events)]
                        actual["returned"] = returned
                        operands = [[operand, constant_id], [first], [second, first]] if site == 2 else [[operand]]
                        opcodes = [22, 21, 3] if site == 2 else [21]
                        events = [{"opcode": opcodes[index], "first": operands[index][0],
                                   "second": operands[index][1] if len(operands[index]) == 2 else sentinel,
                                   "length": len(operands[index]), "pointer": "separate-live-array", "alignment": 0}
                                  if index < calls else {name: sentinel for name, _ in Event._fields_} for index in range(3)]
                        expected = {**initial, "operation_calls": calls, "constant_calls": constant_calls,
                            "constant_low_word": 1 if constant_calls else sentinel,
                            "graph_growth": constant_calls - int(bool(fail_constant)) + calls - int(bool(calls and failed)),
                            "returned_error": int(failed), "events": events,
                            "input_words": [sentinel, 29 if site == 0 else 7, operand, sentinel],
                            "second_words": [sentinel, 17, 18, sentinel], "third_words": [sentinel, operand, 19, sentinel],
                            "returned": 0 if failed or not reached else third if site == 2 else first}
                        cases.append({"inputs": {"site": site, "operand": operand, "constantId": constant_id,
                            "results": [first, second, third], "lengths": [second_length, third_length],
                            "failOperation": fail_operation, "failConstant": fail_constant},
                            "rawEvents": actual_events, "rawBorrowedPointers": borrowed, "actual": actual, "expected": expected})
    path = output / "native-observations.json"
    write_json(path, {"schema": "oksolc.rule-unary-native-controls.v1", "librarySha256": digest(library), "cases": cases,
        "nativeQueryCorrespondenceVerified": False, "completeExponentRuleVerified": False})
    if any(case["actual"] != case["expected"] for case in cases):
        raise ValueError("native RuleList unary literal observation mismatch")
    return {"cases": len(cases), "librarySha256": digest(library), "sha256": digest(path)}


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.rule-unary-literals.v1", "status": "failed", "jobs": 4,
        "scope": "three live one-word literal segments of the complete RuleList dispatcher",
        "typedLiteralPreparationVerified": False, "preparedConstructorInputVerified": False,
        "ordinaryTemporaryCleanupVerified": False, "completeExponentRuleVerified": False,
        "nativeQueryCorrespondenceVerified": False, "completeRecursiveConstructorsVerified": False,
        "airControlSemanticsVerified": False, "nativeBackendVerified": False, "wholeCompilerVerified": False}
    try:
        report["pythonInputs"], report["leanInputs"] = python_inputs(), lean_check.source_inputs()
        report["admission"], report["inventory"] = admission.check(), constructor_inventory.check()
        report["constructorBinding"] = constructor_frame_checks.bindings()
        sources = source_files(SOURCE, SOURCES)
        env, _, tools = lean_check.toolchain(args.lean_bin, 4)
        report["tools"] = tools
        run(output, "python-preflight", [sys.executable, "-m", "unittest", "discover", "-s", "test/lean", "-p", "test_rule_unary.py"], cwd=ROOT)
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
                root=["constructor_rule_unary.rule_literal"], mode=mode))
            captured = read_json(directory / "report.json")
            dispatchers = {name: entry for name, entry in captured["functions"].items()
                           if name.startswith("src.libevmasm.rule_list.simplifyWithOptions__")}
            if len(dispatchers) != 1:
                raise ValueError("native complete-dispatcher capture is absent or ambiguous")
            command = read_json(directory / "ordinary.process.json")["command"]
            command[command.index("build-obj")] = "build-lib"
            command.append("-dynamic")
            library = directory / "rule-unary.dylib"
            command[command.index("--cache-dir") + 1] = str(directory / "native-cache")
            command = ["-femit-bin=" + str(library) if item.startswith("-femit-bin=") else item for item in command]
            run(directory, "native-build", command)
            observed = native_cases(directory, library)
            report["native"][mode] = {**observed, "captureReportSha256": digest(directory / "report.json"),
                "objects": captured["objects"], "sourceFiles": captured["sourceFiles"],
                "arrayInventory": {name: array_inventory(captured_path(directory / "report.json", entry), 1, 3)
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
            raise ValueError("RuleList unary proof or fresh imported-kernel replay failed")
        if (python_inputs() != report["pythonInputs"] or lean_check.source_inputs() != report["leanInputs"] or
                source_files(SOURCE, SOURCES) != sources or admission.check() != report["admission"] or
                digest(args.toolchain) != report["toolchainReportSha256"] or digest(compiler) != toolchain["compiler"]["sha256"]):
            raise ValueError("RuleList unary acceptance inputs changed")
        report.update(status="passed", typedLiteralPreparationVerified=True,
            preparedConstructorInputVerified=True, ordinaryTemporaryCleanupVerified=True)
    except BaseException as error:
        report["error"] = str(error)
        raise
    finally:
        write_json(output / "report.json", report)
    print("Three live RuleList unary literal segments passed; native prefixes, remaining arrays and recursive induction remain open.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    check(parser.parse_args())


if __name__ == "__main__":
    main()
