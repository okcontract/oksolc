#!/usr/bin/env python3
"""Check source-bound max-base EXP literals and their reached constructor chain.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import ctypes
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(ROOT / "lean"), str(ROOT / "lean/zig_air")]
import environment as lean_check
import constructor_inventory
import extract_rule_max_exponent as admission
import prove
import check_word_swap
import constructor_frame_checks
from check_rule_unary import Event
from check_local_arguments import SOURCES
from check_temporary_arguments import python_inputs
from constructor_array_checks import max_exponent_inventory
from build_toolchain import digest, run, write_json
from capture import capture, read_json, source_files
from generate import captured_path
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

SOURCE = ROOT / "test/lean/constructor_rule_max_exponent.zig"
MODULE = "Compiler.Extraction.InternerRuleMaxExponentTests"
NS = "Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryArguments."
CLAIMS = [NS + name for name in ("prepared_opcode_verified", "prepared_operation_verified", "invoke_of_preparation",
    "invoke_preparation_error", "invoke_verified", "borrowedFirst_of_load", "borrowedFirst_read_error", "borrowedFirst_verified")]
CLAIMS += [NS + "MaxExponent." + name for name in ("helper_projection", "parity_initializer", "even_initializer",
    "final_initializer", "constant_error", "after_constant", "parity_error", "after_parity", "even_error",
    "after_even", "final_error", "success")]
CLAIMS += [NS + "MaxExponent.Tests." + name for name in ("full_chain_result", "full_chain_unwinds", "original_borrow_survives", "reached_graph_growth",
    "constant_oom_skips_all_arrays", "constant_rejection_keeps_world", "bounds_reject_after_constant",
    "missing_borrow_rejects_after_constant", "wrong_offset_is_observed", "parity_oom_skips_later_arrays",
    "even_oom_keeps_parity_effects", "final_oom_keeps_even_effects", "first_allocator_oom_keeps_constant",
    "observation_rejection_keeps_storage", "older_parent_array_survives", "changed_returned",
    "post_constant_load_is_observed", "changed_operand_is_not_snapshot", "nonvacuous_pair_contract")]
CLAIMS += ["Compiler.Algebraic.Effect.bind_pure", "Compiler.Extraction.Dispatch.exp_evm_stage_safe",
    "Compiler.Extraction.Dispatch.exp_evm_miss", "Compiler.Extraction.Dispatch.exp_simplify_safe"]


def audit(output, env, lean):
    result = check_word_swap.audit(output, env, lean, MODULE, CLAIMS)
    claims = {record["theorem"]: set(record["dependencies"]) for record in read_json(output / "audit.json")["claims"]}
    requirements = {
        NS + "prepared_opcode_verified": {NS + "prepare_verified", "Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorFrame.operation_verified"},
        NS + "borrowedFirst_verified": {NS + "borrowedFirst_of_load", NS + "invoke_verified", NS + "prepare_verified", "Compiler.ZigAir.Memory.load"},
        NS + "MaxExponent.helper_projection": {"Compiler.Extraction.Dispatch.maxExponent"},
        NS + "MaxExponent.parity_initializer": {NS + "borrowedFirst_of_load", NS + "invoke"},
        NS + "MaxExponent.constant_error": {"Compiler.Algebraic.Effect.bind_failure", "Compiler.Extraction.Dispatch.maxExponent"},
        NS + "MaxExponent.after_constant": {"Compiler.Algebraic.Effect.bind_success", NS + "borrowedFirst"},
        NS + "MaxExponent.final_error": {NS + "MaxExponent.after_even", "Compiler.Algebraic.Effect.bind_failure"},
        NS + "MaxExponent.success": {NS + "MaxExponent.after_even", "Compiler.Algebraic.Effect.bind_success"},
        NS + "MaxExponent.Tests.nonvacuous_pair_contract": {NS + "invoke_verified"},
        "Compiler.Extraction.Dispatch.exp_evm_stage_safe": {"Compiler.Algebraic.Effect.bind_pure", "Compiler.Extraction.Dispatch.maxExponent", "Compiler.Extraction.Dispatch.exp_minus_one_safe"},
    }
    for name, required in requirements.items():
        if not required <= claims[name]:
            raise ValueError("max-base EXP proof lost dependencies: " + name + ": " + ", ".join(sorted(required - claims[name])))
    return {**result, "checkedDependencies": sorted(requirements)}


def controls(output, env, lean):
    directory = ROOT / "lean/Compiler/Extraction"
    # Keep the original imported definitions and a separately named diagnostic
    # copy. The complete unchanged copy is checked before any mutant is tried.
    original = NS.rstrip(".")
    diagnostic = original.replace("TemporaryArguments", "DiagnosticArguments")
    model = without_imports((directory / "InternerTemporaryArguments.lean").read_text()).replace(original, diagnostic)
    program = without_imports(admission.OUTPUT.read_text()).replace(original, diagnostic)
    proofs = without_imports((directory / "InternerRuleMaxExponentProofs.lean").read_text()).replace(original, diagnostic)
    tests = without_imports((directory / "InternerRuleMaxExponentTests.lean").read_text()).replace(original, diagnostic)
    imports = "import Compiler.Extraction.InternerTemporaryUnaryTests\nimport Compiler.Extraction.DispatchExponentProofs\n"
    bounded = "set_option pp.maxSteps 8\nset_option pp.deepTerms false\nset_option pp.notation false\n"
    records = [mutation_check(output, "max-exponent-complete-unchanged", imports + model + program + proofs + tests, True, env, lean)]
    def strip(text):
        text = re.sub(r"/--[\s\S]*?-/", "", text)
        return re.sub(r"\n(?:private )?theorem [\s\S]*?(?=\n(?:def |(?:private )?theorem |end ))", "", text)
    observed, fixtures = strip(model), strip(tests)
    suffix = "\nend " + diagnostic + ".MaxExponent.Tests"
    fixtures = fixtures[:fixtures.rindex(suffix)] + """
example : (run).1 = .ok (some 96) := by rfl'
example : (run).2.memory.memory.heap = original.memory.heap := by rfl'
example : run none (some (.language .outOfMemory)) = (.error (.language .outOfMemory), grown caller) := by rfl'
example : run none none Normalization.Tests.success ⟨0, 0, 1⟩ =
  (.error (.memory (.preparation (.memory .sourceBounds))), grown caller) := by rfl'
example : (zigChain changingConstant Normalization.Tests.success 160 7
  (callbacks) Caller.Tests.queries source mutableCaller).1 = .error .missingHandle := by rfl'
""" + suffix + "\n"
    records.append(mutation_check(output, "max-exponent-observations-unchanged", imports + bounded + observed + program + fixtures, True, env, lean))
    chain = program[program.index("def zigChain "):program.rindex("\nend ")]
    discard = chain[:chain.index(" :=") + 3] + " fun before =>\n" + """
  match constant 1 before with
  | (.error fault, _) => (.error fault, before)
  | (.ok one, reached) => (do
      let odd ← parity external budget allocator p q source one
      let even ← TemporaryUnary.invoke external budget allocator p q Compiler.Extraction.Dispatch.opISZERO odd
      return some (← invoke external budget allocator p q Compiler.Extraction.Dispatch.opSUB even odd)) reached
"""
    continue_error = discard.replace("| (.error fault, _) => (.error fault, before)", """| (.error fault, reached) =>
      let (_, last) := parity external budget allocator p q source 99 reached
      (.error fault, last)""")
    for name, layer, before, after in (
        ("wrong-exponent-index", "program", "opAND source 1 one", "opAND source 0 one"),
        ("wrong-returned-one", "program", "opAND source 1 one", "opAND source 1 (one + 1)"),
        ("swapped-final-operands", "program", "opcode even odd", "opcode odd even"),
        ("omitted-borrow-bound", "model", "if index < source.length then", "if index < source.length ∨ True then"),
        ("manufactured-first-id", "model", "source opcode [first, second] prepared)", "source opcode [first + 1, second] prepared)"),
        ("discard-constant-world", "program", chain, discard),
        ("continue-after-constant-error", "program", chain, continue_error),
        ("omit-ordinary-array-cleanup", "model", "unwind before.memory.memory.nextId\n    (ConstructorFrame.operation",
         "(fun ran => (ran.1, ran.2.world))\n    (ConstructorFrame.operation"),
    ):
        target = observed if layer == "model" else program
        if target.count(before) != 1:
            raise ValueError("ambiguous max-base EXP control: " + name)
        changed = target.replace(before, after)
        records.append(mutation_check(output, "max-exponent-" + name,
            imports + bounded + (changed if layer == "model" else observed) +
            (changed if layer == "program" else program) + fixtures, False, env, lean))
    for record in records:
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant",
                     (output / (record["name"] + ".stdout")).read_text(), re.I):
            raise ValueError("max-base EXP control hit a resource or syntax failure: " + record["name"])
    return records


class Observation(ctypes.Structure):
    _fields_ = [(name, ctypes.c_uint32) for name in ("fail_at", "mutate_input", "replacement", "constant_result",
        "parity_result", "even_result", "final_result", "call_count", "graph_growth", "returned_error")]
    _fields_ += [("base_words", ctypes.c_uint64 * 4), ("input_words", ctypes.c_uint32 * 4), ("events", Event * 4)]


def native_cases(output, library):
    native = ctypes.CDLL(str(library))
    function = native.max_exponent
    function.argtypes, function.restype = [ctypes.POINTER(Observation)], ctypes.c_uint32
    cases, sentinel = [], 0xA5A5A5A5
    for operand, replacement, one, odd, even, final in ((3, 1, 80, 99, 42, 13), (0, 0xFFFFFFFF, 1, 0xFFFFFFFF, 0, 0), (0xFFFFFFFF, 0, 255, 0, 0xFFFFFFFF, 1)):
        for mutate in (0, 1):
            for fail_at in range(5):
                observation = Observation(fail_at, mutate, replacement, one, odd, even, final, 0, 0, 0,
                    (ctypes.c_uint64 * 4)(*([0xFFFFFFFFFFFFFFFF] * 4)),
                    (ctypes.c_uint32 * 4)(sentinel, 7, operand, sentinel),
                    (Event * 4)(*(Event(*([sentinel] * 6)) for _ in range(4))))
                fields = [name for name, _ in Observation._fields_ if name not in ("events", "input_words", "base_words")]
                initial = {name: getattr(observation, name) for name in fields}
                returned = function(ctypes.byref(observation))
                count = fail_at or 4
                input_value = replacement if mutate and fail_at != 1 else operand
                operands, opcodes = [[1], [input_value, one], [odd], [even, odd]], [256, 22, 21, 3]
                pointers = [ctypes.addressof(observation) + Observation.input_words.offset + offset * 4 for offset in range(4)]
                raw = [{name: getattr(event, name) for name, _ in Event._fields_} for event in observation.events]
                actual = {name: getattr(observation, name) for name in fields}
                actual.update(returned=returned, input_words=list(observation.input_words), base_words=list(observation.base_words), events=[
                    {**event, "pointer": "separate-live-array" if event["pointer"] > 0 and event["pointer"] not in pointers else "invalid-array"}
                    if 0 < index < count else event for index, event in enumerate(raw)])
                events = [{"opcode": opcodes[index], "first": operands[index][0],
                    "second": operands[index][1] if len(operands[index]) == 2 else sentinel,
                    "length": len(operands[index]) if index else 0,
                    "pointer": "separate-live-array" if index else 0, "alignment": 0}
                    if index < count else {name: sentinel for name, _ in Event._fields_} for index in range(4)]
                expected = {**initial, "returned": 0 if fail_at else final, "returned_error": int(bool(fail_at)),
                    "call_count": count, "graph_growth": count - int(bool(fail_at)),
                    "input_words": [sentinel, 7, input_value, sentinel], "base_words": [0xFFFFFFFFFFFFFFFF] * 4, "events": events}
                cases.append({"inputs": {"operand": operand, "replacement": replacement, "results": [one, odd, even, final],
                    "mutateInput": mutate, "failAt": fail_at}, "rawEvents": raw, "rawInputPointers": pointers,
                    "actual": actual, "expected": expected})
    path = output / "native-observations.json"
    write_json(path, {"schema": "oksolc.max-exponent-native-controls.v1", "librarySha256": digest(library), "cases": cases,
        "inputMutationScope": "evaluation-order diagnostic; not a production borrow-frame contract",
        "nativeGraphCorrespondenceVerified": False, "completeExponentRuleVerified": False})
    if any(case["actual"] != case["expected"] for case in cases):
        raise ValueError("native max-base EXP constructor observation mismatch")
    return {"cases": len(cases), "sha256": digest(path), "librarySha256": digest(library)}


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.rule-max-exponent-constructors.v1", "status": "failed", "jobs": 4,
        "scope": "two pair literals and the four reached constructors of the max-base EXP branch",
        "typedLiteralPreparationVerified": False, "constructorOrderVerified": False,
        "completeExponentRuleVerified": False, "nativeGraphCorrespondenceVerified": False,
        "completeRecursiveConstructorsVerified": False, "airControlSemanticsVerified": False,
        "nativeBackendVerified": False, "wholeCompilerVerified": False}
    try:
        report["pythonInputs"], report["leanInputs"] = python_inputs(), lean_check.source_inputs()
        report["admission"], report["inventory"] = admission.check(), constructor_inventory.check()
        report["constructorBinding"] = constructor_frame_checks.bindings()
        sources = source_files(SOURCE, SOURCES)
        env, _, tools = lean_check.toolchain(args.lean_bin, 4)
        report["tools"] = tools
        run(output, "python-preflight", [sys.executable, "-m", "unittest", "discover", "-s", "test/lean", "-p", "test_rule_max_exponent.py"], cwd=ROOT)
        run(output, "cached-proof-preflight", [tools["lake"]["path"], "build", MODULE,
            "Compiler.Extraction.DispatchExponentTests", "Compiler.Extraction.InternerTemporaryArgumentsTests"], cwd=ROOT / "lean", env=env)
        report["audit"], report["controls"] = audit(output, env, tools["lean"]["path"]), controls(output, env, tools["lean"]["path"])
        toolchain = read_json(args.toolchain)
        compiler, lib = Path(toolchain["compiler"]["path"]), Path(toolchain["compiler"]["zigLibDir"])
        if (toolchain["compiler"]["version"] != "0.17.0" or digest(compiler) != toolchain["compiler"]["sha256"] or
                digest(lib.parent / "src/SemanticExport.zig") != digest(ROOT / "lean/zig_air/SemanticExport.zig")):
            raise ValueError("native toolchain does not use the pinned compiler and current exporter")
        report["toolchainReportSha256"], report["native"] = digest(args.toolchain), {}
        owner = next(source for source in constructor_inventory.inventory()["sources"] if source["path"] == "src/libevmasm/rule_list.zig")
        pair_count = sum(site["owner"] == "simplifyWithOptions" and site["storage"] == "temporary" and site["arity"] == 2 for site in owner["sites"])
        for mode in ("ReleaseFast", "Debug", "ReleaseSafe"):
            directory = output / mode
            capture(argparse.Namespace(toolchain=args.toolchain, source=SOURCE, source_file=SOURCES, output=directory,
                root=["constructor_rule_max_exponent.max_exponent"], mode=mode))
            captured = read_json(directory / "report.json")
            dispatchers = {name: entry for name, entry in captured["functions"].items() if name.startswith("src.libevmasm.rule_list.simplifyWithOptions__")}
            if len(dispatchers) != 1:
                raise ValueError("native complete-dispatcher capture is absent or ambiguous")
            command = read_json(directory / "ordinary.process.json")["command"]
            command[command.index("build-obj")] = "build-lib"
            command.append("-dynamic")
            library = directory / "max-exponent.dylib"
            command[command.index("--cache-dir") + 1] = str(directory / "native-cache")
            command = ["-femit-bin=" + str(library) if item.startswith("-femit-bin=") else item for item in command]
            run(directory, "native-build", command)
            observed = native_cases(directory, library)
            report["native"][mode] = {**observed, "captureReportSha256": digest(directory / "report.json"),
                "objects": captured["objects"], "sourceFiles": captured["sourceFiles"],
                "sourceOwnerPairLiteralCount": pair_count,
                "arrayInventory": {name: max_exponent_inventory(captured_path(directory / "report.json", entry)) for name, entry in dispatchers.items()}}
        proof, artifacts = prove.check_module(MODULE, CLAIMS, lean_bin=args.lean_bin, jobs=4, fresh=True)
        directory = output / "proof"
        directory.mkdir()
        for name, data in artifacts.items():
            (directory / name).write_bytes(data)
        write_json(directory / "report.json", proof)
        report["proofReportSha256"] = digest(directory / "report.json")
        if (proof.get("status") != "passed" or proof.get("freshKernelReplay") is not True or
                proof.get("replayIncludesImports") is not True or proof.get("auditedDeclarations") != CLAIMS):
            raise ValueError("max-base EXP proof or fresh imported-kernel replay failed")
        if (python_inputs() != report["pythonInputs"] or lean_check.source_inputs() != report["leanInputs"] or
                source_files(SOURCE, SOURCES) != sources or admission.check() != report["admission"] or
                digest(args.toolchain) != report["toolchainReportSha256"] or digest(compiler) != toolchain["compiler"]["sha256"]):
            raise ValueError("max-base EXP acceptance inputs changed")
        report.update(status="passed", typedLiteralPreparationVerified=True, constructorOrderVerified=True)
    except BaseException as error:
        report["error"] = str(error)
        raise
    finally:
        write_json(output / "report.json", report)
    print("Max-base EXP constructor literals and order passed; native graph correspondence and recursive induction remain open.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    check(parser.parse_args())


if __name__ == "__main__":
    main()
