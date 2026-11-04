#!/usr/bin/env python3
"""Check named-local initialization and overwrite without assuming graph refinement.
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
import extract_local_arguments as admission
import prove
import check_word_swap
import constructor_frame_checks
from check_temporary_arguments import python_inputs, SOURCES as ALGEBRAIC_SOURCES
from constructor_array_checks import local_inventory
from build_toolchain import digest, run, write_json
from capture import capture, read_json, source_files
from generate import captured_path
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

SOURCE = ROOT / "test/lean/constructor_local.zig"
SOURCES = [Path("src/libevmasm/rule_list.zig"), *ALGEBRAIC_SOURCES]
MODULE = "Compiler.Extraction.InternerLocalArgumentsTests"
NS = "Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.LocalArguments."
CLAIMS = [NS + name for name in (
    "readId_of_load", "initPair_of_success", "initPair_of_error", "copy_of_reads", "copy_first_error", "copy_second_error", "copy_verified",
    "overwrite_of_store", "overwrite_verified", "first_error", "after_copy", "prepare_verified",
    "invoke_preparation_error", "invoke_verified")]
CLAIMS += [NS + "Tests." + name for name in (
    "source_represented", "copied_offset_words", "good_and_writable_are_derived", "original_borrow_preserved",
    "false_flag_skips_overwrite", "overwrite_first_slot", "overwrite_second_slot", "optional_store_preserves_borrow_and_identity",
    "aggregate_rejection_has_no_prefix", "rejected_second_load_keeps_allocation", "missing_source_keeps_allocation",
    "length_guard_precedes_allocation", "invalid_overwrite_keeps_initialized_copy", "stack_limit_precedes_load",
    "older_stack_borrow_survives_copy", "stale_local_cannot_alias_new_lifetime", "ordinary_success_unwinds_local",
    "ordinary_oom_unwinds_local", "nonvacuous_constructor_contract")]
CLAIMS += [NS.rsplit("LocalArguments.", 1)[0] + "TemporaryArguments.prepare_with_writable"]


def audit(output, env, lean):
    result = check_word_swap.audit(output, env, lean, MODULE, CLAIMS)
    claims = {record["theorem"]: set(record["dependencies"]) for record in read_json(output / "audit.json")["claims"]}
    memory = "Compiler.ZigAir.Memory."
    normal = "Compiler.Extraction.Memory.Arguments.Normalization."
    requirements = {
        NS + "copy_verified": {NS + "copy_of_reads", normal + "caller_buffer",
            normal + "OwnedCall.TemporaryArguments.prepare_with_writable", memory + "allocate",
            memory + "WordArray.write_total", memory + "store_preserves_valid"},
        NS + "prepare_verified": {NS + "copy_verified", NS + "overwrite_verified",
            memory + "WordArray.write_total", memory + "WordArray.write_allocation_frame"},
        NS + "invoke_verified": {NS + "prepare_verified", normal + "OwnedCall.TemporaryArguments.unwind_verified",
            normal + "OwnedCall.ConstructorFrame.operation_verified"},
        NS + "Tests.good_and_writable_are_derived": {NS + "copy_verified"},
        NS + "Tests.nonvacuous_constructor_contract": {NS + "invoke_verified"},
    }
    for name, required in requirements.items():
        if not required <= claims[name]:
            raise ValueError("named local proof lost dependencies: " + name + ": " + ", ".join(sorted(required - claims[name])))
    return {**result, "checkedDependencies": sorted(requirements)}


def controls(output, env, lean):
    directory = ROOT / "lean/Compiler/Extraction"
    model = without_imports((directory / "InternerLocalArguments.lean").read_text())
    program = without_imports(admission.OUTPUT.read_text())
    proofs = without_imports((directory / "InternerLocalArgumentsProofs.lean").read_text())
    tests = without_imports((directory / "InternerLocalArgumentsTests.lean").read_text())
    imports = "import Compiler.Extraction.InternerTemporaryArguments\nimport Compiler.ZigAir.MemoryWordCopy\nimport Compiler.Extraction.InternerConstructorFrameTests\n"
    records = [mutation_check(output, "local-complete-unchanged", imports + model + program + proofs + tests, True, env, lean)]
    observed = re.sub(r"\ntheorem [\s\S]*?(?=\n(?:private def |def |theorem |end ))", "", model)
    fixtures = tests[:tests.index("\ndef semanticCaller")]
    fixtures = re.sub(r"\ntheorem [\s\S]*?(?=\n(?:def |theorem |end ))", "", fixtures + "\nend ")[:-5]
    # Diagnostic subsets do not replace the complete proof or fresh replay.
    # Closed scalar observations keep proof-rejection diagnostics bounded.
    fixtures += """
example : Compiler.ZigAir.Memory.load copied.memory.memory (target.pointer 0) = .ok (number 1) := by rfl'
example : Compiler.ZigAir.Memory.load copied.memory.memory (target.pointer 1) = .ok (number 2) := by rfl'
example : Compiler.ZigAir.Memory.load (overwritten 0).memory.memory (target.pointer 0) = .ok (number 99) := by rfl'
example : Compiler.ZigAir.Memory.load (overwritten 1).memory.memory (target.pointer 1) = .ok (number 99) := by rfl'
example : Compiler.ZigAir.Memory.load (zigLocal source 1 99 false Semantic.Tests.caller).2.memory.memory
    (target.pointer 1) = .ok (number 2) := by rfl'
example : secondLoadRejected.2.memory.memory.nextId = 4 := by rfl'
example : Compiler.ZigAir.Memory.load secondLoadRejected.2.memory.memory (target.pointer 0) = .error .uninitialized := by rfl'
example : Compiler.ZigAir.Memory.load (initPair target 99 1 short).2.memory.memory (target.pointer 0) = .error .uninitialized := by rfl'
example : (copy ⟨99, 0, 2⟩ Semantic.Tests.caller).2.memory.memory.nextId = 4 := by rfl'
"""
    fixtures += "\nend Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.LocalArguments.Tests\n"
    diagnostics = imports + "set_option pp.maxSteps 8\nset_option pp.deepTerms false\nset_option pp.notation false\n"
    records.append(mutation_check(output, "local-observations-unchanged", diagnostics + observed + program + fixtures, True, env, lean))
    original_copy = observed[observed.index("def copy "):observed.index("def overwrite ")]
    delayed_copy = """def copy (source : View) : GraphAction σ View := fun before =>
  if source.length != 2 then (.error (.memory (.preparation (.memory .sourceBounds))), before) else
  match readId before.memory.memory source 0 with
  | .error fault => (.error (.memory (.preparation (.memory fault))), before)
  | .ok left => match readId before.memory.memory source 1 with
    | .error fault => (.error (.memory (.preparation (.memory fault))), before)
    | .ok right => match Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) with
      | .error fault => (.error (.memory (.preparation (.memory fault))), before)
      | .ok (_, memory) => initPair ⟨before.memory.memory.nextId, 0, 2⟩ left right
          { before with memory := { before.memory with memory } }

"""
    for name, layer, before, after in (
        ("allocation-after-loads", "model", original_copy, delayed_copy),
        ("wrong-first-source-index", "model", "match readId memory source 0 with", "match readId memory source 1 with"),
        ("manufactured-second-word", "model", "| .ok right => initPair target left right allocated",
            "| .ok _right => initPair target left (left + 2) allocated"),
        ("exposed-aggregate-prefix", "model", "commitPair before (TemporaryArguments.writePair target left right before)",
            "TemporaryArguments.writePair target left right before"),
        ("wrong-overwrite-slot", "program", "overwrite target selected repeated initialized", "overwrite target (1 - selected) repeated initialized"),
        ("unconditional-overwrite", "program", "if repeatedIsFirst then overwrite", "if repeatedIsFirst || true then overwrite"),
        ("discard-allocated-error-state", "program", "| (.error fault, reached) => (.error fault, reached)",
            "| (.error fault, _reached) => (.error fault, before)"),
    ):
        target = observed if layer == "model" else program
        if target.count(before) != 1:
            raise ValueError("ambiguous named local semantic control: " + name)
        changed = target.replace(before, after)
        records.append(mutation_check(output, "local-" + name,
            diagnostics + (changed if layer == "model" else observed) + (changed if layer == "program" else program) + fixtures,
            False, env, lean))
    for record in records:
        text = (output / (record["name"] + ".stdout")).read_text()
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant", text, re.I):
            raise ValueError("named local control hit a resource or syntax failure: " + record["name"])
    return records


class Observation(ctypes.Structure):
    _fields_ = [(name, ctypes.c_uint32) for name in (
        "repeated", "repeated_is_first", "matches_first", "matches_second", "found", "fail_operation",
        "result_id", "operation_calls", "constant_calls", "returned_error", "opcode", "first", "second")]
    _fields_ += [(name, ctypes.c_size_t) for name in (
        "borrowed_length", "length", "pointer", "borrowed_pointer", "alignment")]
    _fields_ += [("borrowed", ctypes.c_uint32 * 4)]


def native_cases(output, library):
    native = ctypes.CDLL(str(library))
    function = native.local_operands
    function.argtypes = [ctypes.POINTER(Observation), ctypes.c_uint32]
    function.restype = ctypes.c_uint32
    cases, sentinel = [], 0xA5A5A5A5
    for use_or in (0, 1):
        for left, right, repeated, result_id in ((3, 1, 99, 42), (0, 0xFFFFFFFF, 0xFFFFFE, 0), (256, 255, 0xFFFFFFFF, 0xFFFFFFFF)):
            for repeated_is_first in (0, 1):
                for matches_first, matches_second in ((0, 0), (1, 0), (0, 1), (1, 1)):
                    for found, length in ((0, 2), (1, 0), (1, 1), (1, 2), (1, 3)):
                        for fail_operation in (0, 1):
                            observed = Observation(repeated, repeated_is_first, matches_first, matches_second,
                                found, fail_operation, result_id, 0, 0, 0, sentinel, sentinel, sentinel,
                                length, sentinel, sentinel, sentinel, sentinel,
                                (ctypes.c_uint32 * 4)(sentinel, left, right, sentinel))
                            initial = {name: getattr(observed, name) for name, _ in Observation._fields_ if name != "borrowed"}
                            initial["borrowed"] = list(observed.borrowed)
                            returned = function(ctypes.byref(observed), use_or)
                            actual = {name: getattr(observed, name) for name, _ in Observation._fields_ if name != "borrowed"}
                            raw_pointers = {name: actual[name] for name in ("pointer", "borrowed_pointer")}
                            actual["borrowed"], actual["returned"] = list(observed.borrowed), returned
                            matched = bool(found and length == 2 and (matches_first or matches_second))
                            expected = {**initial, "returned": result_id if matched and not fail_operation else 0}
                            if matched:
                                slot = 1 if matches_second else 0
                                operands = [left, right]
                                if repeated_is_first:
                                    operands[slot] = repeated
                                actual["pointer"] = "separate-aligned-local" if actual["pointer"] > 0 and actual["pointer"] != actual["borrowed_pointer"] else "invalid-local"
                                actual["borrowed_pointer"] = "nonzero" if actual["borrowed_pointer"] > 0 else "zero"
                                expected.update(operation_calls=1, opcode=23 if use_or else 22, first=operands[0], second=operands[1],
                                    length=2, pointer="separate-aligned-local", borrowed_pointer="nonzero", alignment=0,
                                    returned_error=int(bool(fail_operation)))
                            cases.append({"inputs": {"useOr": use_or, **initial}, "rawPointers": raw_pointers,
                                "actual": actual, "expected": expected})
    path = output / "native-observations.json"
    write_json(path, {"schema": "oksolc.named-local-native-controls.v1", "cases": cases,
        "librarySha256": digest(library), "nativeGraphCorrespondenceVerified": False})
    if any(case["actual"] != case["expected"] for case in cases):
        raise ValueError("native named-local initializer/overwrite observation mismatch")
    return {"cases": len(cases), "sha256": digest(path), "librarySha256": digest(library)}


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.named-local-arguments.v1", "status": "failed", "jobs": 4,
        "scope": "dropRepeatedNested named-array initializer, optional overwrite and conditional constructor handoff",
        "typedLocalInitializationVerified": False, "preparedConstructorInputVerified": False,
        "ordinaryLocalCleanupVerified": False, "completeRecursiveConstructorsVerified": False,
        "completeHelperNativeCorrespondenceVerified": False, "nativeGraphCorrespondenceVerified": False,
        "airControlSemanticsVerified": False, "nativeBackendVerified": False, "wholeCompilerVerified": False}
    try:
        report["pythonInputs"], report["leanInputs"] = python_inputs(), lean_check.source_inputs()
        report["admission"], report["inventory"] = admission.check(), constructor_inventory.check()
        report["constructorBinding"] = constructor_frame_checks.bindings()
        sources = source_files(SOURCE, SOURCES)
        env, _, tools = lean_check.toolchain(args.lean_bin, 4)
        report["tools"] = tools
        run(output, "python-preflight", [sys.executable, "-m", "unittest", "discover", "-s", "test/lean", "-p", "test_local_arguments.py"], cwd=ROOT)
        run(output, "cached-proof-preflight", [tools["lake"]["path"], "build", MODULE], cwd=ROOT / "lean", env=env)
        report["audit"], report["controls"] = audit(output, env, tools["lean"]["path"]), controls(output, env, tools["lean"]["path"])
        toolchain = read_json(args.toolchain)
        compiler, lib = Path(toolchain["compiler"]["path"]), Path(toolchain["compiler"]["zigLibDir"])
        if (toolchain["compiler"]["version"] != "0.17.0" or digest(compiler) != toolchain["compiler"]["sha256"] or
                digest(lib.parent / "src/SemanticExport.zig") != digest(ROOT / "lean/zig_air/SemanticExport.zig")):
            raise ValueError("native toolchain does not use the pinned compiler and current exporter")
        report["toolchainReportSha256"], report["native"] = digest(args.toolchain), {}
        report["initializerCompilerSources"] = {name: digest(lib.parent / name) for name in ("lib/std/zig/AstGen.zig", "src/Sema.zig")}
        for mode in ("ReleaseFast", "Debug", "ReleaseSafe"):
            directory = output / mode
            capture(argparse.Namespace(toolchain=args.toolchain, source=SOURCE, source_file=SOURCES, output=directory,
                root=["constructor_local.local_operands"], mode=mode))
            captured = read_json(directory / "report.json")
            helpers = {name: entry for name, entry in captured["functions"].items()
                       if name.startswith("src.libevmasm.rule_list.dropRepeatedNested__")}
            if len(helpers) != 1:
                raise ValueError("native named-array helper capture is absent or ambiguous")
            command = read_json(directory / "ordinary.process.json")["command"]
            command[command.index("build-obj")] = "build-lib"
            command.append("-dynamic")
            library = directory / "local.dylib"
            command[command.index("--cache-dir") + 1] = str(directory / "native-cache")
            command = ["-femit-bin=" + str(library) if item.startswith("-femit-bin=") else item for item in command]
            run(directory, "native-build", command)
            observed = native_cases(directory, library)
            report["native"][mode] = {**observed, "captureReportSha256": digest(directory / "report.json"),
                "objects": captured["objects"], "sourceFiles": captured["sourceFiles"],
                "arrayInventory": {name: local_inventory(captured_path(directory / "report.json", entry))
                                   for name, entry in helpers.items()}}
        proof, artifacts = prove.check_module(MODULE, CLAIMS, lean_bin=args.lean_bin, jobs=4, fresh=True)
        directory = output / "proof"
        directory.mkdir()
        for name, data in artifacts.items():
            (directory / name).write_bytes(data)
        write_json(directory / "report.json", proof)
        report["proofReportSha256"] = digest(directory / "report.json")
        if (proof.get("status") != "passed" or proof.get("freshKernelReplay") is not True or
                proof.get("replayIncludesImports") is not True or proof.get("auditedDeclarations") != CLAIMS):
            raise ValueError("named local proof or fresh imported-kernel replay failed")
        if (python_inputs() != report["pythonInputs"] or lean_check.source_inputs() != report["leanInputs"] or
                source_files(SOURCE, SOURCES) != sources or admission.check() != report["admission"] or
                digest(args.toolchain) != report["toolchainReportSha256"] or
                digest(compiler) != toolchain["compiler"]["sha256"] or
                {name: digest(lib.parent / name) for name in report["initializerCompilerSources"]} != report["initializerCompilerSources"]):
            raise ValueError("named local acceptance inputs changed")
        report.update(status="passed", typedLocalInitializationVerified=True,
            preparedConstructorInputVerified=True, ordinaryLocalCleanupVerified=True)
    except BaseException as error:
        report["error"] = str(error)
        raise
    finally:
        write_json(output / "report.json", report)
    print("Named local preparation and constructor inputs passed; native query correspondence and recursive induction remain open.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    check(parser.parse_args())


if __name__ == "__main__":
    main()
