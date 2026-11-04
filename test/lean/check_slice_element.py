#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Capture and check the complete slice-element invocation and its heap frame.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""
import argparse
import copy
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "lean"))
sys.path.insert(0, str(ROOT / "lean/zig_air"))
import environment as lean_check
import prove
from build_toolchain import digest, run, source_identity, write_json
from capture import capture, read_json
from generate import captured_path
from generate_memory import Decoder, generate
from check_zig_air_memory import inspect_memory
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
from zig_slice_element_native import CASES, WORDS

MODULE = "Compiler.ZigAir.MemorySliceAudit"
AIR_ROOT = "zig_air_slice_element.slice_element"
SOURCE = ROOT / "test/lean/zig_air_slice_element.zig"
DIRECTORY = ROOT / "lean/Compiler/ZigAir"
NS = "Compiler.ZigAir.MemorySliceInvocation."
CLAIMS = ["Compiler.ZigAir.Memory." + n for n in (
    "sliceElementPointer_in_bounds", "sliceElementPointer_out_of_bounds", "sliceElementPointer_address",
    "WordArray.slice_element", "WordArray.make_slice", "WordArray.writable_allocate", "WordArray.offset_zero",
    "Cells.write_root", "fresh_store_total", "allocate_fault_of_layout")]
CLAIMS += ["Compiler.ZigAir.MemoryAir.Prim." + n for n in ("eval_slice_element", "eval_slice", "eval_bounds")]
CLAIMS += [NS + n for n in ("generated_body", "run_preserves")]
CLAIMS += [NS + "Tests." + n for n in (
    "valid_caller", *[f"case_{i}" for i in range(len(CASES))], "exact_slice_bound", "empty_slice", "allocation_extent",
    "valid_first_exhausted", "valid_second_exhausted", "first_allocation_exhausted", "second_allocation_exhausted",
    "uninitialized_address", "dead_slice", "oversized_slice", "zero_sized_child", "total_invocation_witness")]


def inputs():
    paths = list((ROOT / "lean").rglob("*.py")) + list((ROOT / "test/lean").rglob("*.py"))
    paths += [SOURCE, ROOT / "lean/zig_air/SemanticExport.zig"]
    return {str(p.relative_to(ROOT)): digest(p) for p in sorted(paths) if ".lake" not in p.parts}


def controls(output, env, lean, generated, record):
    declarations = "import Compiler.ZigAir.MemorySliceElements\nimport Compiler.ZigAir.MemorySlots\nimport Compiler.ZigAir.MemoryFill\n"
    proof = without_imports((DIRECTORY / "MemorySliceInvocation.lean").read_text())
    original = declarations + without_imports(generated) + proof
    result = [mutation_check(output, "invocation-unchanged", original, True, env, lean)]
    before = Decoder(record).program(record)
    for name in ("index-replaced-by-length", "index-replaced-by-zero"):
        replacement = {"kind": "instruction", "index": 1}
        changed = copy.deepcopy(record)
        elements = [i for i in changed["instructions"] if i["tag"] == "slice_elem_ptr"]
        if len(elements) != 1 or generated.count(before) != 1:
            raise ValueError("slice mutation is not bound to the captured root")
        # Reuse the captured zero's complete constant representation.
        if name == "index-replaced-by-zero":
            replacement = copy.deepcopy(next(i["rhs"] for i in changed["instructions"] if i["tag"] == "ptr_add"))
        elements[0]["rhs"] = replacement
        after = Decoder(changed).program(changed)
        if after == before:
            raise ValueError("index mutation did not change generated code")
        write_json(output / (name + ".air.json"), changed)
        result.append(mutation_check(output, name, declarations + without_imports(generated.replace(before, after)) + proof,
                                     False, env, lean))
    memory = (DIRECTORY / "Memory.lean").read_text()
    operation = memory[memory.index("def sliceElementPointer"):memory.index("def makeSlice")]
    laws = (DIRECTORY / "MemorySliceElements.lean").read_text()
    laws = laws[laws.index("theorem sliceElementPointer_in_bounds"):laws.index("namespace WordArray")]
    # Rename the exact implementation and its laws so controls can coexist with
    # the imported memory definitions without altering the production module.
    primitive = "import Compiler.ZigAir.MemoryPointers\nnamespace SliceControl\nopen Compiler.ZigAir.Memory\n"
    primitive += (operation + laws).replace("sliceElementPointer", "checkedElement") + "\nend SliceControl\n"
    result.append(mutation_check(output, "primitive-unchanged", primitive, True, env, lean))
    for name, before, after in (
        ("slice-bound-includes-end", "if index < length then", "if index ≤ length then"),
        ("element-index-shifted", "child) address) index", "child) address) (index + 1)"),
    ):
        if operation.count(before) != 1:
            raise ValueError("ambiguous slice-operation mutation")
        changed = operation.replace(before, after)
        text = "import Compiler.ZigAir.MemoryPointers\nnamespace SliceControl\nopen Compiler.ZigAir.Memory\n"
        text += (changed + laws).replace("sliceElementPointer", "checkedElement") + "\nend SliceControl\n"
        result.append(mutation_check(output, name, text, False, env, lean))
    for r in result:
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant",
                     (output / (r["name"] + ".stdout")).read_text(), re.I):
            raise ValueError("slice control had a resource or syntax failure: " + r["name"])
    return result


def audit(output, env, lean):
    run(output, "audit", [lean, "-DwarningAsError=true", DIRECTORY / "MemorySliceAudit.lean"], cwd=ROOT / "lean", env=env)
    (output / "audit.json").write_bytes((output / "audit.stdout").read_bytes())
    data = read_json(output / "audit.json")
    if data.get("schema") != "oksolc.slice-element-audit.v1" or [c["theorem"] for c in data["claims"]] != CLAIMS:
        raise ValueError("unexpected slice declaration audit")
    for claim in data["claims"]:
        if not set(claim["axioms"]) <= {"propext", "Quot.sound", "Classical.choice"}:
            raise ValueError("unexpected slice axiom")
        if claim["theorem"] == NS + "run_preserves":
            needed = {"Compiler.ZigAir.Memory." + n for n in (
                "State.valid", "WordArray.Writable", "allocate", "store", "fresh_store_total",
                "allocate_fault_of_layout", "cleanup", "cleanup_eq_older", "sliceElementPointer")}
            needed |= {"Compiler.ZigAir.GeneratedMemory.fn_slice_element", "Compiler.ZigAir.MemoryAir.Program.run"}
            if not needed <= set(claim["dependencies"]):
                raise ValueError("complete invocation theorem lost a required effect")
    return {"claims": len(CLAIMS), "sha256": digest(output / "audit.json")}


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.slice-element-acceptance.v1", "status": "failed", "jobs": 4,
              "proofScope": "zigFreshAirTypedHeap", "decodedModes": ["ReleaseFast"],
              "sourceSafetyVerified": False, "decoderVerified": False, "nativeBackendVerified": False,
              "wholeCompilerVerified": False, "byteSwapLoopVerified": False,
              "assumptions": ["valid typed heap", "live writable contained u32 array view", "index below original slice length",
                              "64-bit pointers and usize", "sequential nonvolatile memory"],
              "excluded": ["sentinels", "zero-sized elements", "general byte pointer casts", "noalias and native ABI refinement",
                           "source/frontend/backend preservation"]}
    try:
        report["inputs"], report["leanInputs"] = inputs(), lean_check.source_inputs()
        report["toolchainReportSha256"] = digest(args.toolchain)
        toolchain = read_json(args.toolchain)
        report["toolchainBuildStatus"] = toolchain["status"]
        exporter = [p for p in toolchain["freshAirCapturePatch"] if p["file"] == "src/SemanticExport.zig"]
        if len(exporter) != 1 or exporter[0]["afterSha256"] != digest(ROOT / "lean/zig_air/SemanticExport.zig"):
            raise ValueError("capturing toolchain was built with different exporter bytes")
        env, _, tools = lean_check.toolchain(args.lean_bin, 4)
        run(output, "python-tests", [sys.executable, "-m", "unittest", "discover", "-s", "test/lean", "-p", "test_zig_air_*.py"], cwd=ROOT, env=env)
        run(output, "preflight", [tools["lake"]["path"], "build", MODULE], cwd=ROOT / "lean", env=env)
        report["audit"] = audit(output, env, tools["lean"]["path"])
        captured_dir = output / "capture"
        capture(argparse.Namespace(toolchain=args.toolchain, source=SOURCE, output=captured_dir, root=[AIR_ROOT], mode="ReleaseFast"))
        captured = read_json(captured_dir / "report.json")
        record = read_json(captured_path(captured_dir / "report.json", captured["functions"][AIR_ROOT]))
        if record["configuration"]["arch"] != "aarch64" or record["configuration"]["os"] != "macos":
            raise ValueError("native fixture gate requires aarch64-macos")
        observed = inspect_memory(record)
        if observed.get("slice_elem_ptr") != 1 or observed.get("alloc") != 2:
            raise ValueError("complete slice-element capture changed")
        report["capturedOperations"] = observed
        generated = output / "GeneratedSliceElement.lean"
        report["generation"] = generate(captured_dir / "report.json", [AIR_ROOT], generated, output / "generation.json")
        if generated.read_bytes() != (DIRECTORY / generated.name).read_bytes():
            raise ValueError("captured slice-element code differs from the proved module")
        report["captureReportSha256"] = digest(captured_dir / "report.json")
        negative = output / "controls"
        negative.mkdir()
        report["controls"] = controls(negative, env, tools["lean"]["path"], generated.read_text(), record)
        bindings = "import Compiler.ZigAir.MemorySliceTests\nopen Compiler.ZigAir.MemorySliceInvocation.Tests\n"
        bindings += "open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray\n"
        bindings += "example : words = [" + ", ".join(map(str, WORDS)) + "] := rfl\n"
        for i, (first, length, index) in enumerate(CASES):
            bindings += f"example : observe {first} {length} {index} = (.ok (.pointer (.pointer true false word) ⟨0, {(first + index) * 4}⟩), ⟨caller.heap, 3, 72⟩) := case_{i}\n"
        report["nativeModelBinding"] = mutation_check(negative, "native-model-binding", bindings, True, env, tools["lean"]["path"])
        compiler, lib = Path(toolchain["compiler"]["path"]), Path(toolchain["compiler"]["zigLibDir"])
        run(output, "format", [compiler, "fmt", "--check", SOURCE, ROOT / "lean/zig_air/SemanticExport.zig"], env=env)
        report["modes"] = {}
        for mode in ("Debug", "ReleaseSafe", "ReleaseFast"):
            directory = output / mode
            directory.mkdir()
            library = directory / "slice-element.dylib"
            run(directory, "build", [compiler, "build-lib", SOURCE, "--zig-lib-dir", lib,
                "-dynamic", "-fllvm", "-fno-incremental", "-O" + mode, "-femit-bin=" + str(library),
                "--cache-dir", directory / "cache", "--global-cache-dir", directory / "global-cache"], env=env)
            run(directory, "native", [sys.executable, ROOT / "test/lean/zig_slice_element_native.py", "--library", library,
                "--output", directory / "observations.json"], env=env)
            observations = read_json(directory / "observations.json")
            wanted = [{"first": first, "length": length, "index": index, "before": WORDS, "after": WORDS,
                       "offset": (first + index) * 4} for first, length, index in CASES]
            if observations != {"status": "passed", "cases": wanted}:
                raise ValueError("native/model slice observations differ")
            report["modes"][mode] = {"status": "passed", "cases": len(wanted), "librarySha256": digest(library),
                                     "observationsSha256": digest(directory / "observations.json")}
        proof, artifacts = prove.check_module(MODULE, CLAIMS, lean_bin=args.lean_bin, jobs=4, fresh=True)
        directory = output / "proof"
        directory.mkdir()
        for name, data in artifacts.items():
            (directory / name).write_bytes(data)
        write_json(directory / "report.json", proof)
        report["proofReportSha256"] = digest(directory / "report.json")
        if (proof.get("status") != "passed" or proof.get("freshKernelReplay") is not True or
                proof.get("replayIncludesImports") is not True or proof.get("auditedDeclarations") != CLAIMS):
            raise ValueError("slice-element fresh kernel replay failed")
        if (inputs() != report["inputs"] or lean_check.source_inputs() != report["leanInputs"] or
                digest(args.toolchain) != report["toolchainReportSha256"] or
                digest(compiler) != toolchain["compiler"]["sha256"] or source_identity(lib.parent) != toolchain["sourceTree"]):
            raise ValueError("slice-element acceptance inputs changed")
        report.update(status="passed", auditedDeclarations=len(CLAIMS), universalSliceInvocationVerified=True,
                      callerHeapFrameVerified=True, freshKernelReplay=True)
    finally:
        write_json(output / "report.json", report)
    print("Slice-element invocation acceptance passed; source and native preservation remain open.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    check(parser.parse_args())
