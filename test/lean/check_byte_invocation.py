#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Capture, decode and kernel-check complete u32 byte-access invocations.
// Copyright (C) 2026 OKcontract Pte. Ltd.

Universal invocation refinement requires the stated initialized writable-view
premises. Source safety, decoder correctness and native lowering remain open.
"""
import argparse
import copy
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "lean"))
sys.path.insert(0, str(ROOT / "lean/zig_air"))
import environment as lean_check
import prove
import check_word_bytes
from build_toolchain import digest, run, source_identity, write_json
from capture import capture, read_json
from generate import captured_path
from generate_memory import generate
from generate_byte_memory import ByteDecoder
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
from zig_word_bytes_native import CASES, expected

DIRECTORY = ROOT / "lean/Compiler/ZigAir"
SOURCE = ROOT / "test/lean/zig_word_bytes.zig"
MODULE = "Compiler.ZigAir.MemoryByteInvocationTests"
ROOTS = ["zig_word_bytes.read_word_byte", "zig_word_bytes.write_word_byte"]
NS = "Compiler.ZigAir.MemoryByteInvocation."
CLAIMS = [NS + n for n in ("read_preserves_valid", "write_preserves_valid", "generated_read_body", "generated_write_body",
                           "cast_word", "access_steps", "saved_steps", "read_result", "write_result")]
CLAIMS += ["Compiler.ZigAir.Memory." + n for n in (
    "access_prepend", "load_prepend", "store_prepend", "valid_heap_ids", "Heap.replace_absent", "saved_slot_prefix",
    "cleanup_initial", "cleanup_prepend", "WordArray.writable_heap_eq", "WordArray.represents_heap_eq",
    "ByteAccess.read_prepend", "ByteAccess.write_prepend")]
CLAIMS += [NS + "Tests." + n for n in (
    "read_uninitialized", "write_uninitialized", "readonly_read", "readonly_write", "read_exact_bound", "write_exact_bound",
    "valid_exhausted", "read_allocation_exhausted", "write_allocation_exhausted", "dead_read", "dead_write", "const_write_argument",
    "read_total_witness", "write_total_witness")]
CLAIMS += [NS + "Tests." + name for name, *_ in CASES]


def inputs():
    paths = list((ROOT / "lean").rglob("*.py")) + list((ROOT / "test/lean").glob("*.py"))
    paths += [SOURCE, ROOT / "lean/zig_air/SemanticExport.zig"]
    return {str(p.relative_to(ROOT)): digest(p) for p in sorted(paths) if ".lake" not in p.parts}


def audit(output, env, lean):
    source = "import " + MODULE + '''
import Contract.Check.Declarations
import Lean.Elab.Command
open Lean Elab Command Contract.Check in
run_cmd do
  let mut claims := #[]
  for root in #[
''' + ",\n".join("    ``" + name for name in CLAIMS) + '''] do
    let .ok dependencies := Declarations.closure (← getEnv) #[root] | throwError "invalid closure: {root}"
    let .ok axioms := Declarations.axioms dependencies | throwError "disallowed axiom: {root}"
    let some info := (← getEnv).find? root | throwError "missing theorem: {root}"
    unless info matches .thmInfo _ do throwError "not a theorem: {root}"
    claims := claims.push <| Json.mkObj [
      ("theorem", .str root.toString), ("statement", Declarations.expression info.type),
      ("axioms", toJson axioms), ("dependencies", toJson (dependencies.map (·.name.toString)))]
  liftIO <| IO.println (Json.mkObj [("claims", .arr claims)]).pretty
'''
    (output / "audit.lean").write_text(source)
    run(output, "audit", [lean, "-DwarningAsError=true", output / "audit.lean"], cwd=ROOT / "lean", env=env)
    raw = (output / "audit.stdout").read_bytes()
    (output / "audit.json").write_bytes(raw)
    data = json.loads(raw)
    if [c["theorem"] for c in data["claims"]] != CLAIMS:
        raise ValueError("unexpected byte invocation claims")
    for c in data["claims"]:
        if not set(c["axioms"]) <= {"propext", "Quot.sound", "Classical.choice"}:
            raise ValueError("unexpected byte invocation axiom")
        if c["theorem"] in (NS + "read_preserves_valid", NS + "write_preserves_valid") or c["theorem"].startswith(NS + "Tests.case_"):
            required = {"Compiler.ZigAir.MemoryAir.Program.run", "Compiler.ZigAir.Memory.ByteAccess.cast"}
            if c["theorem"] != NS + "read_preserves_valid":
                required |= {"Compiler.ZigAir.Memory.ByteAccess.write", "Compiler.ZigAir.GeneratedMemory.fn_write_word_byte"}
            if c["theorem"] != NS + "write_preserves_valid":
                required |= {"Compiler.ZigAir.Memory.ByteAccess.read", "Compiler.ZigAir.GeneratedMemory.fn_read_word_byte"}
            if not required <= set(c["dependencies"]):
                raise ValueError("byte invocation lost a captured effect dependency")
    requirements = {
        NS + "read_result": {"State.valid", "WordArray.Writable", "WordArray.Represents", "ByteAccess.read_refines",
                            "allocate_fault_of_layout", "fresh_store_total", "saved_slot_prefix", "ByteAccess.read_prepend", "cleanup_prepend"},
        NS + "write_result": {"State.valid", "WordArray.Writable", "WordArray.Represents", "ByteAccess.write_refines", "WordArray.Frame",
                             "allocate_fault_of_layout", "fresh_store_total", "saved_slot_prefix", "ByteAccess.write_prepend", "cleanup_prepend"}}
    for c in data["claims"]:
        if c["theorem"] in requirements:
            required = {"Compiler.ZigAir.Memory." + name for name in requirements[c["theorem"]]}
            required.add("Compiler.ZigAir.MemoryAir.Program.run")
            operation = "read" if c["theorem"] == NS + "read_result" else "write"
            required |= {"Compiler.ZigAir.GeneratedMemory.fn_" + operation + "_word_byte",
                         NS + "generated_" + operation + "_body"}
            if not required <= set(c["dependencies"]):
                raise ValueError("universal invocation lost its memory premises or effects")
    return {"claims": len(CLAIMS), "sha256": digest(output / "audit.json")}


def controls(output, env, lean, generated, records):
    prefix = "import Compiler.ZigAir.MemoryByteAccessTests\n"
    client = '''
open Compiler.ZigAir.Memory Compiler.ZigAir.GeneratedMemory in
example : fn_read_word_byte.run [.pointer (.pointer false false WordArray.word) ⟨0, 4⟩, .scalar (.int false 64 1)]
    (WordByteView.Tests.caller 305419896) =
      (.ok (ByteAccess.number 86), ⟨(WordByteView.Tests.caller 305419896).heap, 2, 48⟩) := by decide +kernel
open Compiler.ZigAir.Memory Compiler.ZigAir.GeneratedMemory in
example : fn_write_word_byte.run
    [.pointer (.pointer true false WordArray.word) ⟨0, 4⟩, .scalar (.int false 64 1), ByteAccess.number 255]
    (WordByteView.Tests.caller 0) = (.ok (.scalar .unit),
      ⟨[(0, { WordByteView.Tests.cell 65280 with cells :=
        [(4, WordArray.number 65280), (0, WordArray.number 3735928559), (8, WordArray.number 3131961357)] })], 2, 48⟩) := by decide +kernel
'''
    proof = without_imports((DIRECTORY / "MemoryByteInvocation.lean").read_text())
    prefix += "import Compiler.ZigAir.MemoryStackPrefix\nimport Compiler.ZigAir.MemoryFill\n"
    original = prefix + without_imports(generated) + proof
    result = [mutation_check(output, "invocation-unchanged", original, True, env, lean),
              mutation_check(output, "closed-effects-unchanged", prefix + without_imports(generated) + client, True, env, lean)]
    for name, root, tag in (("read-wrong-index", ROOTS[0], "slice_elem_ptr"),
                            ("write-wrong-index", ROOTS[1], "slice_elem_ptr"),
                            ("write-wrong-byte", ROOTS[1], "store")):
        record = records[root]
        changed = copy.deepcopy(record)
        sites = [i for i in changed["instructions"] if i["tag"] == tag and i.get("payloadVisited") is True]
        # The second store is the byte effect; the first saves the local slice.
        site = sites[-1]
        if len(sites) != (2 if tag == "store" else 1):
            raise ValueError("byte invocation mutation site changed")
        width = 8 if tag == "store" else 64
        site["rhs"] = {"kind": "constant", "type": {"kind": "int", "bits": width, "signedness": "unsigned"}, "value": 0}
        before, after = ByteDecoder(record).program(record), ByteDecoder(changed).program(changed)
        if generated.count(before) != 1 or before == after:
            raise ValueError("byte invocation mutation lost its source binding")
        write_json(output / (name + ".air.json"), changed)
        result.append(mutation_check(output, name, prefix + without_imports(generated.replace(before, after)) + proof, False, env, lean))
    before = ".wordByteLoad .little"
    if generated.count(before) != 1:
        raise ValueError("byte order mutation is ambiguous")
    result.append(mutation_check(output, "read-wrong-byte-order",
                                 prefix + without_imports(generated.replace(before, ".wordByteLoad .big")) + proof, False, env, lean))
    framing = "import Compiler.ZigAir.MemorySlots\nimport Compiler.ZigAir.MemoryByteAccessProofs\n"
    framing += without_imports((DIRECTORY / "MemoryStackPrefix.lean").read_text())
    result.append(mutation_check(output, "stack-prefix-unchanged", framing, True, env, lean))
    for name, before, after in (
            ("stack-prefix-drops-caller", "(id, cell) :: state.heap", "(id, cell) :: state.heap.drop 1"),
            ("cleanup-wrong-watermark", "cleanup state.nextId (prepend state.nextId cell", "cleanup 0 (prepend state.nextId cell")):
        if framing.count(before) != 1:
            raise ValueError("stack framing mutation is ambiguous")
        result.append(mutation_check(output, name, framing.replace(before, after), False, env, lean))
    for c in result:
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant",
                     (output / (c["name"] + ".stdout")).read_text(), re.I):
            raise ValueError("invocation control hit a resource or syntax failure")
    return result


def bindings(output, env, lean):
    source = "import " + MODULE + "\nopen Compiler.ZigAir.MemoryByteInvocation.Tests\n"
    for name, value, index, byte in CASES:
        wanted = expected("little", value, index, byte)
        before = ", ".join(f".ok {n}" for n in wanted["beforeBytes"])
        after = ", ".join(f".ok {n}" for n in wanted["afterBytes"])
        words = ", ".join(f".ok (Compiler.ZigAir.Memory.WordArray.number {n})" for n in wanted["afterWords"])
        source += f"example : (observe {value} {index} {byte}).bytes = ⟨[{before}], .ok (), [{words}], [{after}]⟩ := congrArg Observation.bytes {name}\n"
    return mutation_check(output, "native-model-binding", source, True, env, lean)


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.byte-invocation-acceptance.v1", "status": "failed", "jobs": 4,
              "proofScope": "zigFreshAirTypedHeap", "decodedModes": ["ReleaseFast"], "sourceSafetyVerified": False,
              "decoderVerified": False, "nativeBackendVerified": False, "wholeCompilerVerified": False,
              "universalInvocationRefinementVerified": False, "byteSwapLoopVerified": False,
              "assumptions": ["aarch64-macos little-endian ABI", "initialized u32 representations for byte effects",
                              "sequential nonvolatile memory", "valid heap and live writable contained u32 view",
                              "initialized represented words", "word index inside the view and byte index below four"],
              "excluded": ["generic and noalias contracts", "byte-view escapes and control joins",
                           "pointer-bearing input metadata", "general pointer casts", "source/frontend/backend preservation"]}
    try:
        report["inputs"], report["leanInputs"] = inputs(), lean_check.source_inputs()
        report["toolchainReportSha256"] = digest(args.toolchain)
        toolchain = read_json(args.toolchain)
        report["toolchainBuildStatus"] = toolchain["status"]
        exporter = [p for p in toolchain["freshAirCapturePatch"] if p["file"] == "src/SemanticExport.zig"]
        if len(exporter) != 1 or exporter[0]["afterSha256"] != digest(ROOT / "lean/zig_air/SemanticExport.zig"):
            raise ValueError("capturing toolchain has different exporter bytes")
        env, _, tools = lean_check.toolchain(args.lean_bin, 4)
        lean = tools["lean"]["path"]
        run(output, "python-tests", [sys.executable, "-m", "unittest", "discover", "-s", "test/lean", "-p", "test_zig_air_*.py"], cwd=ROOT, env=env)
        run(output, "preflight", [tools["lake"]["path"], "build", MODULE], cwd=ROOT / "lean", env=env)
        report["audit"] = audit(output, env, lean)
        capture(argparse.Namespace(toolchain=args.toolchain, source=SOURCE, output=output / "capture", root=ROOTS, mode="ReleaseFast"))
        capture_path = output / "capture/report.json"
        captured = read_json(capture_path)
        records = {root: read_json(captured_path(capture_path, captured["functions"][root])) for root in ROOTS}
        generated = output / "GeneratedWordByteAccess.lean"
        report["generation"] = generate(capture_path, ROOTS, generated, output / "generation.json", word_bytes=True)
        if generated.read_bytes() != (DIRECTORY / generated.name).read_bytes():
            raise ValueError("fresh captured byte invocations differ from the proved module")
        report["captureReportSha256"] = digest(capture_path)
        directory = output / "controls"
        directory.mkdir()
        report["controls"] = controls(directory, env, lean, generated.read_text(), records)
        report["nativeModelBinding"] = bindings(directory, env, lean)
        compiler, lib = Path(toolchain["compiler"]["path"]), Path(toolchain["compiler"]["zigLibDir"])
        report["modes"] = check_word_bytes.native(output, compiler, lib.parent, env)
        if any(mode["byteOrder"] != "little" for mode in report["modes"].values()):
            raise ValueError("native observations disagree with the captured target byte order")
        proof, artifacts = prove.check_module(MODULE, CLAIMS, lean_bin=args.lean_bin, jobs=4, fresh=True)
        directory = output / "proof"
        directory.mkdir()
        for name, data in artifacts.items():
            (directory / name).write_bytes(data)
        write_json(directory / "report.json", proof)
        report["proofReportSha256"] = digest(directory / "report.json")
        if (proof.get("status") != "passed" or proof.get("freshKernelReplay") is not True or
                proof.get("replayIncludesImports") is not True or proof.get("auditedDeclarations") != CLAIMS):
            raise ValueError("byte invocation fresh kernel replay failed")
        if (inputs() != report["inputs"] or lean_check.source_inputs() != report["leanInputs"] or
                digest(args.toolchain) != report["toolchainReportSha256"] or digest(compiler) != toolchain["compiler"]["sha256"] or
                source_identity(lib.parent) != toolchain["sourceTree"]):
            raise ValueError("byte invocation acceptance inputs changed")
        report.update(status="passed", auditedDeclarations=len(CLAIMS), byteViewDecodingChecked=True,
                      capturedInvocationHeapValidityVerified=True, closedInvocationEffectsVerified=True,
                      universalInvocationRefinementVerified=True, invocationCallerFrameVerified=True)
    finally:
        write_json(output / "report.json", report)
    print("Captured byte invocation functional/frame proofs passed; source and native refinement remain open.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    check(parser.parse_args())
