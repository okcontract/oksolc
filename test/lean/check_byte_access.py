#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Check byte-address geometry, typed heap refinement and AIR primitive effects.
// Copyright (C) 2026 OKcontract Pte. Ltd.

This gate does not certify a fresh-AIR decoder, the swap loop or native lowering.
"""
import argparse
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
from build_toolchain import REVISION, check_checkout, digest, run, source_identity, write_json
from check_insertion_sort import memory_controls
from check_zig_air_memory_proofs import invariant_controls, without_imports
from check_zig_air_proofs import mutation_check
from zig_word_bytes_native import CASES, expected

DIRECTORY = ROOT / "lean/Compiler/ZigAir"
MODULE = "Compiler.ZigAir.MemoryByteAudit"
NS = "Compiler.ZigAir.Memory.ByteAccess."
LAWS = ["write_store", "number_valid", "number_typed", "wordAddress_atByte", "atByte_lane", "read_atByte",
        "write_atByte", "cast_address", "cast_array", "read_refines", "write_refines", "access_bytes",
        "make_byte_slice", "byte_element", "cast_slice_element", "read_alias"]
TESTS = ["cast_uninitialized", "read_uninitialized", "write_uninitialized", "cast_readonly", "read_readonly",
         "write_readonly", "cast_const_upgrade", "write_const", "cast_alignment_zero", "cast_alignment_three",
         "cast_alignment_eight", "cast_alignment_one", "cast_alignment_two", "cast_unaligned", "cast_dead",
         "cast_outside", "cast_wrong_subobject", "read_byte_array", "read_pointer_bytes", "element_exact_bound",
         "read_last_byte", "read_outside", "write_malformed", "write_negative", "air_cast", "air_load",
         "air_failure_retains_heap", "air_missing_operand"]
TESTS += [name + "_" + order for order in ("little", "big") for name, *_ in CASES]
CLAIMS = [NS + n for n in LAWS] + [NS + "Tests." + n for n in TESTS]
CLAIMS += ["Compiler.ZigAir.MemoryAir.Prim." + n for n in
           ("eval_word_byte_cast", "eval_word_byte_load", "eval_word_byte_store", "preserves_valid", "failure_retains_state")]
CLAIMS += ["Compiler.ZigAir.MemoryAir.Program.preserves_valid", "Compiler.ZigAir.MemorySliceInvocation.run_preserves",
           "Compiler.ZigAir.MemoryExp.exp_safe_terminates", "Compiler.ZigAir.MemoryExp.exp_preserves_caller_heap",
           "Compiler.Extraction.InsertionSort.Heap.run_refines"]


def inputs():
    paths = list((ROOT / "lean").rglob("*.py")) + list((ROOT / "test/lean").glob("*.py"))
    paths += [ROOT / "test/lean/zig_word_bytes.zig"]
    return {str(p.relative_to(ROOT)): digest(p) for p in sorted(paths) if ".lake" not in p.parts}


def controls(output, env, lean):
    prefix = "import Compiler.ZigAir.MemoryBytePointers\n"
    body = "".join(without_imports((DIRECTORY / name).read_text()) for name in
                   ("MemoryByteAccess.lean", "MemoryByteAccessProofs.lean", "MemoryBytePointers.lean"))
    # Original runtime definitions are transitively imported by the proofs.
    # Rename the entire copied namespace, including internal qualified uses.
    original = prefix + body.replace("ByteAccess", "ByteControl")
    original += '''
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.ByteControl in
example : write .little {} (pointer true false ⟨0, 0⟩) (.scalar (.int false 8 256)) = .error .malformed := by rfl
'''
    result = [mutation_check(output, "byte-access-unchanged", original, True, env, lean)]
    for name, before, after in (
        ("wrong-containing-word", "address.offset / 4 * 4", "address.offset / 4 * 8"),
        ("wrong-byte-lane", "(address.offset % 4)", "((address.offset + 1) % 4)"),
        ("cast-upgrades-const", "writable && !sourceWritable", "false"),
        ("cast-wrong-alignment", "if alignment ≠ 1 ∧ alignment ≠ 2 ∧ alignment ≠ 4 then",
         "if alignment ≠ 1 ∧ alignment ≠ 3 ∧ alignment ≠ 4 then"),
        ("cast-discards-subobject", "if !acceptsView cell.type address.offset word then", "if false then"),
        ("cast-rebases-address", ".ok (pointer writable many address)", ".ok (pointer writable many { address with offset := 0 })"),
        ("write-discards-value-check", "if !value.valid then", "if false then"),
    ):
        if original.count(before) != (2 if name == "wrong-byte-lane" else 1):
            raise ValueError("ambiguous byte-access mutation: " + name)
        result.append(mutation_check(output, name, original.replace(before, after, 1), False, env, lean))
    for record in result:
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant",
                     (output / (record["name"] + ".stdout")).read_text(), re.I):
            raise ValueError("byte-access control hit a resource or syntax failure: " + record["name"])
    return result


def audit(output, env, lean):
    run(output, "audit", [lean, "-DwarningAsError=true", DIRECTORY / "MemoryByteAudit.lean"], cwd=ROOT / "lean", env=env)
    raw = (output / "audit.stdout").read_bytes()
    (output / "audit.json").write_bytes(raw)
    data = json.loads(raw)
    if data.get("schema") != "oksolc.byte-access-audit.v1" or [c["theorem"] for c in data["claims"]] != CLAIMS:
        raise ValueError("unexpected byte-access declaration audit")
    for claim in data["claims"]:
        if not set(claim["axioms"]) <= {"propext", "Quot.sound", "Classical.choice"}:
            raise ValueError("unexpected byte-access axiom")
        required = set()
        if claim["theorem"] == NS + "write_refines":
            required = {"Compiler.ZigAir.Memory." + n for n in (
                "ByteAccess.write", "WordByteView.write_refines", "store", "State.valid", "WordArray.Writable",
                "WordArray.Represents", "WordArray.Frame")}
        elif claim["theorem"] == NS + "cast_slice_element":
            required = {"Compiler.ZigAir.Memory." + n for n in (
                "ByteAccess.cast", "access", "acceptsView", "makeSlice", "sliceElementPointer", "WordArray.Writable")}
        elif claim["theorem"] == "Compiler.ZigAir.MemoryAir.Prim.preserves_valid":
            required = {NS + "write_store", "Compiler.ZigAir.Memory.store_preserves_valid"}
        if not required <= set(claim["dependencies"]):
            raise ValueError("byte-access proof lost required effects: " + claim["theorem"])
    return {"claims": len(CLAIMS), "sha256": digest(output / "audit.json")}


def bindings(output, env, lean):
    source = "import Compiler.ZigAir.MemoryByteAccessTests\nopen Compiler.ZigAir.Memory.ByteAccess.Tests\n"
    for order in ("little", "big"):
        for name, value, index, byte in CASES:
            wanted = expected(order, value, index, byte)
            before = ", ".join(f".ok {n}" for n in wanted["beforeBytes"])
            after = ", ".join(f".ok {n}" for n in wanted["afterBytes"])
            words = ", ".join(f".ok (Compiler.ZigAir.Memory.WordArray.number {n})" for n in wanted["afterWords"])
            source += f"example : observe .{order} {value} {index} {byte} = ⟨[{before}], .ok (), [{words}], [{after}]⟩ := {name}_{order}\n"
    return mutation_check(output, "native-model-binding", source, True, env, lean)


def check(args):
    output, tree, zig = args.output.resolve(), args.zig_tree.resolve(), args.zig.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.byte-access-acceptance.v1", "status": "failed", "jobs": 4,
              "proofScope": "typedHeapByteAddressOperations", "freshAirByteCastsVerified": False,
              "byteSwapLoopVerified": False, "nativeBackendVerified": False, "wholeCompilerVerified": False,
              "assumptions": ["explicit target byte order", "initialized u32 objects for reads and writes",
                              "sequential nonvolatile storage", "valid heap and live writable contained array view for totality"],
              "excluded": ["partial word initialization", "padding and pointer bytes", "general pointer casts",
                           "noalias and generic call linking", "native allocator/pointer correspondence", "frontend/backend preservation"]}
    try:
        check_checkout(output, tree, "zig-before")
        report["zigRevision"], report["zigLibrary"] = REVISION, source_identity(tree / "lib")
        report["pythonInputs"], report["leanInputs"] = inputs(), lean_check.source_inputs()
        report["zig"] = {"path": str(zig), "sha256": digest(zig)}
        env, _, tools = lean_check.toolchain(args.lean_bin, 4)
        lean = tools["lean"]["path"]
        run(output, "zig-version", [zig, "version"], env=env)
        if (output / "zig-version.stdout").read_text().strip() != "0.17.0":
            raise ValueError("Zig must be version 0.17.0")
        run(output, "format", [zig, "fmt", "--check", ROOT / "test/lean/zig_word_bytes.zig"], env=env)
        run(output, "preflight", [tools["lake"]["path"], "build", MODULE], cwd=ROOT / "lean", env=env)
        report["audit"] = audit(output, env, lean)
        report["controls"] = {}
        for name, check_controls in (("byte-access", controls), ("word-bytes", check_word_bytes.controls),
                                     ("word-array", memory_controls), ("memory-invariants", invariant_controls)):
            directory = output / name
            directory.mkdir()
            report["controls"][name] = check_controls(directory, env, lean)
        report["nativeModelBinding"] = bindings(output, env, lean)
        report["modes"] = check_word_bytes.native(output, zig, tree, env)
        proof, artifacts = prove.check_module(MODULE, CLAIMS, lean_bin=args.lean_bin, jobs=4, fresh=True)
        proof_dir = output / "proof"
        proof_dir.mkdir()
        for name, data in artifacts.items():
            (proof_dir / name).write_bytes(data)
        write_json(proof_dir / "report.json", proof)
        report["proofReportSha256"] = digest(proof_dir / "report.json")
        if (proof.get("status") != "passed" or proof.get("freshKernelReplay") is not True or
                proof.get("replayIncludesImports") is not True or proof.get("auditedDeclarations") != CLAIMS):
            raise ValueError("byte-access proof audit or fresh replay failed")
        if (inputs() != report["pythonInputs"] or lean_check.source_inputs() != report["leanInputs"] or
                source_identity(tree / "lib") != report["zigLibrary"] or digest(zig) != report["zig"]["sha256"]):
            raise ValueError("byte-access acceptance inputs changed")
        check_checkout(output, tree, "zig-after")
        report.update(status="passed", auditedDeclarations=len(CLAIMS), byteAddressRefinementVerified=True)
    finally:
        write_json(output / "report.json", report)
    print("Byte-address operations acceptance passed; fresh AIR and native preservation remain open.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--zig-tree", type=Path, required=True)
    parser.add_argument("--zig", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    check(parser.parse_args())
