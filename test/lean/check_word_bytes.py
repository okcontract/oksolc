#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Audit initialized u32 byte views over the existing typed heap.
// Copyright (C) 2026 OKcontract Pte. Ltd.

This does not certify Zig pointer-cast decoding, swap loops or the backend.
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
from build_toolchain import REVISION, check_checkout, digest, run, source_identity, write_json
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
from zig_word_bytes_native import CASES, expected

MODULE = "Compiler.ZigAir.MemoryWordBytesTests"
NS = "Compiler.ZigAir.Memory.WordByteView."
CLAIMS = ["Compiler.ZigAir.WordBytes." + n for n in ("read_write_same", "read_write_other", "write_read", "ext")]
CLAIMS += [NS + n for n in ("read_alias", "read_word", "write_word", "write_refines", "write_effect", "read_written")]
TESTS = ["valid_caller", "writable_caller", "represented_caller", "total_write_witness", "uninitialized_read",
         "uninitialized_write", "readonly_read", "readonly_write", "const_pointer_write", "bounds_read",
         "bounds_write", "dead_read", "pointer_bytes_reject", "pointer_byte_write_reject"]
TESTS += [name + "_" + order for order in ("little", "big") for name, *_ in CASES]
CLAIMS += [NS + "Tests." + n for n in TESTS]


def inputs():
    paths = list((ROOT / "lean").rglob("*.py")) + list((ROOT / "test/lean").glob("*.py"))
    paths += [ROOT / "test/lean/zig_word_bytes.zig"]
    return {str(p.relative_to(ROOT)): digest(p) for p in sorted(paths) if ".lake" not in p.parts}


def controls(output, env, lean):
    directory = ROOT / "lean/Compiler/ZigAir"
    codec = "import Compiler.ZigAir.MemoryTypes\n" + without_imports((directory / "WordBytes.lean").read_text())
    codec += '''
open Compiler.ZigAir.WordBytes in
example : read .big 305419896 0 = 18 := by rfl
'''
    memory = "import Compiler.ZigAir.WordBytes\nimport Compiler.ZigAir.MemoryWordFrame\n"
    body = "".join(without_imports((directory / name).read_text())
                   for name in ("MemoryWordByteView.lean", "MemoryWordBytes.lean"))
    # Runtime AIR now imports the original byte-view definitions. Keep the
    # mutation copy independent of those imports while checking the same laws.
    memory += body.replace("Memory.WordByteView", "Memory.WordByteViewControl")
    memory += '''
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordByteViewControl in
example : read .little {} (.pointer (.pointer true false WordArray.word) ⟨0, 0⟩) 0 = .error .unallocated := by rfl
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordByteViewControl in
example : read .little {} (.pointer (.pointer true false WordArray.word) ⟨0, 0⟩) 4 = .error .sourceBounds := by rfl
'''
    result = [mutation_check(output, "codec-unchanged", codec, True, env, lean),
              mutation_check(output, "memory-unchanged", memory, True, env, lean)]
    for name, original, before, after in (
        ("wrong-byte-order", codec, "| .big => 3 - index.val", "| .big => index.val"),
        ("clobbered-lower-bytes", codec, "value.toNat % 256 ^ position +", "0 +"),
        ("wrong-written-byte", codec, "256 ^ position * byte.toNat", "256 ^ position * (byte.toNat + 1)"),
        ("discarded-write", memory,
         "store state pointer (number (WordBytes.write order (BitVec.ofInt 32 value) ⟨offset, inside⟩ byte))", ".ok state"),
        ("missing-read-becomes-zero", memory, "| .error reason => .error reason", "| .error _ => .ok 0"),
        ("bounds-fault-changed", memory, "else .error .sourceBounds", "else .error .unsupported"),
    ):
        # The two last controls intentionally change only the read definition.
        count = original.count(before)
        if count != (2 if name in ("missing-read-becomes-zero", "bounds-fault-changed") else 1):
            raise ValueError("ambiguous byte-view mutation: " + name)
        changed = original.replace(before, after, 1)
        result.append(mutation_check(output, name, changed, False, env, lean))
    for record in result:
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant",
                     (output / (record["name"] + ".stdout")).read_text(), re.I):
            raise ValueError("byte-view control hit a resource or syntax failure: " + record["name"])
    return result


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
  liftIO <| IO.println (Json.mkObj [("claims", .arr claims)]).compress
'''
    (output / "audit.lean").write_text(source)
    run(output, "audit", [lean, "-DwarningAsError=true", output / "audit.lean"], cwd=ROOT / "lean", env=env)
    raw = (output / "audit.stdout").read_bytes()
    (output / "audit.json").write_bytes(raw)
    data = json.loads(raw)
    if [c["theorem"] for c in data["claims"]] != CLAIMS:
        raise ValueError("unexpected byte-view claim list")
    for c in data["claims"]:
        if not set(c["axioms"]) <= {"propext", "Quot.sound", "Classical.choice"}:
            raise ValueError("unexpected byte-view axiom")
        needed = set()
        if c["theorem"] == NS + "write_refines":
            needed = {"Compiler.ZigAir.Memory." + n for n in ("load", "store", "State.valid", "WordArray.Writable",
                      "WordArray.Represents", "WordArray.write_total", "WordArray.Frame", "WordArray.frame_store")}
        elif c["theorem"] == NS + "read_written":
            needed = {"Compiler.ZigAir.WordBytes." + n for n in ("read_write_same", "read_write_other")}
            needed |= {NS + "write_effect", "Compiler.ZigAir.Memory.load_after_store"}
        if not needed <= set(c["dependencies"]):
            raise ValueError("byte-view theorem lost an effect dependency: " + c["theorem"])
    return {"claims": len(CLAIMS), "sha256": digest(output / "audit.json")}


def bindings(output, env, lean):
    source = "import " + MODULE + "\nopen Compiler.ZigAir.Memory.WordByteView.Tests\n"
    for order in ("little", "big"):
        for name, value, index, byte in CASES:
            wanted = expected(order, value, index, byte)
            before = ", ".join(f".ok {n}" for n in wanted["beforeBytes"])
            after = ", ".join(f".ok {n}" for n in wanted["afterBytes"])
            words = ", ".join(f".ok (Compiler.ZigAir.Memory.WordArray.number {n})" for n in wanted["afterWords"])
            source += f"example : observe .{order} {value} {index} {byte} = ⟨[{before}], .ok (), [{words}], [{after}]⟩ := {name}_{order}\n"
    return mutation_check(output, "native-model-binding", source, True, env, lean)


def native(output, zig, tree, env):
    result = {}
    for mode in ("Debug", "ReleaseSafe", "ReleaseFast"):
        directory = output / mode
        directory.mkdir()
        library = directory / "word-bytes.dylib"
        run(directory, "build", [zig, "build-lib", ROOT / "test/lean/zig_word_bytes.zig", "--zig-lib-dir", tree / "lib",
            "-dynamic", "-fllvm", "-fno-incremental", "-O" + mode, "-femit-bin=" + str(library),
            "--cache-dir", directory / "cache", "--global-cache-dir", directory / "global-cache"], env=env)
        run(directory, "native", [sys.executable, ROOT / "test/lean/zig_word_bytes_native.py", "--library", library,
            "--output", directory / "observations.json"], env=env)
        observations = json.loads((directory / "observations.json").read_text())
        order = observations["byteOrder"]
        if order not in ("little", "big") or observations["status"] != "passed":
            raise ValueError("invalid native byte order or result")
        wanted = [{"case": name, "value": value, "index": index, "byte": byte,
                   "expected": expected(order, value, index, byte), "actual": expected(order, value, index, byte)}
                  for name, value, index, byte in CASES]
        if observations["cases"] != wanted:
            raise ValueError("native byte-view observations differ from checked fixtures")
        result[mode] = {"status": "passed", "cases": len(wanted), "byteOrder": order,
                       "librarySha256": digest(library), "observationsSha256": digest(directory / "observations.json")}
    return result


def check(args):
    output, tree, zig = args.output.resolve(), args.zig_tree.resolve(), args.zig.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.word-byte-view-acceptance.v1", "status": "failed", "jobs": 4,
              "proofScope": "typedHeapInitializedU32ByteViews", "freshAirByteCastsVerified": False,
              "byteSwapLoopVerified": False, "nativeBackendVerified": False, "wholeCompilerVerified": False,
              "assumptions": ["explicit target byte order", "initialized u32 objects", "sequential nonvolatile storage",
                              "valid heap, writable live contained array view for totality"],
              "excluded": ["partial word initialization", "padding and pointer bytes", "general pointer casts",
                           "native allocator/pointer correspondence", "frontend/backend preservation"]}
    try:
        check_checkout(output, tree, "zig-before")
        report["zigRevision"], report["zigLibrary"] = REVISION, source_identity(tree / "lib")
        report["pythonInputs"], report["leanInputs"] = inputs(), lean_check.source_inputs()
        report["zig"] = {"path": str(zig), "sha256": digest(zig)}
        env, _, tools = lean_check.toolchain(args.lean_bin, 4)
        run(output, "zig-version", [zig, "version"], env=env)
        if (output / "zig-version.stdout").read_text().strip() != "0.17.0":
            raise ValueError("Zig must be version 0.17.0")
        run(output, "format", [zig, "fmt", "--check", ROOT / "test/lean/zig_word_bytes.zig"], env=env)
        run(output, "preflight", [tools["lake"]["path"], "build", MODULE, "Compiler.Extraction.InsertionSortHeapTests"],
            cwd=ROOT / "lean", env=env)
        # Both clients must coexist: test-local derived instances may otherwise
        # collide despite each root elaborating successfully in isolation.
        combined = output / "combined-imports.lean"
        combined.write_text("import Compiler.Extraction.InsertionSortHeapTests\nimport " + MODULE + "\n")
        run(output, "combined-imports", [tools["lean"]["path"], "-DwarningAsError=true", combined], cwd=ROOT / "lean", env=env)
        report["audit"] = audit(output, env, tools["lean"]["path"])
        report["controls"] = controls(output, env, tools["lean"]["path"])
        report["nativeModelBinding"] = bindings(output, env, tools["lean"]["path"])
        report["modes"] = native(output, zig, tree, env)
        proof, artifacts = prove.check_module(MODULE, CLAIMS, lean_bin=args.lean_bin, jobs=4, fresh=True)
        proof_dir = output / "proof"
        proof_dir.mkdir()
        for name, data in artifacts.items():
            (proof_dir / name).write_bytes(data)
        write_json(proof_dir / "report.json", proof)
        report["proofReportSha256"] = digest(proof_dir / "report.json")
        if (proof.get("status") != "passed" or proof.get("freshKernelReplay") is not True or
                proof.get("replayIncludesImports") is not True or proof.get("auditedDeclarations") != CLAIMS):
            raise ValueError("byte-view proof audit or fresh replay failed")
        if (inputs() != report["pythonInputs"] or lean_check.source_inputs() != report["leanInputs"] or
                source_identity(tree / "lib") != report["zigLibrary"] or digest(zig) != report["zig"]["sha256"]):
            raise ValueError("byte-view acceptance inputs changed")
        check_checkout(output, tree, "zig-after")
        report.update(status="passed", auditedDeclarations=len(CLAIMS), byteViewLawsVerified=True,
                      typedHeapByteEffectsVerified=True)
    finally:
        write_json(output / "report.json", report)
    print("Initialized u32 byte-view acceptance passed; native refinement remains open.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--zig-tree", type=Path, required=True)
    parser.add_argument("--zig", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    check(parser.parse_args())
