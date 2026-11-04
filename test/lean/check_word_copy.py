#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Audit typed u32 copying, including readonly sources and uninitialized targets.
// Copyright (C) 2026 OKcontract Pte. Ltd.

This specifies the normalization memcpy boundary; it does not verify captured
memcpy AIR, native copy lowering or the allocator that supplies the destination.
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
from build_toolchain import digest, run, write_json
from check_word_swap import audit
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

MODULE = "Compiler.ZigAir.MemoryWordCopyTests"
NS = "Compiler.ZigAir.Memory.WordCopy."
CLAIMS = [NS + n for n in ("load_readonly", "copyFrom_step", "disjoint_offsets", "source_after_store", "prefix_after_store",
    "copyFrom_refines", "copy_refines", "unequal_lengths_reject", "overlap_rejects")]
CLAIMS += [NS + "Tests." + n for n in ("valid_caller", "writable_target", "represented_source", "target_uninitialized",
    "readonly_source", "copies_readonly_into_uninitialized", "source_and_sentinels_preserved", "counters_preserved",
    "total_witness", "empty_skips_accesses", "unequal_lengths", "aliases_rejected", "partial_overlap_rejected",
    "same_allocation_disjoint", "incomplete_source_valid", "uninitialized_retains_prefix", "prefix_not_zero_filled",
    "readonly_target_rejected", "dead_source_rejected", "dead_target_rejected", "outside_target_rejected")]


def inputs():
    paths = list((ROOT / "lean").rglob("*.py")) + list((ROOT / "test/lean").glob("*.py"))
    return {str(p.relative_to(ROOT)): digest(p) for p in sorted(paths) if ".lake" not in p.parts}


def controls(output, env, lean):
    directory = ROOT / "lean/Compiler/ZigAir"
    source = "import Compiler.ZigAir.MemoryWordFrame\n" + "".join(
        without_imports((directory / name).read_text()) for name in
        ("MemoryWordCopy.lean", "MemoryWordCopyProofs.lean", "MemoryWordCopyTests.lean"))
    records = [mutation_check(output, "copy-unchanged", source, True, env, lean)]
    for name, before, after in (
        ("lost-write", "copyFrom source target remaining (index + 1) middle\n    else", "copyFrom source target remaining (index + 1) state\n    else"),
        ("wrong-word", "match store state (target.pointer index) value with", "match store state (target.pointer index) (number 0) with"),
        ("wrong-source-index", "match load state (readPointer source index) with", "match load state (readPointer source (index + 1)) with"),
        ("skipped-last-word", "else copyFrom source target source.length 0 state", "else copyFrom source target (source.length - 1) 0 state"),
        ("accepted-overlap", "else if !disjoint source target then", "else if false then"),
        ("accepted-length-mismatch", "if source.length ≠ target.length then", "if false then"),
        ("failed-read-is-success", "| .error fault => (.error fault, state)\n      | .ok value", "| .error _ => (.ok (), state)\n      | .ok value"),
    ):
        if source.count(before) != 1:
            raise ValueError("ambiguous copy mutation: " + name)
        records.append(mutation_check(output, name, source.replace(before, after), False, env, lean))
    for record in records:
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant",
                     (output / (record["name"] + ".stdout")).read_text(), re.I):
            raise ValueError("copy control hit a resource or syntax failure: " + record["name"])
    return records


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.word-copy-acceptance.v1", "status": "failed", "jobs": 4,
              "proofScope": "typedHeapReadonlyU32Copy", "typedCopyVerified": False,
              "copyAirVerified": False, "nativeCopyVerified": False, "callerAllocationVerified": False,
              "wholeCompilerVerified": False,
              "assumptions": ["valid sequential typed heap", "initialized source view", "writable contained target view",
                              "equal view lengths", "non-overlapping logical views"],
              "excluded": ["native pointer and allocator correspondence", "bytewise or volatile copying",
                           "source memcpy decoding", "frontend/backend preservation"]}
    try:
        report["pythonInputs"], report["leanInputs"] = inputs(), lean_check.source_inputs()
        env, _, tools = lean_check.toolchain(args.lean_bin, 4)
        run(output, "preflight", [tools["lake"]["path"], "build", MODULE, "Contract.Check.Declarations"], cwd=ROOT / "lean", env=env)
        report["audit"] = audit(output, env, tools["lean"]["path"], MODULE, CLAIMS)
        claims = {claim["theorem"]: set(claim["dependencies"]) for claim in json.loads((output / "audit.json").read_text())["claims"]}
        needed = {NS + n for n in ("copy", "copyFrom", "disjoint", "Prefix", "source_after_store", "prefix_after_store")}
        needed |= {"Compiler.ZigAir.Memory." + n for n in ("load", "store", "State.valid", "WordArray.Writable",
            "WordArray.Represents", "WordArray.Frame", "WordArray.frame_store", "WordArray.write_total")}
        if not needed <= claims[NS + "copy_refines"] or NS + "copy_refines" not in claims[NS + "Tests.total_witness"]:
            raise ValueError("copy proof lost a semantic or nonvacuity dependency")
        report["controls"] = controls(output, env, tools["lean"]["path"])
        proof, artifacts = prove.check_module(MODULE, CLAIMS, lean_bin=args.lean_bin, jobs=4, fresh=True)
        directory = output / "proof"
        directory.mkdir()
        for name, data in artifacts.items():
            (directory / name).write_bytes(data)
        write_json(directory / "report.json", proof)
        report["proofReportSha256"] = digest(directory / "report.json")
        if (proof.get("status") != "passed" or proof.get("freshKernelReplay") is not True or
                proof.get("replayIncludesImports") is not True or proof.get("auditedDeclarations") != CLAIMS):
            raise ValueError("copy fresh kernel replay failed")
        if inputs() != report["pythonInputs"] or lean_check.source_inputs() != report["leanInputs"]:
            raise ValueError("copy acceptance inputs changed")
        report.update(status="passed", typedCopyVerified=True, auditedDeclarations=len(CLAIMS))
    finally:
        write_json(output / "report.json", report)
    print("Typed copy acceptance passed; source and native correspondence remain open.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    check(parser.parse_args())
