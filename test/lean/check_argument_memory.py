#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Audit the logical/typed argument-memory relation and checked release contract.
// Copyright (C) 2026 OKcontract Pte. Ltd.

This model gate makes no native allocator or normalization integration claim.
"""
import argparse
import json
from pathlib import Path
import re

import check_word_swap
from check_word_swap import ROOT, lean_check, prove
from build_toolchain import digest, run, write_json
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

MODULE = "Compiler.Extraction.ArgumentMemoryTests"
NS = "Compiler.Extraction.Memory.Arguments."
MEMORY = "Compiler.ZigAir.Memory."
CLAIMS = [MEMORY + name for name in (
    "erase_lookup", "erase_preserves_valid", "erase_keeps_counters", "erase_load_other", "erase_load_dead")]
CLAIMS += [NS + name for name in (
    "owned_writable", "related_read", "release_empty", "release_effects", "related_erase", "release_refines", "released_read_rejects")]
CLAIMS += [NS + "Tests." + name for name in (
    "valid", "first_live", "related", "read_agrees", "release_both", "total_witness", "after_related", "after_valid",
    "history_retained", "alias_dead", "other_words_and_uninitialized_preserved", "double_free_rejected",
    "wrong_allocator_rejected", "wrong_extent_rejected", "missing_typed_lifetime_rejected",
    "empty_skips_invalid_heap_and_sentinel", "stack_rejected", "stack_is_not_owned", "readonly_storage_rejected",
    "uninitialized_owned_can_be_freed", "uninitialized_is_not_related", "malformed_heap_rejected", "second_release_keeps_scratch")]


def inputs():
    # Include transitive imported harness helpers, including lean/zig_air.
    paths = list((ROOT / "lean").rglob("*.py")) + list((ROOT / "test/lean").glob("*.py"))
    return {str(path.relative_to(ROOT)): digest(path) for path in sorted(paths) if ".lake" not in path.parts}


def audit(output, env, lean):
    result = check_word_swap.audit(output, env, lean, MODULE, CLAIMS)
    claims = {claim["theorem"]: set(claim["dependencies"]) for claim in json.loads((output / "audit.json").read_text())["claims"]}
    requirements = {
        NS + "release_refines": {NS + name for name in (
            "release", "Related", "Owned", "ReleasePost", "release_effects", "related_erase")}
            | {MEMORY + "erase", MEMORY + "erase_preserves_valid", "Compiler.Extraction.Memory.releaseSlice"},
        NS + "related_read": {NS + "Related", MEMORY + "WordArray.Represents", "Compiler.Extraction.Memory.readArgument"},
        NS + "released_read_rejects": {NS + "ReleasePost", MEMORY + "load", "Compiler.Extraction.Memory.readArgument"},
        NS + "Tests.total_witness": {NS + "release_refines", NS + "Tests.related"},
        NS + "Tests.read_agrees": {NS + "related_read"},
    }
    for name, needed in requirements.items():
        if not needed <= claims[name]:
            raise ValueError("argument memory proof lost a representation or release dependency: " + name)
    return {**result, "checkedDependencies": sorted(requirements)}


def controls(output, env, lean):
    paths = [ROOT / "lean/Compiler/ZigAir/MemoryRelease.lean"]
    paths += [ROOT / "lean/Compiler/Extraction" / name for name in (
        "ArgumentMemory.lean", "ArgumentMemoryProofs.lean", "ArgumentMemoryTests.lean")]
    source = "import Compiler.Extraction.MemoryProofs\nimport Compiler.ZigAir.MemoryWordArrayWrites\n"
    source += "\n".join(without_imports(path.read_text()) for path in paths)
    records = [mutation_check(output, "release-unchanged", source, True, env, lean)]
    for name, before, after in (
        ("erase-wrong-lifetime", "entry.1 != id", "entry.1 == id"),
        ("erase-rewinds-id", "{ state with heap := state.heap.filter", "{ state with nextId := 0, heap := state.heap.filter"),
        ("erase-rewinds-address", "{ state with heap := state.heap.filter", "{ state with nextAddress := 8, heap := state.heap.filter"),
        ("release-keeps-logical", ".ok (after, memory)", ".ok (heap, memory)"),
        ("release-keeps-physical", ".ok (after, memory)", ".ok (after, state)"),
        ("release-wrong-allocator", "(releaseSlice heap allocator slice).mapError", "(releaseSlice heap 7 slice).mapError"),
        ("release-ignores-extent", "if cell.type = type ∧", "if True ∧"),
        ("release-ignores-stack", "∧ cell.stack = false then", "∧ True then"),
        ("release-ignores-permission", "∧ cell.writable = true ∧ cell.stack = false then", "∧ True ∧ cell.stack = false then"),
        ("release-ignores-validity", "if !state.valid then", "if false then"),
        ("release-accesses-empty", "if slice.items.isEmpty then .ok (heap, state) else", "if false then .ok (heap, state) else"),
        ("release-accepts-dead", "let some cell := state.heap.lookup id | .error .unallocated",
         "let some cell := state.heap.lookup id | .ok state"),
        ("release-requires-initialization", "if cell.type = type ∧",
         "if cell.cells.isEmpty then .error .uninitialized else\n  if cell.type = type ∧"),
    ):
        if source.count(before) != 1:
            raise ValueError("ambiguous release mutation: " + name)
        records.append(mutation_check(output, name, source.replace(before, after), False, env, lean))
    for record in records:
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant",
                     (output / (record["name"] + ".stdout")).read_text(), re.I):
            raise ValueError("release control hit a resource or syntax failure: " + record["name"])
    return records


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.argument-memory-release.v1", "status": "failed", "jobs": 4,
              "proofScope": "logicalArgumentToTypedHeapRelationAndCheckedRelease",
              "checkedReleaseVerified": False, "nativeAllocatorVerified": False,
              "normalizationReleaseMemoryVerified": False, "sourceTranslatorVerified": False,
              "nativeBackendVerified": False, "wholeCompilerVerified": False,
              "assumptions": ["valid typed heap", "same lifetime IDs in logical and typed heaps",
                              "nonempty logical argument allocations have complete writable nonstack word storage and represented contents",
                              "matching logical allocator and slice"],
              "excluded": ["native allocation/free implementation", "allocation and duplicate-copy integration",
                           "normalization cleanup integration", "item and representative block representation", "machine pointer injection"]}
    try:
        report["inputs"], report["leanInputs"] = inputs(), lean_check.source_inputs()
        env, _, tools = lean_check.toolchain(args.lean_bin, 4)
        report["tools"] = tools
        run(output, "preflight", [tools["lake"]["path"], "build", MODULE], cwd=ROOT / "lean", env=env)
        report["audit"] = audit(output, env, tools["lean"]["path"])
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
            raise ValueError("argument memory audit or fresh kernel replay failed")
        if inputs() != report["inputs"] or lean_check.source_inputs() != report["leanInputs"]:
            raise ValueError("argument memory acceptance inputs changed")
        report.update(status="passed", checkedReleaseVerified=True, auditedDeclarations=len(CLAIMS))
    finally:
        write_json(output / "report.json", report)
    print("Argument-memory relation and checked release passed; native allocator and normalization integration remain open.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    check(parser.parse_args())
