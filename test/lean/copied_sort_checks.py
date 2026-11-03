#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Acceptance helpers for source-bound typed copy followed by captured-swap sort.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""
import json
from pathlib import Path
import re
import sys

from build_toolchain import digest, run
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
from zig_copy_sort_native import CASES, expected
import check_word_copy

ROOT = Path(__file__).resolve().parents[2]
MODULE = "Compiler.Extraction.InsertionSortCopiedTests"
NS = "Compiler.Extraction.InsertionSort.Copied."
TESTS = "Compiler.Extraction.InsertionSort.CopiedTests."
SOURCE = ROOT / "test/lean/zig_copy_sort.zig"
CLAIMS = check_word_copy.CLAIMS + ["Compiler.ZigAir.Memory.WordCopy.source_frame"]
CLAIMS += [NS + n for n in ("run_after_copy", "run_refines", "run_result")]
CLAIMS += [TESTS + n for n, _ in CASES]
CLAIMS += [TESTS + n for n in ("total_witness", "every_success", "zero_budget_keeps_copy", "failed_copy_keeps_prefix",
    "overlap_skips_sort", "one_swap_room_valid", "exhaustion_keeps_copy_and_swap", "exhaustion_observations",
    "suspension_keeps_copied_partial_swap", "suspension_state", "suspension_observations", "shared_run", "same_allocation_source_preserved")]


def audit(output):
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_text())["claims"]}
    required = {NS + n for n in ("run", "copyTo", "run_after_copy")}
    required |= {"Compiler.Extraction.InsertionSort." + n for n in ("copySortUsing", "Captured.run_refines", "Captured.exchange")}
    required |= {"Compiler.ZigAir.Memory.WordCopy." + n for n in ("copy_refines", "source_frame")}
    required |= {"Compiler.ZigAir.GeneratedMemory.fn_swap_u32", "Compiler.ZigAir.Memory.WordArray.Frame.heapFrame"}
    checks = {NS + "run_refines": required,
              NS + "run_result": {"Compiler.Extraction.InsertionSort.Captured.run_result", "Compiler.ZigAir.Memory.WordCopy.copy_refines"},
              TESTS + "total_witness": {NS + "run_refines"}, TESTS + "every_success": {NS + "run_result"}}
    for name, needed in checks.items():
        if not needed <= claims[name]:
            raise ValueError("copy/sort proof lost a semantic dependency: " + name)
    return {"checkedDependencies": sorted(checks)}


def controls(output, env, lean):
    directory = ROOT / "lean/Compiler/Extraction"
    source = "import Compiler.Extraction.InsertionSortCapturedTests\nimport Compiler.ZigAir.MemoryWordCopyProofs\n"
    source += "import Compiler.ZigAir.MemoryWordCopyTests\nimport Compiler.ZigAir.MemoryWordCopyFrame\n"
    source += "".join(without_imports((directory / name).read_text()) for name in ("InsertionSortCopied.lean", "InsertionSortCopiedTests.lean"))
    records = [mutation_check(output, "copied-sort-unchanged", source, True, env, lean)]
    for name, before, after in (
        ("copied-sort-reversed-copy", "let (result, after) := WordCopy.copy state source target", "let (result, after) := WordCopy.copy state target source"),
        ("copied-sort-wrong-view", "Captured.run budget middle target", "Captured.run budget middle source"),
        ("copied-sort-stale-state", "fun middle => Captured.run budget middle target", "fun _ => Captured.run budget state target"),
    ):
        if source.count(before) != (2 if name == "copied-sort-wrong-view" else 1):
            raise ValueError("ambiguous copy/sort mutation: " + name)
        records.append(mutation_check(output, name, source.replace(before, after, 1), False, env, lean))
    # Isolate the extracted sequence so intentional state/control mutations
    # exercise small effect observations without cascading proof resource errors.
    program = (directory / "InsertionSortProgram.lean").read_text()
    start, stop = program.index("def copySortUsing "), program.index("def insert (j : Nat)")
    sequence = "import Compiler.Extraction.InsertionSortModel\n" + program[start:stop].replace("copySortUsing", "sequenceControl")
    sequence += '''
example : sequenceControl (fun (_ : Nat) => (Except.ok (), 1))
    (fun state => (Except.ok (), state + 10) : Nat → Except Nat Unit × Nat) 0 = (.ok (), 11) := rfl
example : sequenceControl (fun (_ : Nat) => (Except.error 7, 1))
    (fun state => (Except.ok (), state + 10) : Nat → Except Nat Unit × Nat) 0 = (.error 7, 1) := rfl
'''
    records.append(mutation_check(output, "copy-sequence-unchanged", sequence, True, env, lean))
    for name, before, after in (
        ("copy-sequence-lost-state", "| (.ok (), after) => sort after", "| (.ok (), _) => sort state"),
        ("copy-sequence-ignored-failure", "| (.error fault, after) => (.error fault, after)", "| (.error _, after) => sort after"),
        ("copy-sequence-lost-failed-prefix", "| (.error fault, after) => (.error fault, after)", "| (.error fault, _) => (.error fault, state)"),
    ):
        if sequence.count(before) != 1:
            raise ValueError("ambiguous sequence mutation: " + name)
        records.append(mutation_check(output, name, sequence.replace(before, after), False, env, lean))
    for record in records:
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant",
                     (output / (record["name"] + ".stdout")).read_text(), re.I):
            raise ValueError("copy/sort control hit a resource or syntax failure: " + record["name"])
    return records


def bindings(output, env, lean):
    source = "import " + MODULE + "\nopen Compiler.Extraction.InsertionSort.CopiedTests\nopen Compiler.ZigAir.Memory.WordArray\n"
    for name, values in CASES:
        wanted = expected(values)
        words = wanted["source"] + wanted["target"] + [99]
        source += f"example : observe 160 {values} = (.ok (), {words}.map (fun value => .ok (number value))) := {name}\n"
    source += '''
open Compiler.ZigAir.Memory in
example : Compiler.Extraction.InsertionSort.Copied.run 160 WordCopy.Tests.shared WordCopy.Tests.source sharedTarget =
    (.ok (), sharedAfter) := shared_run
open Compiler.ZigAir.Memory in
example : (List.range 6).map (fun index => load sharedAfter (WordCopy.Tests.source.pointer index)) =
    [3, 1, 2, 1, 2, 3].map (fun value => .ok (number value)) := by rfl'
'''
    return mutation_check(output, "copy-sort-native-model-binding", source, True, env, lean)


def native(output, zig, tree, env):
    records = {}
    run(output, "format", [zig, "fmt", "--check", SOURCE], env=env)
    for mode in ("Debug", "ReleaseSafe", "ReleaseFast"):
        directory = output / mode
        directory.mkdir()
        library = directory / "copy-sort.dylib"
        run(directory, "build", [zig, "build-lib", SOURCE, "--zig-lib-dir", tree / "lib", "-dynamic", "-fllvm",
            "-fno-incremental", "-O" + mode, "-femit-bin=" + str(library), "--cache-dir", directory / "cache",
            "--global-cache-dir", directory / "global-cache"], env=env)
        run(directory, "native", [sys.executable, ROOT / "test/lean/zig_copy_sort_native.py", "--library", library,
            "--output", directory / "observations.json"], env=env)
        wanted = [{"case": name, "input": values, "expected": expected(values), "actual": expected(values)} for name, values in CASES]
        wanted.append({"case": "same_allocation", "input": [3, 1, 2], "expected": [3, 1, 2, 1, 2, 3], "actual": [3, 1, 2, 1, 2, 3]})
        observed = json.loads((directory / "observations.json").read_text())
        if observed != {"schema": "oksolc.native-copy-sort-cases.v1", "cases": wanted}:
            raise ValueError("native copy/sort observations differ from the checked model inputs")
        records[mode] = {"status": "passed", "cases": len(wanted), "librarySha256": digest(library),
                         "observationsSha256": digest(directory / "observations.json")}
    return records
