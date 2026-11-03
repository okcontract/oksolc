#!/usr/bin/env python3
"""Audit captured native Expression fields in the existing typed heap.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "lean"))
sys.path.insert(0, str(ROOT / "lean/zig_air"))
import environment as lean_check
import check_compiler
import check_word_swap
import generate_expression_layout as admission
import prove
from build_toolchain import digest, run, source_identity, text, write_json
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

MODULE = "Compiler.Extraction.ExpressionFieldTests"
NS = "Compiler.Extraction.Expression."
MEM = "Compiler.ZigAir.Memory."
CLAIMS = [MEM + name for name in ("Field.layout_eq_leaf", "Ty.aggregate_member_geometry", "Ty.aggregate_disjoint",
    "Ty.fieldAt_geometry", "fieldPointer_address", "fieldPointer_parent", "root_fieldPointer",
    "fieldPointer_replace_cells", "fieldPointer_after_store", "field_load_after_store")]
CLAIMS += [NS + name for name in ("layout_checked", "field_types_checked", "root_selector", "read_after_store",
    "read_from_root", "fields_after_stores")]
CLAIMS += [NS + "Tests." + name for name in ("complete_valid", "complete_fields", "source_field_read",
    "unsorted_offset_borrow", "original_slice_bound", "item_allocation_identity", "uninitialized_fields_reject",
    "partial_slice_reject", "missing_id_is_not_defaulted", "wrong_leaf_type_rejects", "wrong_leaf_state_invalid",
    "duplicate_leaf_state_invalid", "overlapping_fields_reject", "field_extent_rejects", "misaligned_field_rejects",
    "parent_alignment_rejects", "same_extent_different_owner_rejects", "interior_bytes_are_not_fields",
    "full_parent_extent_is_required", "const_field_store_rejects", "whole_record_load_remains_unsupported",
    "cleanup_rejects_stale_descriptor", "cleanup_keeps_independent_operands", "address_reuse_keeps_lifetime",
    "array_descriptor_field_read", "item_store_initializes_only_item", "independent_field_overwrites",
    "store_readback_from_execution")]
PROBES = {"layout": ROOT / "test/lean/expression_layout.zig", "fields": ROOT / "test/lean/expression_fields.zig"}


def inputs():
    saved = check_compiler.snapshot()
    saved.update({str(path.relative_to(ROOT)): digest(path) for path in (ROOT / "test/lean").rglob("*.py")})
    saved.update({str(path.relative_to(ROOT)): digest(path) for path in PROBES.values()})
    return saved


def check_observations(profile, mode):
    expected_keys = {"schema", "zigVersion", "mode", "backend", "item_pointer", "argument_allocation_pointer",
        "argument_allocation_length", "descriptor_pointers", "descriptor_bytes", "descriptor_alignment",
        "before", "after", "borrowed_arguments"}
    if (not isinstance(profile, dict) or set(profile) != expected_keys or
            profile["schema"] != "oksolc.expression-field-observations.v1" or profile["zigVersion"] != "0.17.0" or
            profile["mode"] != mode or profile["backend"] != "stage2_llvm"):
        raise ValueError("unsupported native expression field observations")
    for key, expected in (("argument_allocation_length", 4), ("descriptor_bytes", 32), ("descriptor_alignment", 8)):
        if type(profile[key]) is not int or profile[key] != expected:
            raise ValueError("changed expression/argument extent or alignment: " + key)
    descriptors = profile["descriptor_pointers"]
    if not isinstance(descriptors, list) or len(descriptors) != 2:
        raise ValueError("incomplete descriptor array observations")
    item, arguments = profile["item_pointer"], profile["argument_allocation_pointer"]
    regions = [(item, 224, 16), (arguments, 16, 4), (descriptors[0], 64, 8)]
    if (any(type(base) is not int or not 0 < base < 2**64 or base + size > 2**64 or base % aligned
            for base, size, aligned in regions) or
            type(descriptors[1]) is not int or descriptors[1] != descriptors[0] + 32 or
            any(not (a + size <= b or b + other <= a)
                for i, (a, size, _) in enumerate(regions) for b, other, _ in regions[i + 1:])):
        raise ValueError("invalid, misaligned or aliased native field backing")
    before = {"item_pointer": item, "arguments_pointer": arguments + 4, "arguments_length": 2,
        "id": 17, "sequence_number": 23}
    for label, expected in (("before", [before, before]),
            ("after", [before, {**before, "id": 19, "sequence_number": 29}])):
        observations = profile[label]
        if (not isinstance(observations, list) or len(observations) != 2 or
                any(not isinstance(record, dict) or set(record) != set(before) or
                    any(type(value) is not int for value in record.values()) for record in observations) or
                observations != expected):
            raise ValueError("incomplete or changed native field observations: " + label)
    borrowed = profile["borrowed_arguments"]
    if not isinstance(borrowed, list) or any(type(value) is not int for value in borrowed) or borrowed != [99, 1]:
        raise ValueError("native offset borrow lost its original unsorted contents")


def audit(output, env, lean):
    checked = check_word_swap.audit(output, env, lean, MODULE, CLAIMS)
    records = json.loads((output / "audit.json").read_bytes())["claims"]
    dependencies = {record["theorem"]: set(record["dependencies"]) for record in records}
    requirements = {
        MEM + "Ty.fieldAt_geometry": {MEM + "Ty.aggregateValid", MEM + "Ty.fieldAt", MEM + "Ty.aggregate_member_geometry"},
        MEM + "field_load_after_store": {MEM + "fieldPointer", MEM + "fieldPointer_after_store", MEM + "load_after_store"},
        NS + "read_from_root": {NS + "allocationType", NS + "root_selector", MEM + "root_fieldPointer",
            MEM + "acceptsView", MEM + "load"},
        NS + "fields_after_stores": {NS + "readFields", MEM + "fieldPointer_after_store",
            MEM + "load_disjoint_after_store", MEM + "load_after_store"},
        NS + "Tests.store_readback_from_execution": {NS + "root_selector", NS + "field_types_checked",
            NS + "read_after_store", MEM + "field_load_after_store"},
    }
    for claim, required in requirements.items():
        if not required <= dependencies[claim]:
            raise ValueError("native field proof lost dependencies: " + claim)
    return {**checked, "checkedDependencies": sorted(requirements)}


def controls(output, env, lean):
    directory = ROOT / "lean/Compiler"
    source = "import Compiler.ZigAir.MemoryPointers\nimport Compiler.ZigAir.MemorySlots\nimport Compiler.Extraction.AssemblyItemLayout\n"
    for name in ("ZigAir/MemoryRecordFields.lean", "Extraction/ExpressionLayout.lean",
            "Extraction/ExpressionFields.lean", "Extraction/ExpressionFieldTests.lean"):
        source += without_imports((directory / name).read_text()) + "\n"
    records = [mutation_check(output, "expression-fields-unchanged", source, True, env, lean)]
    for name, before, after in (
            ("lost-parent-check", "if !acceptsView allocation.type address.offset owner", "if false"),
            ("lost-lifetime", "⟨address.allocation, address.offset + offset⟩", "⟨0, address.offset + offset⟩"),
            ("lost-parent-offset", "⟨address.allocation, address.offset + offset⟩", "⟨address.allocation, offset⟩"),
            ("wrong-field-offset", "def idOffset : Nat := 24", "def idOffset : Nat := 28"),
            ("omitted-field", "(28, .scalar (.int false 32))", "(32, .scalar (.int false 32))"),
            ("borrow-rebased", "def arguments : Value := .slice argumentsType ⟨1, 4⟩ 2", "def arguments : Value := .slice argumentsType ⟨1, 0⟩ 2"),
            ("omitted-read", "  .ok [item, arguments, id, sequence]\n", "  .ok [item, arguments, id, id]\n"),
    ):
        count = source.count(before)
        # Address conclusions deliberately repeat the selector expression. Only
        # mutate its executable definition, leaving the theorem statement fixed.
        if name in ("lost-lifetime", "lost-parent-offset"):
            if count != 2:
                raise ValueError("ambiguous field-pointer mutation: " + name)
        elif count != 1:
            raise ValueError("ambiguous expression field mutation: " + name)
        records.append(mutation_check(output, "expression-fields-" + name,
            source.replace(before, after, 1), False, env, lean))
    return records


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.expression-field-verification.v1", "status": "failed", "jobs": 4,
        "scope": "complete captured Expression field geometry, typed loads/stores and lifetime identity",
        "typedFieldProjectionVerified": False, "nativeGraphMutationCorrespondenceVerified": False,
        "recursiveConstructorsVerified": False, "nativeBackendVerified": False, "wholeCompilerVerified": False}
    try:
        report["inputs"] = inputs()
        toolchain = json.loads(args.toolchain.read_bytes())
        compiler, lib = Path(toolchain["compiler"]["path"]), Path(toolchain["compiler"]["zigLibDir"])
        report["toolchainReportSha256"], report["compilerSha256"] = digest(args.toolchain), digest(compiler)
        if report["compilerSha256"] != toolchain["compiler"]["sha256"] or source_identity(lib.parent) != toolchain["sourceTree"]:
            raise ValueError("expression field toolchain inputs changed")
        env, _, tools = lean_check.toolchain(args.lean_bin, 4)
        report["tools"] = tools
        run(output, "python-preflight", [sys.executable, "-m", "unittest", "discover", "-s", "test/lean", "-p", "test_expression_layout.py"], cwd=ROOT)
        run(output, "cached-proof", [tools["lake"]["path"], "build", MODULE], cwd=ROOT / "lean", env=env)
        report["audit"] = audit(output, env, tools["lean"]["path"])
        report["controls"] = controls(output, env, tools["lean"]["path"])
        run(output, "version", [compiler, "version"])
        if text(output, "version") != "0.17.0":
            raise ValueError("expression fields require pinned Zig 0.17.0")
        report["native"] = []
        for mode in ("Debug", "ReleaseSafe", "ReleaseFast"):
            entry = {"mode": mode, "accepted": False}
            report["native"].append(entry)
            for kind, probe in PROBES.items():
                label = kind + "-" + mode
                binary = output / label
                run(output, "build-" + label, [compiler, "build-exe", "-j4", "--zig-lib-dir", lib, "-fllvm", "-O", mode,
                    "--dep", "compiler", "-Mroot=" + str(probe), "-O", mode, "-Mcompiler=" + str(ROOT / "src/modules.zig"),
                    "--cache-dir", ROOT / ".zig-cache", "--global-cache-dir", output / "global-cache", "-femit-bin=" + str(binary)], cwd=ROOT)
                run(output, "probe-" + label, [binary], cwd=ROOT)
                observation = output / ("probe-" + label + ".stdout")
                entry[kind] = {"binarySha256": digest(binary), "observationSha256": digest(observation)}
                write_json(output / "report.json", report)
                if observation.stat().st_size > 16384:
                    raise ValueError("native expression field profile exceeded bound")
                profile = json.loads(observation.read_bytes())
                if kind == "layout":
                    if profile["target"]["mode"] != mode or admission.generate(profile) != admission.OUTPUT.read_bytes():
                        raise ValueError("captured field layout differs from source-bound admitted layout")
                else:
                    check_observations(profile, mode)
                if (output / ("build-" + label + ".stderr")).read_bytes() or (output / ("probe-" + label + ".stderr")).read_bytes():
                    raise ValueError("unreviewed native expression field diagnostic")
            entry.update(accepted=True, completeFields=4, descriptorCases=2, offsetBorrow=[99, 1])
        proof, artifacts = prove.check_module(MODULE, CLAIMS, lean_bin=args.lean_bin, jobs=4, fresh=True)
        directory = output / "proof"
        directory.mkdir()
        for name, data in artifacts.items():
            (directory / name).write_bytes(data)
        write_json(directory / "report.json", proof)
        report["proofReportSha256"] = digest(directory / "report.json")
        if (proof.get("status") != "passed" or proof.get("freshKernelReplay") is not True or
                proof.get("replayIncludesImports") is not True or proof.get("auditedDeclarations") != CLAIMS):
            raise ValueError("expression field proof or fresh imported replay failed")
        if (inputs() != report["inputs"] or digest(args.toolchain) != report["toolchainReportSha256"] or
                digest(compiler) != report["compilerSha256"] or source_identity(lib.parent) != toolchain["sourceTree"]):
            raise ValueError("expression field acceptance inputs changed")
        report.update(status="passed", typedFieldProjectionVerified=True)
    except BaseException as error:
        report["error"] = str(error)
        raise
    finally:
        write_json(output / "report.json", report)
    print("Captured Expression field proofs passed; native graph mutation correspondence and recursive constructors remain open.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    check(parser.parse_args())
