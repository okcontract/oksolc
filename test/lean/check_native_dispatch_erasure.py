#!/usr/bin/env python3
"""Audit paired native operand transport and its actual caller consumption.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import json
from pathlib import Path

import check_publication_resource_trace as publication
import physical_dispatch_preservation_checks as preservation
from check_zig_air_memory_proofs import without_imports

native = publication.native
MODULE = "Compiler.Extraction.InternerNativeDispatchEffectsTests"
DISPATCH = "Compiler.Extraction.Dispatch.Effects."
NS = native.OWNED + "ConstructorItem.NativeRecursion."
PAIRED = ["logical_operands", "alternating_build_operands", "alternating_search_operands", "alternating_operands",
    "signextend_mask_operands", "shift_product_operands", "unary_stage_operands", "evm_stage_operands",
    "binary_stage_operands", "simplify_options_operands", "simplify_operands"]
CLAIMS = list(dict.fromkeys(publication.CLAIMS + preservation.CLAIMS + [DISPATCH + name for name in PAIRED]))
CLAIMS += [NS + name for name in ("operand_erases", "query_erases", "dispatcher_erases", "exhausted_erases", "recorded_find_erases")]
CLAIMS += [NS + "EffectTests." + name for name in (
    "native_operand_ignores_annotation", "native_operand_bounds", "native_operand_after_retirement", "reached_operand_erases",
    "empty_native_query", "invalid_native_query", "all_native_queries_erase", "native_dispatch_erases",
    "native_dispatch_reaches_child", "native_dispatch_query_failure", "native_caller_erases", "caller_query_fault_retains_scope")]


def dependencies(output):
    checked = publication.dependencies(output)
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    checked += preservation.audit_claims(claims)["checkedDependencies"]
    required = {
        DISPATCH + "simplify_operands": {DISPATCH + "Operands.load", DISPATCH + "simplify_options_operands",
            DISPATCH + "binary_stage_operands", DISPATCH + "unary_stage_operands", DISPATCH + "evm_stage_operands"},
        NS + "operand_erases": {NS + "operand", native.OWNED + "ConstructorItem.ShiftInput.operand",
            native.OWNED + "TemporaryMemory.readId"},
        NS + "dispatcher_erases": {DISPATCH + "simplify_operands", NS + "operand_erases", NS + "dispatcher_snapshot",
            native.OWNED + "Recursive.QueryTiming.simplify", native.OWNED + "NativeReads.query"},
        NS + "recorded_find_erases": {NS + "dispatcher_erases", publication.TRACE + "find_erases",
            publication.PUB + "EffectTransport.publish", native.OWNED + "Caller.EffectTransport.find"},
        NS + "EffectTests.native_caller_erases": {NS + "recorded_find_erases", NS + "exhausted_erases"},
        NS + "EffectTests.caller_query_fault_retains_scope": {native.OWNED + "NativeReads.query", NS + "context",
            native.OWNED + "Caller.find", native.TRACE + "record"},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError("native dispatcher erasure lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return list(dict.fromkeys(checked + sorted(required)))


def source_parts():
    directory = native.ROOT / "lean/Compiler/Extraction"
    def read(name):
        return without_imports((directory / (name + ".lean")).read_text())
    effects = read("DispatchEffects").replace("namespace Compiler.Extraction.Dispatch\n",
        "namespace Compiler.Extraction.DispatchErasureMutation\nopen Compiler.Extraction.Dispatch\n")
    effects = effects.replace("end Compiler.Extraction.Dispatch\n", "end Compiler.Extraction.DispatchErasureMutation\n")
    physical = read("InternerPhysicalDispatchEffects").replace("OwnedCall.Recursive\n", "OwnedCall.RecursiveErasureMutation\n")
    physical = physical.replace("open Compiler.Algebraic", "open Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Recursive\nopen Compiler.Algebraic")
    physical = physical.replace("Dispatch.Effects", "DispatchErasureMutation.Effects")
    recursion = read("InternerNativeRecursion").replace("ConstructorItem.NativeRecursion", "ConstructorItem.NativeErasureMutation")
    transport = read("InternerNativeDispatchEffects").replace("ConstructorItem.NativeRecursion", "ConstructorItem.NativeErasureMutation")
    transport = transport.replace("Recursive.erasing", "RecursiveErasureMutation.erasing")
    tests = read("InternerNativeDispatchEffectsTests").replace("ConstructorItem.NativeRecursion", "ConstructorItem.NativeErasureMutation")
    return effects, physical, recursion, transport, tests


def controls(output, env, lean):
    records = publication.controls(output, env, lean) + preservation.controls(output, env, lean)
    effects, physical, recursion, transport, tests = source_parts()
    prefix = "import " + MODULE + "\n"
    def program(effects, recursion):
        return prefix + effects + physical + recursion + transport + tests
    source = program(effects, recursion)
    variants = []
    for name, before, after in (
        ("annotation-only", "r.related (left source index annotation) (right source index annotation)",
            "r.related (left source index annotation) (pure annotation)"),
        ("first-index-only", "load : ∀ source index annotation, r.related", "load : ∀ source index annotation, index = 0 → r.related"),
    ):
        if effects.count(before) != 1:
            raise ValueError("ambiguous paired operand mutation: " + name)
        variants.append((name, program(effects.replace(before, after), recursion)))
    for name, before, after in (
        ("annotation-as-native-read", "fun source index _ =>\n  ShiftInput.operand (view source) index",
            "fun _ _ annotation => pure annotation"),
        ("wrong-native-index", "ShiftInput.operand (view source) index", "ShiftInput.operand (view source) 0"),
        ("logical-query-fallback", "operand source.address (NativeReads.query owner) before } }",
            "operand source.address (fun action => Nested.readAction (action (Interner.representativeReads before.graph))) before } }"),
    ):
        if recursion.count(before) != 1:
            raise ValueError("ambiguous native dispatch mutation: " + name)
        variants.append((name, program(effects, recursion.replace(before, after))))
    return records + native.check_controls(output, env, lean, source, variants, prefix="native-dispatch-")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--preflight", action="store_true")
    native.check(parser.parse_args(), module=MODULE, claims=CLAIMS, dependency_check=dependencies,
        control_check=controls, publication=True, native_dispatch=True)
