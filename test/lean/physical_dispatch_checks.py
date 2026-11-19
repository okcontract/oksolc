#!/usr/bin/env python3
"""Bind the complete extracted dispatcher to physical recursive constructors.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import importlib
import json
import re

from check_argument_memory import ROOT, NS
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

MODULE = "Compiler.Extraction.InternerPhysicalDispatchTests"
RECURSIVE = NS + "Normalization.OwnedCall.Recursive."
GENERATORS = ("nested_construction", "associative", "alternating_mask", "signextend_mask", "opposite_shifts", "shift_masks", "dispatch")
CLAIMS = [RECURSIVE + name for name in (
    "operation_request", "borrowed_operation_request", "constant_request", "materialize_request", "actual_dispatcher", "actual_borrowed_dispatcher", "ignores_seed",
    "lift_language_error", "bind_fault_reached")]
CLAIMS += [RECURSIVE + "Tests." + name for name in (
    "constant_trace", "sequential_constructor_state", "first_failure_stops_second", "second_failure_retains_first",
    "semantic_failure_retains_effects", "materialization_encoding", "unary_dispatch", "revision_dispatch",
    "complete_nested_success", "complete_nested_failure")]


def bindings():
    checked = []
    for name in GENERATORS:
        module = importlib.import_module("extract_" + name)
        args = [module.nested.SOURCE.read_bytes(), module.nested.OPCODES.read_bytes(), module.nested.STORAGE.read_bytes()]
        if name == "dispatch":
            args.append(module.VERSIONS.read_bytes())
        if module.extract(*args) != module.OUTPUT.read_bytes():
            raise ValueError("stale polymorphic dispatcher/helper: " + name)
        checked.append(str(module.OUTPUT.relative_to(ROOT)))
    return {"generatedModules": checked, "control": "one extracted dispatcher specialized to logical and physical effects",
            "boundary": "Native graph queries, recursive argument preparation and universal physical recursive preservation remain open."}


def audit(output):
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    owned = NS + "Normalization.OwnedCall."
    required = {
        RECURSIVE + "actual_dispatcher": {RECURSIVE + "constructors", RECURSIVE + "callbacks",
            "Compiler.Extraction.Dispatch.simplify", "Compiler.Extraction.Dispatch.binaryStage",
            "Compiler.Extraction.Dispatch.unaryStage", "Compiler.Extraction.Dispatch.constantStage",
            "Compiler.Extraction.Dispatch.evmStage", "Compiler.Extraction.Interner.constructorCode"},
        RECURSIVE + "Tests.complete_nested_success": {RECURSIVE + "callbacks", RECURSIVE + "Tests.constantChild",
            owned + "Caller.find", owned + "Caller.initLookup", owned + "finish",
            "Compiler.Extraction.Dispatch.simplify", "Compiler.ZigAir.Memory.allocate", "Compiler.ZigAir.Memory.cleanup"},
        RECURSIVE + "Tests.second_failure_retains_first": {RECURSIVE + "Tests.recording", "Compiler.Algebraic.Effect.bind"},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError("physical dispatcher lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return {"checkedDependencies": sorted(required), "physicalDispatcherBindingVerified": True,
            "physicalRecursivePreservationVerified": False,
            "pendingObligations": ["universal physical recursive memory and word induction", "native constructor argument preparation and graph/query refinement"]}


def controls(output, env, lean):
    directory = ROOT / "lean/Compiler/Extraction"
    imports = "import Compiler.Extraction.InternerPhysicalTests\nimport Compiler.Extraction.DispatchTests\n"
    model = without_imports((directory / "InternerPhysicalDispatch.lean").read_text())
    tests = without_imports((directory / "InternerPhysicalDispatchTests.lean").read_text())
    records = [mutation_check(output, "physical-dispatch-unchanged", imports + model + tests, True, env, lean)]
    for name, before, after in (
        ("reversed-operands", "operation := fun opcode ids _ => find (Interner.constructorCode.operationRequest opcode ids)",
         "operation := fun opcode ids _ => find (Interner.constructorCode.operationRequest opcode ids.reverse)"),
        ("wrong-constant", "constant := fun value _ => find (Interner.constructorCode.constantRequest value)",
         "constant := fun value _ => find (Interner.constructorCode.constantRequest (value + 1))"),
        ("wrong-materialization", "materialize := fun _ value _ => find (Interner.constructorCode.constantRequest value)",
         "materialize := fun _ value _ => find (Interner.constructorCode.constantRequest (value + 1))"),
        ("discard-callback-memory", "Dispatch.simplify (reads before.graph) (constructors find borrowed) usizeBits key.instruction key.arguments () before }",
         "let (result, after) := Dispatch.simplify (reads before.graph) (constructors find borrowed) usizeBits key.instruction key.arguments () before\n    (result, { after with memory := before.memory }) }"),
        ("reversed-dispatch-arguments", "usizeBits key.instruction key.arguments () before }",
         "usizeBits key.instruction key.arguments.reverse () before }"),
        ("semantic-fault-as-oom", "result.mapError Fault.language", "result.mapError (fun _ => Fault.language .outOfMemory)"),
    ):
        if model.count(before) != 1:
            raise ValueError("ambiguous physical dispatcher mutation: " + name)
        records.append(mutation_check(output, "physical-dispatch-" + name,
            imports + model.replace(before, after) + tests, False, env, lean))
    for record in records:
        diagnostic = (output / (record["name"] + ".stdout")).read_text()
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant", diagnostic, re.I):
            raise ValueError("physical dispatcher control hit a resource or syntax failure: " + record["name"])
        if not record["expectedAcceptance"] and not re.search(
                r"error: (?:unsolved goals|Application type mismatch|Type mismatch|Tactic[^\n]*failed)", diagnostic):
            raise ValueError("physical dispatcher control lacks a semantic proof failure: " + record["name"])
    return records
