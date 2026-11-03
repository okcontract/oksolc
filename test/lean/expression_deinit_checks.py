#!/usr/bin/env python3
"""Bind the checked expression destructor to insertion rollback.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import json
import re
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
import extract_expression_deinit as extraction
from test_expression_deinit import MUTATIONS, change_body

MODULE = "Compiler.Extraction.ExpressionDeinitTests"
NS = "Compiler.Extraction.ExpressionDeinit."
CLAIMS = [NS + name for name in (
    "execute_equation", "run_equation", "run_verified", "Post.preserves_borrow", "last_value_memory_equation", "last_value_equation", "last_value_preserved", "insertion_verified")]
CLAIMS += [NS + "Tests." + name for name in (
    "external_admitted", "initial_valid", "complete_contract", "source_order", "argument_dead",
    "borrowed_cells_preserved", "allocation_history", "item_value_fault", "item_allocation_fault",
    "wrong_allocator", "wrong_extent", "dead_descriptor", "empty_arguments", "insertion_initial_valid",
    "taken_result", "taken_valid", "rollback_contract", "insertion_rollback", "insertion_fault_stops",
    "exact_descriptors", "insertion_words")]


def audit(output):
    claims = {c["theorem"]: set(c["dependencies"])
              for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    memory = "Compiler.Extraction.Memory.Arguments.Normalization."
    required = {
        NS + "run_equation": {NS + "expressionDeinitCode", NS + "execute", NS + "Stage.execute", memory + "free"},
        NS + "run_verified": {NS + "run_equation", memory + "free_valid", memory + "released_consumed"},
        NS + "last_value_preserved": {NS + "run_verified", NS + "last_value_equation", NS + "insertionOperations"},
        NS + "insertion_verified": {NS + "last_value_preserved", "Compiler.Extraction.Interner.InsertionExecution.verified"},
        NS + "Tests.rollback_contract": {NS + "last_value_preserved", NS + "Tests.taken_valid", memory + "take_refines"},
        NS + "Tests.insertion_words": {NS + "insertion_verified", NS + "Tests.insertion_rollback"},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError("destructor lost checked dependencies: " + name + ": " + ", ".join(sorted(needed - claims[name])))
    return {"checkedDependencies": sorted(required), "argumentDestructionDependenciesChecked": True,
            "nativeItemDestructionVerified": False, "universalRollbackAdmissionVerified": False,
            "physicalCallerInsertionContractsDerived": False}


def controls(output, env, lean):
    directory = ROOT / "lean/Compiler/Extraction"
    names = ("ExpressionDeinit.lean", "ExpressionDeinitProgram.lean", "ExpressionDeinitProofs.lean",
             "ExpressionDeinitInsertion.lean", "ExpressionDeinitTests.lean")
    sources = {name: without_imports((directory / name).read_text()) for name in names}
    prelude = ("import Compiler.Extraction.StorageExecutionTests\n"
               "import Compiler.Extraction.ArgumentMemoryTests\n"
               "import Compiler.Extraction.NormalizationMemoryLifetime\n")

    def assembled(parts):
        return prelude + "\n".join(parts[name] for name in names)

    source = assembled(sources)
    records = [mutation_check(output, "destructor-unchanged", source, True, env, lean)]
    for name, before, after in (
        ("traversal-discard-fault-state", "| .error fault => (.error fault, reached)\n    | .ok () => executeStages step rest reached",
         "| .error fault => (.error fault, before)\n    | .ok () => executeStages step rest reached"),
        ("traversal-continue-after-fault", "| .error fault => (.error fault, reached)\n    | .ok () => executeStages step rest reached",
         "| .error _ => executeStages step rest reached\n    | .ok () => executeStages step rest reached"),
        ("traversal-discard-success-state", "| .ok () => executeStages step rest reached",
         "| .ok () => executeStages step rest before"),
        ("discard-item-effects", "(result.mapError Fault.item, { before with memory := reached })",
         "(result.mapError Fault.item, before)"),
        ("discard-item-fault", "(result.mapError Fault.item, { before with memory := reached })",
         "(.ok (), { before with memory := reached })"),
        ("wrong-item-pointer", "action descriptor.item before.memory", "action (descriptor.item + 1) before.memory"),
        ("wrong-allocator", "let (result, memory) := free external allocator descriptor.arguments before.memory",
         "let (result, memory) := free external 0 descriptor.arguments before.memory"),
        ("dead-descriptor-reused", "if before.invalidated then (.error .invalidDescriptor, before) else",
         "if false then (.error .invalidDescriptor, before) else"),
        ("skip-invalidation", "| .invalidate => (.ok (), { before with invalidated := true })",
         "| .invalidate => (.ok (), before)"),
        ("discard-release-fault", "(result.mapError Fault.arguments, { before with memory })\n  | .invalidate",
         "(.ok (), { before with memory })\n  | .invalidate"),
        ("use-unchecked-callback", "| .lastValue => execute items external allocator (last ownership before) expressionDeinitCode before",
         "| .lastValue => rest.release .lastValue ownership before"),
    ):
        if source.count(before) != 1:
            raise ValueError("ambiguous destructor mutation: " + name)
        records.append(mutation_check(output, "destructor-" + name, source.replace(before, after), False, env, lean))
    original = extraction.SOURCE.read_bytes()
    variants = [("destructor-source-unchanged", original, True)]
    variants += [("destructor-source-" + name, change_body(original, before, after), False)
                 for name, (before, after) in MUTATIONS.items()]
    for name, native, accepted in variants:
        parts = {**sources, "ExpressionDeinitProgram.lean": without_imports(extraction.extract(native).decode())}
        records.append(mutation_check(output, name, assembled(parts), accepted, env, lean))
    for record in records:
        diagnostic = (output / (record["name"] + ".stdout")).read_text()
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant|failed to synthesize",
                     diagnostic, re.I):
            raise ValueError("destructor control hit a resource, syntax or elaboration failure: " + record["name"])
        if not record["expectedAcceptance"] and not re.search(
                r"unsolved goals|Type mismatch|Tactic [^\n]*(?:failed|proved)|Dependent elimination failed|Application type mismatch",
                diagnostic, re.I):
            raise ValueError("destructor negative control has no semantic proof failure: " + record["name"])
    return records
