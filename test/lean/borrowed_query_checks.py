#!/usr/bin/env python3
"""Audit accepted source-bound argument queries into the complete caller.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import re

import extract_storage
from check_argument_memory import ROOT, NS
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

QUERY = NS + "Normalization.OwnedCall.BorrowedQuery."
MODULE = "Compiler.Extraction.InternerBorrowedQueryTests"
CLAIMS = [QUERY + name for name in (
    "typed_sound", "contents_sound", "slice_sound", "slice_complete", "accepted", "accepted_good",
    "resident_accepted", "operation_verified")]
CLAIMS += [QUERY + "Tests." + name for name in (
    "slice_accepted", "empty_without_sentinel", "wrong_owner_rejected", "wrong_address_rejected",
    "wrong_block_rejected", "missing_storage_rejected", "stack_storage_rejected", "readonly_storage_rejected",
    "wrong_extent_rejected", "stale_contents_rejected", "last_element_rejected", "uninitialized_rejected",
    "query_accepted", "query_misses", "absent_graph_rejected", "malformed_query_rejected", "unbacked_query_rejected",
    "inserted_query_accepted", "produced_valid", "produced_graph", "inserted_query_good", "contracts",
    "production_contract", "success_observation", "failure_observation", "zero_budget_without_swaps",
    "unsorted_query_accepted", "semantic_fault_retained", "success_verified", "failure_verified")]


def bindings():
    if extract_storage.extract(extract_storage.SOURCE.read_bytes()) != extract_storage.OUTPUT.read_bytes():
        raise ValueError("stale borrowed query storage extraction")
    return {"generatedModule": str(extract_storage.OUTPUT.relative_to(ROOT)),
            "productionReader": "ExpressionClasses.operationArguments",
            "acceptedObservation": "exact returned full-array address and every typed ID in the reached world",
            "validatorInNativeCompiler": False,
            "boundary": "Valid world and graph callback contracts remain premises; native observation binding, universal admission and recursive preservation remain open."}


def audit(claims):
    owned = NS + "Normalization.OwnedCall."
    required = {
        QUERY + "slice_sound": {QUERY + "typed_sound", QUERY + "contents_sound", owned + "Insertion.ownsArguments_sound",
            "Compiler.ZigAir.Memory.load", NS + "Owned", "Compiler.ZigAir.Memory.WordArray.Represents"},
        QUERY + "accepted_good": {QUERY + "accepted", QUERY + "slice_sound", "Compiler.Extraction.Interner.representativeReads",
            "Compiler.Extraction.Storage.operationProgram"},
        QUERY + "resident_accepted": {QUERY + "slice_complete", "Compiler.Extraction.Storage.operation_found", NS + "Related"},
        QUERY + "operation_verified": {QUERY + "accepted_good", owned + "Recursive.BorrowedConstructor.operation_verified",
            owned + "ConstructorFrame.operation_verified", "Compiler.Extraction.Interner.Queries.queries",
            owned + "Semantic.production_verified", NS + "Normalization.Valid.cleanup"},
        QUERY + "Tests.inserted_query_good": {QUERY + "accepted_good", QUERY + "Tests.inserted_query_accepted",
            owned + "Insertion.CallerTests.find_closed"},
        QUERY + "Tests.production_contract": {QUERY + "operation_verified", QUERY + "Tests.inserted_query_accepted",
            owned + "Insertion.graph_contracts", owned + "Insertion.CallerTests.find_closed"},
        QUERY + "Tests.success_verified": {QUERY + "Tests.production_contract", QUERY + "Tests.success_observation"},
        QUERY + "Tests.failure_verified": {QUERY + "Tests.production_contract", QUERY + "Tests.failure_observation"},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError("borrowed query lost dependencies: " + name + ": " + ", ".join(sorted(needed - claims[name])))
    return {"checkedDependencies": sorted(required), "acceptedBorrowedQueryMemoryVerified": True,
            "insertionQueryCallerCompositionVerified": True, "nativeObservationBindingVerified": False,
            "universalNativeAdmissionVerified": False, "completeRecursiveConstructorsVerified": False}


def controls(output, env, lean):
    directory = ROOT / "lean/Compiler/Extraction"
    imports = ("import Compiler.Extraction.InternerBorrowedConstructor\n"
               "import Compiler.Extraction.InternerQueries\n"
               "import Compiler.Extraction.InternerInsertionValidity\n"
               "import Compiler.Extraction.RepresentativeOperationTests\n")
    model = without_imports((directory / "InternerBorrowedQuery.lean").read_text())
    # Caller fixtures now import the native-query bridge. Use its independent
    # native-memory fixtures here to avoid importing the unchanged checker into
    # a mutation. The full caller fixture remains audited and freshly replayed.
    tests = "\n".join(without_imports((directory / name).read_text()) for name in
                      ("RepresentativeBorrowedQuery.lean", "RepresentativeBorrowedQueryTests.lean"))
    source = imports + model + tests
    records = [mutation_check(output, "borrowed-query-unchanged", source, True, env, lean)]
    for name, before, after in (
        ("ignore-owner", "Insertion.ownsArguments allocator slice state.heap && typed slice state.memory", "true && typed slice state.memory"),
        ("ignore-storage", "&& typed slice state.memory && contents slice state.memory", "&& true && contents slice state.memory"),
        ("ignore-contents", "&& contents slice state.memory\n", "&& true\n"),
        ("skip-last-element", "(List.range slice.items.length).all", "(List.range (slice.items.length - 1)).all"),
        ("read-first-element", "| some id => match Compiler.ZigAir.Memory.load state ((view slice).pointer index) with",
         "| some id => match Compiler.ZigAir.Memory.load state ((view slice).pointer 0) with"),
        ("ignore-stack", "&& cell.writable && !cell.stack", "&& cell.writable && true"),
        ("ignore-extent", "decide (cell.type = .array slice.items.length word) && cell.writable", "true && cell.writable"),
        ("bypass-admission", "if checkSlice allocator slice before.memory then", "if true then"),
        ("fault-is-miss", "let found ← ((Interner.representativeReads before.graph).operation id opcode).mapError Rejection.query",
         "let found := ((Interner.representativeReads before.graph).operation id opcode).toOption.flatten"),
    ):
        if model.count(before) != 1:
            raise ValueError("ambiguous borrowed query mutation: " + name)
        records.append(mutation_check(output, "borrowed-query-" + name, imports + model.replace(before, after) + tests, False, env, lean))
    for record in records:
        diagnostic = (output / (record["name"] + ".stdout")).read_text()
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant", diagnostic, re.I):
            raise ValueError("borrowed query control hit a resource or syntax failure: " + record["name"])
        if not record["expectedAcceptance"] and not re.search(
                r"error: (?:unsolved goals|Application type mismatch|Type mismatch|Tactic[^\n]*failed)", diagnostic):
            raise ValueError("borrowed query control lacks a semantic proof failure: " + record["name"])
    return records
