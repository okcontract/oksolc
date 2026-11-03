#!/usr/bin/env python3
"""Check universal dispatcher effects and physical preservation contracts.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import json
import re

from check_argument_memory import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
from physical_dispatch_checks import RECURSIVE

MODULE = "Compiler.Extraction.InternerPhysicalDispatchPreservationTests"
EFFECTS = "Compiler.Extraction.Dispatch.Effects."
CLAIMS = [EFFECTS + name for name in (
    "read", "arithmetic", "add_word", "sub_word", "or_next", "let_related", "double_iszero", "drop_repeated",
    "apply_replacement", "reassociate", "alternating_build", "alternating_search", "alternating", "signextend_mask",
    "opposite_net", "opposite", "shift_mask", "shift_product", "constant_stage", "unary_stage", "evm_stage",
    "binary_stage", "simplify_options", "simplify")]
CLAIMS += [RECURSIVE + name for name in (
    "keeps_bind", "constructors_keep", "simplify_borrows", "projects_at_bind", "projects_bind", "ProjectsAt.safe", "Projects.safe", "ProjectsAt.safe_cursor", "simplify_verified_cursor", "simplify_verified")]
CLAIMS += ["Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Semantic.Ensures.cursor_iff"]
CLAIMS += [RECURSIVE + "PreservationTests." + name for name in (
    "counted_projects", "outer_held", "coupled", "logical_sound", "all_depths_verified", "success_observation",
    "success_borrows", "cutoff_retains_effects", "ordinary_failure_borrows", "ordinary_failure_effects",
    "changed_result_rejected", "changed_graph_rejected", "advance_projects", "cursor_bind_projects",
    "cursor_success", "cursor_oom", "cursor_exhaustion", "cursor_rewind_rejected",
    "cursor_wrong_result_rejected", "cursor_changed_read_rejected", "cursor_graph_fields",
    "advance_projects_held", "advancing_raw_graph_rejected", "advancing_success_words")]


def audit(output):
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    return audit_claims(claims)


def audit_claims(claims):
    required = {
        EFFECTS + "simplify_options": {EFFECTS + name for name in (
            "simplify_options_operands", "logical_operands", "constant_stage", "unary_stage_operands",
            "evm_stage_operands", "binary_stage_operands", "let_related", "bind", "lift",
            "apply_replacement", "drop_repeated", "reassociate", "alternating_operands", "signextend_mask_operands",
            "opposite", "shift_mask", "shift_product_operands")},
        **{EFFECTS + name: {EFFECTS + name + "_operands", EFFECTS + "logical_operands"} for name in (
            "alternating_build", "alternating_search", "alternating", "signextend_mask", "shift_product",
            "unary_stage", "evm_stage", "binary_stage")},
        RECURSIVE + "projects_bind": {RECURSIVE + "projects_at_bind"},
        RECURSIVE + "Projects.safe": {RECURSIVE + "ProjectsAt.safe"},
        RECURSIVE + "PreservationTests.cursor_bind_projects": {RECURSIVE + "projects_at_bind",
            RECURSIVE + "PreservationTests.advance_projects", RECURSIVE + "cursorGraph"},
        RECURSIVE + "simplify_borrows": {RECURSIVE + "keeping", RECURSIVE + "keeps_bind", EFFECTS + "simplify",
            RECURSIVE + "callbacks", RECURSIVE + "constructors"},
        RECURSIVE + "ProjectsAt.safe_cursor": {RECURSIVE + "ProjectsAt.safe", RECURSIVE + "cursorGraph",
            "Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Semantic.Ensures.cursor_iff"},
        RECURSIVE + "simplify_verified_cursor": {RECURSIVE + "projectionAt", RECURSIVE + "projects_at_bind", RECURSIVE + "ProjectsAt.safe_cursor",
            EFFECTS + "simplify", "Compiler.Extraction.Dispatch.default_key_simplify_safe", RECURSIVE + "callbacks"},
        RECURSIVE + "simplify_verified": {RECURSIVE + "simplify_verified_cursor"},
        RECURSIVE + "PreservationTests.advancing_success_words": {RECURSIVE + "ProjectsAt.safe_cursor", RECURSIVE + "PreservationTests.advance_projects"},
        RECURSIVE + "PreservationTests.all_depths_verified": {RECURSIVE + "simplify_verified",
            RECURSIVE + "PreservationTests.counted_projects", "Compiler.Extraction.Recursive.unfold_safe",
            "Compiler.Extraction.Memory.Arguments.Normalization.Tests.full_contract"},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError("dispatcher preservation lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return {"checkedDependencies": sorted(required), "physicalDispatcherPreservationVerified": True,
            "physicalRecursivePreservationVerified": False,
            "pendingObligations": ["native recursive constructor simulation and argument preparation",
                                   "complete physical caller recursion induction and native graph/query refinement"]}


def controls(output, env, lean):
    directory = ROOT / "lean/Compiler/Extraction"
    imports = "import Compiler.Extraction.InternerPhysicalDispatchTests\nimport Compiler.Extraction.DispatchDefaultProofs\nimport Lean\n"
    effects = without_imports((directory / "DispatchEffects.lean").read_text())
    physical = without_imports((directory / "InternerPhysicalDispatchPreservation.lean").read_text())
    tests = without_imports((directory / "InternerPhysicalDispatchPreservationTests.lean").read_text())
    # A transitive test import already includes DispatchEffects. Recheck its
    # complete proof body under a fresh namespace, and make the copied physical
    # clients consume that copy rather than the imported effect laws.
    effects = effects.replace("namespace Compiler.Extraction.Dispatch\n",
        "namespace Compiler.Extraction.DispatchPreservationMutation\nopen Compiler.Extraction.Dispatch\n")
    effects = effects.replace("end Compiler.Extraction.Dispatch\n", "end Compiler.Extraction.DispatchPreservationMutation\n")
    physical = physical.replace("Dispatch.Effects", "DispatchPreservationMutation.Effects")
    model = effects + physical
    records = [mutation_check(output, "dispatch-preservation-unchanged", imports + model + tests, True, env, lean)]
    for name, before, after in (
        ("forget-graph", "observe (physical before).2 = (logical (observe before)).2", "True"),
        ("forget-result", "(physical before).1 = (logical (observe before)).1.mapError Fault.language", "True"),
        ("forget-borrow", "predicate (physical before).2 ∧", "True ∧"),
        ("success-only-borrow", "ordinary (action before).1 = true", "(∃ value, (action before).1 = .ok value)"),
        ("reclassify-errors", "(logical (observe before)).1.mapError Fault.language",
         "(logical (observe before)).1.mapError (fun _ => Fault.language .outOfMemory)"),
        ("one-continuation-value", "related left right → (∀ value, related (nextLeft value) (nextRight value))",
         "related left right → (∃ value, related (nextLeft value) (nextRight value))"),
    ):
        if model.count(before) != 1:
            raise ValueError("ambiguous dispatcher preservation mutation: " + name)
        records.append(mutation_check(output, "dispatch-preservation-" + name,
                                      imports + model.replace(before, after) + tests, False, env, lean))
    for name, before, after in (
        ("rewind-cursor", "allocationCursor := cursor world", "allocationCursor := world.graph.allocationCursor"),
        ("erase-read", "{ world.graph with allocationCursor", "{ world.graph with read := fun _ => none, allocationCursor"),
        ("erase-table", "{ world.graph with allocationCursor", "{ world.graph with table := fun _ => none, allocationCursor"),
        ("erase-representatives", "{ world.graph with allocationCursor", "{ world.graph with representatives := none, allocationCursor"),
    ):
        if model.count(before) != 1:
            raise ValueError("ambiguous cursor observation mutation: " + name)
        records.append(mutation_check(output, "dispatch-preservation-" + name,
                                      imports + model.replace(before, after) + tests, False, env, lean))
    for record in records:
        diagnostic = (output / (record["name"] + ".stdout")).read_text()
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant|already been declared", diagnostic, re.I):
            raise ValueError("dispatcher preservation control hit a resource or syntax failure: " + record["name"])
        if not record["expectedAcceptance"] and not re.search(
                r"(?:error: (?:unsolved goals|Application type mismatch|Type mismatch|Tactic[^\n]*failed)|error: Invalid projection)", diagnostic):
            raise ValueError("dispatcher preservation control lacks a semantic proof failure: " + record["name"])
    return records
