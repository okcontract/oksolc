#!/usr/bin/env python3
"""Check the admitted publication body in complete physical interner callers.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import json
import re

from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

MODULE = "Compiler.Extraction.InternerPublicationTests"
OWNED = "Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall."
NS = OWNED + "Publication."
CLAIMS = [NS + name for name in (
    "accepted_body", "ordinary_admitted", "admit_sound", "admit_complete", "external_admitted", "completion_held",
    "publish_held", "publish_semantics", "completed_projection", "publish_linked", "graph_contracts", "production_verified")]
CLAIMS += [NS + "Tests." + name for name in (
    "insertion_memory", "insertion_semantics", "logical_sound", "coupled", "initial_good", "graph_valid", "production_contract",
    "find_success", "find_oom_cleanup", "force_success", "replacement_allocation", "force_cache_hit",
    "replacement_prepared", "replacement_success", "replacement_oom", "source_alias_rejected", "incoming_alias_rejected",
    "absent_old_rejected", "byte_owner_rejected", "admission_reasons", "empty_sentinel_admitted", "declared_contract_admitted", "force_tables", "force_projection", "replacement_tables", "replacement_projection", "source_preserved",
    "find_closed", "success_verified")]


def audit(output):
    claims = {claim["theorem"]: set(claim["dependencies"])
              for claim in json.loads((output / "audit.json").read_bytes())["claims"]}
    physical = "Compiler.Extraction.OwnedKeys.Physical."
    required = {
        NS + "accepted_body": {NS + "admit", NS + "body", physical + "run"},
        NS + "ordinary_admitted": {NS + "admit", OWNED + "ordinary"},
        NS + "admit_sound": {NS + "admit", NS + "Input", "Compiler.Extraction.Memory.SliceValid"},
        NS + "admit_complete": {NS + "admit", NS + "Input", "Compiler.Extraction.Memory.SliceValid"},
        NS + "publish_held": {NS + "ordinary_admitted", NS + "admit_sound", NS + "completion_held",
            physical + "run_local_spec", physical + "complete_local_verified"},
        NS + "publish_linked": {NS + "completed_projection", "Compiler.Extraction.OwnedKeys.view_store"},
        NS + "graph_contracts": {NS + "publish_held", NS + "publish_semantics", NS + "callbacks"},
        NS + "production_verified": {NS + "graph_contracts", NS + "external_admitted",
            OWNED + "Recursive.production_verified", OWNED + "Semantic.production_verified",
            OWNED + "Caller.initialize_verified", OWNED + "finish"},
        NS + "Tests.success_verified": {NS + "production_verified", NS + "Tests.find_success",
            NS + "Tests.logical_sound", OWNED + "Semantic.Verified.closed"},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError("publication caller lost checked dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return {"checkedDependencies": sorted(required), "physicalCallerPublicationContractsDerived": True,
            "nativePublicationAdmissionVerified": False, "nativeHashMapVerified": False,
            "physicalRecursivePreservationVerified": False,
            "remaining": ["native cache binding and universal admission", "global graph ownership invariants",
                          "native insertion, queries and recursive constructor simulation"]}


def controls(output, env, lean):
    directory = ROOT / "lean/Compiler/Extraction"
    imports = "import Compiler.Extraction.InternerPhysicalDispatchProductionTests\nimport Compiler.Extraction.OwnedKeysPhysicalTests\n"
    source = imports + "\n".join(without_imports((directory / name).read_text()) for name in (
        "InternerPublication.lean", "InternerPublicationProofs.lean", "InternerPublicationProduction.lean", "InternerPublicationTests.lean"))
    records = [mutation_check(output, "publication-caller-unchanged", source, True, env, lean)]
    for name, before, after in (
        ("reject-empty-sentinel", "if key.arguments.isEmpty then .ok ()", "if key.arguments.isEmpty then .error .oldOwnership"),
        ("allow-source-alias", "else if source.length ≠ 0 ∧ old.address = source.allocation then .error .sourceAlias",
         "else if False then .error .sourceAlias"),
        ("allow-incoming-alias", "else if old.address = owned.address then .error .incomingAlias",
         "else if False then .error .incomingAlias"),
        ("allow-wrong-descriptor", "if key.arguments != owned.items then .error .descriptor else",
         "if false then .error .descriptor else"),
        ("skip-old-ownership", "if owner == allocator && values == key.arguments then .ok () else .error .oldOwnership",
         "if true then .ok () else .error .oldOwnership"),
        ("accept-byte-owner", "      | _ => .error .oldOwnership",
         "      | some ⟨_, .bytes _⟩ => .ok ()\n      | _ => .error .oldOwnership"),
        ("discard-probe-effects", "(ok, ⟨state.effects.keys, reached⟩)", "(ok, state.effects)"),
        ("discard-owned-key", "effects := { execution.2.memory.effects with keys := execution.2.table }",
         "effects := execution.2.memory.effects"),
        ("discard-cache-projection", "{ before.graph with table := Cache.put equalityFields before.graph.table key id }",
         "before.graph"),
        ("use-seed-publication", "{ p with publish := publish hostProbe host allocator source }", "p"),
        ("treat-rejection-as-oom", "(.error (.language .safetyFault), before)", "(.error (.language .outOfMemory), before)"),
    ):
        if source.count(before) != 1:
            raise ValueError("ambiguous publication caller mutation: " + name)
        records.append(mutation_check(output, "publication-caller-" + name, source.replace(before, after), False, env, lean))
    for record in records:
        diagnostic = (output / (record["name"] + ".stdout")).read_text()
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant",
                     diagnostic, re.I):
            raise ValueError("publication caller control hit a resource or syntax failure: " + record["name"])
    return records
