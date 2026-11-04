#!/usr/bin/env python3
"""Complete extracted interner callers under physical memory contracts.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import json
import re

import extract_interner
from extract_compiler import Unsupported
from check_argument_memory import ROOT, NS
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

MODULE = "Compiler.Extraction.InternerCallerTests"
CALLER = NS + "Normalization.OwnedCall.Caller."
FILES = ["InternerCaller" + suffix + ".lean" for suffix in (
    "Memory", "Cleanup", "Init", "Force", "Proofs", "Production", "Tests")]
CLAIMS = [CALLER + name for name in (
    "owned_execution", "force_owned_execution", "cleanup_lookup", "finish_canClose", "invoke_verified",
    "initialize_graph", "initialize_verified", "publish_post", "force_owned_split", "force_owned_ready",
    "find_ready", "force_ready", "Verified.closed", "find_verified", "force_verified", "production_verified")]
CLAIMS += [CALLER + "Tests." + name for name in (
    "find_cache_hit_releases_temporary", "find_nested_failure", "capacity_before_initialization",
    "validation_before_initialization", "force_cache_hit_releases_temporary", "force_publication_failure",
    "force_publication_success", "nondeterministic_skips_cache_and_simplification", "ordinary_query_error_cleans",
    "semantic_query_error_retains", "scratch_hit_no_owned_free", "duplicate_failure_after_lookup",
    "initializer_failure_precedes_cache_hit", "initialization_fault_retains_provisional", "caller_contract",
    "find_contract", "force_contract", "production_nested_failure", "production_force_failure")]


def bindings():
    source = extract_interner.SOURCE.read_bytes()
    if extract_interner.extract(source) != extract_interner.OUTPUT.read_bytes():
        raise ValueError("complete interner caller extraction is stale")
    controls = []
    for name, before, after in (
        ("capacity-guard-removed", b"if (self.representatives.items.len >= self.idLimit())\n            return error.ExpressionCapacity;", b""),
        ("force-validation-removed", b"_ = try self.representative(id);", b""),
        ("force-cleanup-removed", b"defer if (owned) self.allocator.free(normalized);", b""),
        ("force-handoff-removed", b"try self.publishOwned(key, id);\n        owned = false;", b"try self.publishOwned(key, id);"),
    ):
        if before not in source:
            raise ValueError("complete caller source mutation lost its target: " + name)
        try:
            extract_interner.extract(source.replace(before, after))
        except Unsupported as error:
            controls.append({"name": name, "status": "passed", "admitted": False, "expectedAdmission": False, "reason": str(error)})
        else:
            raise ValueError("unmodeled caller change was admitted: " + name)
    return {"controls": controls, "entryPoints": ["ExpressionClasses.find", "ExpressionClasses.forceEqual"],
            "boundary": "Complete extracted control with physical normalization and cleanup; graph implementation and read-only query refinement remain compiler obligations."}


def audit(output):
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    owned = NS + "Normalization.OwnedCall."
    normalization = NS + "Normalization."
    required = {
        CALLER + "production_verified": {CALLER + n for n in (
            "find_ready", "force_ready", "invoke_verified", "Verified", "Queries", "execution", "initLookup")}
            | {owned + n for n in ("Contracts", "body_ready", "finish_ready", "finish_semantic", "key_arguments")}
            | {normalization + n for n in ("caller_buffer", "init_refines", "take_refines", "deinit_refines")}
            | {"Compiler.Extraction.Interner." + n for n in ("FindCode.controlRun", "ForceCode.controlRun", "ForceCode.controlOwned")},
        CALLER + "initialize_verified": {normalization + "normalized_projection", normalization + "init_refines"},
        CALLER + "force_owned_ready": {CALLER + "publish_post", owned + "key_arguments", normalization + "take_refines"},
        CALLER + "Tests.production_nested_failure": {CALLER + "production_verified", CALLER + "Tests.find_nested_failure",
            owned + "nested_held", owned + "Tests.callbacks_contracts"},
        CALLER + "Tests.production_force_failure": {CALLER + "production_verified", CALLER + "Tests.force_publication_failure",
            owned + "Tests.callbacks_contracts"},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError("complete caller composition lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return {"checkedDependencies": sorted(required), "obligation": "normalization.recursiveBridge",
            "completeCallerControlMemoryVerified": True, "recursiveMemoryBridgeVerified": False,
            "pendingObligations": ["production graph callback memory/ownership contracts", "native read-only query and graph observation refinement",
                                   "same complete execution in ScopedRecursive preservation", "completed native recursive execution binding"]}


def controls(output, env, lean):
    imports = "import Compiler.Extraction.InternerOwnedTests\nimport Compiler.Extraction.InternerScopeTests\n"
    source = "\n".join(without_imports((ROOT / "lean/Compiler/Extraction" / name).read_text()) for name in FILES)
    model = without_imports((ROOT / "lean/Compiler/Extraction" / FILES[0]).read_text())
    records = [mutation_check(output, "interner-caller-unchanged", imports + source, True, env, lean)]
    tests = without_imports((ROOT / "lean/Compiler/Extraction" / FILES[-1]).read_text())
    marker = "theorem caller_contract "
    if tests.count(marker) != 1:
        raise ValueError("complete caller mutation fixture boundary changed")
    # Retain every general refinement proof and concrete path fixture. Leave
    # the final production-theorem instantiations to unchanged/fresh replay:
    # after a mutant breaks the general proof, elaborating those large concrete
    # attachments can exhaust Lean before reporting their dependent failure.
    paths = tests.split(marker)[0] + "end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Tests\n"
    focused = source.replace(tests, paths, 1)
    records.append(mutation_check(output, "interner-caller-paths-unchanged", imports + focused, True, env, lean))
    for name, before, after in (
        ("capacity-bypass", "atCapacity := q.atCapacity", "atCapacity := fun _ => false"),
        ("determinism-bypass", "deterministic := q.deterministic", "deterministic := fun _ => .ok true"),
        ("validation-bypass", "q.validate id item values", "(fun _ _ => .ok ()) id item values"),
        ("skip-cleanup", "finish external allocator result reached", "(result, reached)"),
        ("lose-initialization-effects", "let world := { before.world with memory }", "let world := before.world"),
        ("detach-before-take", "lookup := some handle", "lookup := some { handle with owned := none }"),
        ("wrong-initialized-values", "(.ok handle.values,", "(.ok request.arguments,"),
        ("disable-commutativity", "allocator commutative source buffer request.arguments", "allocator false source buffer request.arguments"),
        ("alias-scratch", "allocator commutative source buffer request.arguments", "allocator commutative source source request.arguments"),
        ("reverse-force-arguments", "q.validate id item values", "q.validate id item values.reverse"),
        ("initialize-before-capacity",
         "Interner.findCode.controlRun (execution external budget allocator p q source buffer) request",
         "do let _ ← initLookup external budget allocator source buffer request; Interner.findCode.controlRun (execution external budget allocator p q source buffer) request"),
        ("force-extra-query",
         "Interner.forceCode.controlRun (execution external budget allocator p q source buffer) q.validate id item values",
         "do let _ ← (execution external budget allocator p q source buffer).lift (q.deterministic item); Interner.forceCode.controlRun (execution external budget allocator p q source buffer) q.validate id item values"),
    ):
        if model.count(before) != 1:
            raise ValueError("ambiguous complete caller mutation: " + name)
        mutated = imports + focused.replace(model, model.replace(before, after), 1)
        records.append(mutation_check(output, "interner-caller-" + name, mutated, False, env, lean))
    for record in records:
        diagnostic = (output / (record["name"] + ".stdout")).read_text()
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant", diagnostic, re.I):
            raise ValueError("complete caller control hit a resource or syntax failure: " + record["name"])
        if not record["expectedAcceptance"] and not re.search(
                r"error: (?:unsolved goals|Application type mismatch|Type mismatch|Tactic[^\n]*failed)", diagnostic):
            raise ValueError("complete caller control lacks a semantic proof failure: " + record["name"])
    return records
