#!/usr/bin/env python3
"""Source-bound owned interner continuation with reached-state deferred cleanup.
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

MODULE = "Compiler.Extraction.InternerOwnedTests"
OWNED = NS + "Normalization.OwnedCall."
FILES = ["InternerOwned" + suffix + ".lean" for suffix in (
    "Memory", "Contracts", "Cleanup", "Proofs", "Production", "Nested", "Tests")]
CLAIMS = [OWNED + name for name in (
    "graph_preserves_local", "insert_post", "miss_post", "deinit_detached", "cleanup_taken", "finish_taken", "finish_semantic",
    "key_arguments", "post_ready", "body_split", "body_ready", "finish_ready", "run_verified", "entry_verified", "production_verified",
    "represented_retained", "held_retained", "nested_held")]
CLAIMS += [OWNED + "Tests." + name for name in (
    "release_good", "callbacks_contracts", "nested_failure_cleanup", "publication_failure_cleanup",
    "publication_success_detached_alias", "insertion_success", "insertion_failure_handoff", "semantic_callback_retains_parent",
    "duplicate_oom_preserves_effects", "temporary_oom_no_defer", "preparation_fault_no_defer", "empty_nested_no_native_allocation",
    "caller_contract", "production_nested_contract", "production_nested_failure")]


def bindings():
    source = extract_interner.SOURCE.read_bytes()
    if extract_interner.extract(source) != extract_interner.OUTPUT.read_bytes():
        raise ValueError("owned interner control extraction is stale")
    controls = []
    for name, before, after in (
        ("omit-owned-cleanup", b"defer if (normalized_owned) self.allocator.free(normalized);", b""),
        ("publication-handoff-omitted", b"normalized_owned = false;\n                return simplified;", b"return simplified;"),
        ("insert-handoff-omitted", b"normalized_owned = false;\n        return self.insertOwned", b"return self.insertOwned"),
    ):
        if before not in source:
            raise ValueError("owned caller source mutation lost its target: " + name)
        try:
            extract_interner.extract(source.replace(before, after))
        except Unsupported as error:
            controls.append({"name": name, "status": "passed", "admitted": False, "expectedAdmission": False, "reason": str(error)})
        else:
            raise ValueError("unmodeled owned caller change was admitted: " + name)
    return {"controls": controls, "entryPoint": "ExpressionClasses.find owned continuation",
            "boundary": "Complete-body admission binds controlOwned/controlMiss and both handoff sites; cache-hit routing, forceEqual and concrete graph callback implementation remain separate."}


def audit(output):
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    required = {
        OWNED + "miss_post": {OWNED + n for n in ("Contracts", "graph", "handoff", "execution")}
            | {"Compiler.Extraction.Interner.FindCode.controlMiss", "Compiler.Extraction.Interner.findCode"},
        OWNED + "run_verified": {OWNED + n for n in ("body_ready", "finish_ready", "finish_semantic", "body_split", "miss_post", "CleanupPost", "key_arguments")}
            | {NS + "Normalization." + n for n in ("take_refines", "free_valid")},
        OWNED + "production_verified": {OWNED + n for n in ("entry_verified", "run_verified", "entry", "Contracts")}
            | {NS + "Normalization." + n for n in ("caller_buffer", "init_refines", "normalized_projection", "Admitted")}
            | {"Compiler.Extraction.Interner.FindCode.controlOwned"},
        OWNED + "nested_held": {OWNED + "nested", OWNED + "held_retained"}
            | {NS + "Normalization.continue_refines", NS + "Normalization.run"},
        OWNED + "Tests.production_nested_failure": {OWNED + "production_verified", OWNED + "nested_held",
            OWNED + "Tests.callbacks_contracts", OWNED + "Tests.nested_failure_cleanup"},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError("owned continuation lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return {"checkedDependencies": sorted(required), "obligation": "normalization.recursiveBridge",
            "ownedContinuationMemoryVerified": True, "recursiveMemoryBridgeVerified": False,
            "pendingObligations": ["production graph callback memory/ownership contracts", "same complete execution in ScopedRecursive preservation",
                                   "cache-hit/capacity/forceEqual integration", "completed native recursive execution binding"]}


def controls(output, env, lean):
    imports = "import Compiler.Extraction.NormalizationTraceTests\n"
    source = "\n".join(without_imports((ROOT / "lean/Compiler/Extraction" / name).read_text()) for name in FILES)
    records = [mutation_check(output, "owned-interner-unchanged", imports + source, True, env, lean)]
    for name, before, after in (
        ("lose-callback-world", "(result, { before with world })", "(result, before)"),
        ("replace-caller-handle", "(result, { before with world })", "(result, ⟨world, { lookup := none }⟩)"),
        ("wrong-callback-address", "action slice before.world", "action { slice with address := slice.address + 1 } before.world"),
        ("wrong-callback-key", "simplify := fun key => graph (p.simplify key)", "simplify := fun key => graph (p.simplify { key with arguments := [] })"),
        ("keep-old-allocator-effects", "let world := { before.world with memory }", "let world := before.world"),
        ("omit-handoff", "handedOff := true", "handedOff := false"),
        ("free-transferred-slice", "if before.scope.handedOff then deinit external allocator before else", "if false then deinit external allocator before else"),
        ("skip-owned-free", "let (result, memory) := free external allocator slice before.world.memory", "let (result, memory) := (Except.ok (), before.world.memory)"),
        ("keep-released-slice", "with slice := none", "with slice := some slice"),
        ("skip-deinit-invalidation", "with lookup := none", "with lookup := before.scope.lookup"),
        ("cleanup-semantic-fault", "if ordinary result then", "if true then"),
        ("lose-body-result", "| .ok () => (result, after)", "| .ok () => (.error (.language .outOfMemory), after)"),
    ):
        # Mutate the executable model only; statements and proof clients retain
        # their intended contracts and must expose the changed behavior.
        model = without_imports((ROOT / "lean/Compiler/Extraction" / FILES[0]).read_text())
        if model.count(before) != 1:
            raise ValueError("ambiguous owned continuation mutation: " + name)
        mutated = imports + source.replace(model, model.replace(before, after), 1)
        records.append(mutation_check(output, "owned-interner-" + name, mutated, False, env, lean))
    for record in records:
        diagnostic = (output / (record["name"] + ".stdout")).read_text()
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant", diagnostic, re.I):
            raise ValueError("owned continuation control hit a resource or syntax failure: " + record["name"])
        if not record["expectedAcceptance"] and not re.search(
                r"error: (?:unsolved goals|Application type mismatch|Type mismatch|Tactic[^\n]*failed)", diagnostic):
            raise ValueError("owned continuation control lacks a semantic proof failure: " + record["name"])
    return records
