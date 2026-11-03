#!/usr/bin/env python3
"""Check source-bound publication against the shared typed memory contracts.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import json
from pathlib import Path
import re
import sys

import check_argument_memory
import check_compiler
import check_word_swap
from check_word_swap import ROOT, lean_check, prove
from build_toolchain import digest, run, write_json
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
import extract_owned_keys

MODULE = "Compiler.Extraction.OwnedKeysPhysicalTests"
OWNED = "Compiler.Extraction.OwnedKeys."
NS = OWNED + "Physical."
CLAIMS = [name for name in check_compiler.CLAIMS if name.startswith(OWNED)]
CLAIMS += [OWNED + "Code." + name for name in ("finish_equation", "run_equation")]
CLAIMS += [NS + name for name in ("complete_local_verified", "complete_verified", "run_local_spec", "run_spec", "Completed.preserves", "run_preserves", "run_semantics")]
CLAIMS += [NS + "Tests." + name for name in (
    "initial_valid", "initial_live", "initial_unique", "incoming_fresh", "borrowed_apart", "complete_ownership",
    "replacement", "borrowed_contents", "oom", "wrong_allocator", "missing_typed_lifetime", "stack_rejected",
    "empty_sentinel", "new_entry", "omitted_release_leaks", "omitted_key_store_dangles")]


def inputs(caller=False):
    result = check_argument_memory.inputs()
    if caller:
        result.update(check_compiler.snapshot())
    for path in (extract_owned_keys.SOURCE, ROOT / "docs/compiler-verification-map.json",
                 ROOT / "docs/compiler-verification-boundary.md"):
        result[str(path.relative_to(ROOT))] = digest(path)
    return result


def audit(output, env, lean, module=MODULE, roots=CLAIMS):
    result = check_word_swap.audit(output, env, lean, module, roots)
    claims = {claim["theorem"]: set(claim["dependencies"])
              for claim in json.loads((output / "audit.json").read_bytes())["claims"]}
    memory = "Compiler.Extraction.Memory.Arguments."
    required = {
        OWNED + "Code.finish_equation": {OWNED + "Code.complete", OWNED + "logicalOperations"},
        OWNED + "Code.run_equation": {OWNED + "Code.execute", OWNED + "logicalOperations"},
        NS + "complete_verified": {OWNED + "publicationCode", OWNED + "Code.complete", NS + "operations",
            memory + "Normalization.free_valid", memory + "release_refines", NS + "Completed"},
        NS + "run_spec": {OWNED + "Code.execute", NS + "complete_local_verified", NS + "Probe"},
        NS + "run_preserves": {NS + "run_spec", NS + "Completed.preserves", OWNED + "after_live",
            OWNED + "store_unique", OWNED + "store_apart", OWNED + "after_frame"},
        NS + "run_semantics": {NS + "run_spec", OWNED + "after_semantics", OWNED + "view_store"},
        NS + "Tests.complete_ownership": {NS + "run_preserves", NS + "Tests.initial_valid", NS + "Tests.incoming_fresh"},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError("publication lost checked dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return {**result, "checkedDependencies": sorted(required)}


def controls(output, env, lean):
    directory = ROOT / "lean/Compiler/Extraction"
    source = "import Compiler.Extraction.OwnedKeysTests\nimport Compiler.Extraction.NormalizationMemoryContracts\n"
    source += "\n".join(without_imports((directory / name).read_text()) for name in (
        "OwnedKeysPhysical.lean", "OwnedKeysPhysicalTests.lean"))
    records = [mutation_check(output, "publication-unchanged", source, True, env, lean)]
    for name, before, after in (
        ("discard-probe-effects", "(ok, { before with memory := { before.memory with effects } })", "(ok, before)"),
        ("ignore-probe-oom", "(ok, { before with memory :=", "(true, { before with memory :="),
        ("omit-release", "Normalization.free external allocator owned before.memory", "(.ok (), before.memory)"),
        ("release-incoming", "Normalization.free external allocator owned before.memory",
         "Normalization.free external allocator ⟨1, owned.items⟩ before.memory"),
        ("discard-release-fault", "(result, { before with memory })", "(.ok (), { before with memory })"),
        ("omit-store", "{ before with table := store before.table key entry }", "before"),
        ("misclassify-oom", "outOfMemory := .outOfMemory", "outOfMemory := .release (.ownership .outOfMemory)"),
    ):
        if source.count(before) != 1:
            raise ValueError("ambiguous publication mutation: " + name)
        records.append(mutation_check(output, "publication-" + name, source.replace(before, after), False, env, lean))
    from lean_control_matrix import PendingControl
    for record in records:
        if isinstance(record, PendingControl):
            record.checked_by(output, check_control_diagnostic)
        else:
            check_control_diagnostic(output, record)
    return records


def check_control_diagnostic(output, record):
    diagnostic = (output / (record["name"] + ".stdout")).read_text()
    if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant",
                 diagnostic, re.I):
        raise ValueError("publication control hit a resource or syntax failure: " + record["name"])


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.owned-publication-physical.v1", "status": "failed", "jobs": 4,
              "proofScope": "sourceBoundPublicationUnderTypedReleaseAndFramedProbeContracts",
              "physicalPublicationVerified": False, "nativeHashMapVerified": False,
              "physicalCallerGraphContractsDischarged": False, "wholeCompilerVerified": False,
              "remaining": ["native bucket allocation, probing and entry-pointer refinement",
                            "complete physical caller graph and query integration", "physical recursive induction"]}
    module, roots = MODULE, CLAIMS
    caller = getattr(args, "caller", False)
    if caller:
        import publication_caller_checks
        module, roots = publication_caller_checks.MODULE, roots + publication_caller_checks.CLAIMS
        report.update(schema="oksolc.interner-publication-acceptance.v1",
                      proofScope="completePhysicalCallersWithAdmittedSourceBoundPublication",
                      physicalCallerPublicationContractsDerived=False, nativePublicationAdmissionVerified=False,
                      physicalRecursivePreservationVerified=False)
        report["remaining"] += ["universal native publication admission and graph ownership invariants"]
    try:
        report["inputs"], report["leanInputs"] = inputs(caller), lean_check.source_inputs()
        env, _, tools = lean_check.toolchain(args.lean_bin, 4)
        report["tools"] = tools
        for name, script in (("source-admission", "test_compiler_owned_keys.py"),
                             ("storage-admission", "test_compiler_storage.py"),
                             ("coverage-map", "check_verification_map.py"),
                             ("coverage-map-tests", "test_verification_map.py")):
            run(output, name, [sys.executable, "test/lean/" + script], cwd=ROOT, env=env)
        if caller:
            import production_normalization_checks
            report["normalizationSourceBinding"] = production_normalization_checks.bindings()
            for layer in ("interner", "constructor", "dispatch", "folding", "nested", "cache"):
                run(output, layer + "-admission", [sys.executable, "test/lean/test_compiler_" + layer + ".py"], cwd=ROOT, env=env)
        extracted = extract_owned_keys.extract(extract_owned_keys.SOURCE.read_bytes())
        if extracted != extract_owned_keys.OUTPUT.read_bytes():
            raise ValueError("owned-key extraction is stale")
        report["publicationProfileSha256"] = digest(extract_owned_keys.OUTPUT)
        run(output, "preflight", [tools["lake"]["path"], "build", module, "Compiler.Algebraic.Audit"], cwd=ROOT / "lean", env=env)
        report["audit"] = audit(output, env, tools["lean"]["path"], module, roots)
        report["controls"] = controls(output, env, tools["lean"]["path"])
        if caller:
            report["callerDependencies"] = publication_caller_checks.audit(output)
            report["callerControls"] = publication_caller_checks.controls(output, env, tools["lean"]["path"])
        proof, artifacts = prove.check_module(module, roots, lean_bin=args.lean_bin, jobs=4, fresh=True)
        directory = output / "proof"
        directory.mkdir()
        for name, data in artifacts.items():
            (directory / name).write_bytes(data)
        write_json(directory / "report.json", proof)
        report["proofReportSha256"] = digest(directory / "report.json")
        if (proof.get("status") != "passed" or proof.get("freshKernelReplay") is not True or
                proof.get("replayIncludesImports") is not True or proof.get("auditedDeclarations") != roots):
            raise ValueError("publication audit or fresh kernel replay failed")
        if inputs(caller) != report["inputs"] or lean_check.source_inputs() != report["leanInputs"]:
            raise ValueError("publication acceptance inputs changed")
        report.update(status="passed", physicalPublicationVerified=True, auditedDeclarations=len(roots))
        if caller:
            report.update(physicalCallerPublicationContractsDerived=True)
    finally:
        write_json(output / "report.json", report)
    print("Complete physical callers derive admitted publication contracts; native admission and graph refinement remain open." if caller else
          "Physical publication verified under framed probe and memory contracts; native hash map and caller integration remain open.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--caller", action="store_true", help="derive publication contracts in both complete physical callers")
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    check(parser.parse_args())
