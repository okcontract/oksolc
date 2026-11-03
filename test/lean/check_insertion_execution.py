#!/usr/bin/env python3
"""Check complete source-bound insertion control with effectful cleanup.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import json
from pathlib import Path
import re
import sys

import check_compiler
import check_word_swap
from check_word_swap import ROOT, lean_check, prove
from build_toolchain import digest, run, write_json
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
import extract_storage
from test_compiler_extraction import mutate
from test_compiler_storage import MUTATIONS

MODULE = "Compiler.Extraction.StorageExecutionTests"
NS = "Compiler.Extraction.Storage."
SEMANTIC = "Compiler.Extraction.Interner.InsertionExecution."
CLAIMS = [NS + name for name in (
    "Release.execute_state", "releaseAll_state", "Cleanup.execute_state", "Program.execute_condition",
    "insert_condition", "insert_execution_safe")]
CLAIMS += [SEMANTIC + name for name in ("project_safe", "verified")]
CLAIMS += [NS + "ExecutionTests." + name for name in (
    "deterministic_success", "nondeterministic_success", "capacity_cleanup", "duplicate_failure", "item_failure",
    "clone_failure", "append_failure", "publication_failure", "aliased_failure", "allocation_fault", "cleanup_fault",
    "cleanup_changes_later_allocation", "capacity_cleanup_fault", "semantic_execution", "success_words", "failures_restore")]


def inputs():
    result = check_compiler.snapshot()
    for name in ("docs/compiler-verification-map.json", "docs/compiler-verification-boundary.md",
                 "test/lean/assembly_item_layout.zig", "test/lean/assembly_item_fields.zig", "test/lean/interner_queries.zig",
                 "test/lean/constructor_rule_max_exponent.zig"):
        result[name] = digest(ROOT / name)
    return result


def audit(output, env, lean, module=MODULE, roots=CLAIMS):
    result = check_word_swap.audit(output, env, lean, module, roots)
    claims = {claim["theorem"]: set(claim["dependencies"])
              for claim in json.loads((output / "audit.json").read_bytes())["claims"]}
    required = {
        NS + "Program.execute_condition": {NS + "Program.execute", NS + "Program.condition", NS + "Cleanup.execute_state"},
        NS + "insert_execution_safe": {NS + "insertProgram", NS + "insert_condition", NS + "Program.execute_condition",
                                        NS + "SafeResult", NS + "InsertionPost"},
        SEMANTIC + "verified": {NS + "insert_execution_safe", SEMANTIC + "project_safe", SEMANTIC + "project",
                               "Compiler.Extraction.Interner.Invariant", "Compiler.Extraction.Interner.Stable"},
        NS + "ExecutionTests.success_words": {SEMANTIC + "verified", NS + "ExecutionTests.deterministic_success"},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError("insertion execution lost checked dependencies: " + name + ": " +
                             ", ".join(sorted(needed - claims[name])))
    return {**result, "checkedDependencies": sorted(required)}


def controls(output, env, lean):
    directory = ROOT / "lean/Compiler/Extraction"
    source = "import Compiler.Extraction.ObservedStorageTests\n" + "\n".join(
        without_imports((directory / name).read_text()) for name in (
            "StorageExecution.lean", "StorageExecutionProofs.lean", "InsertionExecution.lean", "StorageExecutionTests.lean"))
    records = [mutation_check(output, "insertion-unchanged", source, True, env, lean)]
    for name, before, after in (
        ("discard-release-effects", "((.ok (), release.run state), reached)", "((.ok (), release.run state), effects)"),
        ("skip-release", "((.ok (), release.run state), reached)", "((.ok (), state), reached)"),
        ("lose-release-fault", "| .error fault => ((.error fault, state), reached)\n  | .ok ()",
         "| .error _ => ((.ok (), state), reached)\n  | .ok ()"),
        ("ignore-cleanup-flag", "if state.flag flag then release.execute", "if true then release.execute"),
        ("discard-body-effects", "let ((closed, final), effects) := cleanup.execute operations after reached",
         "let ((closed, final), effects) := cleanup.execute operations after effects"),
        ("skip-error-cleanup", "if errorOnly && (outcome == some .success || outcome == none) then ((.ok outcome, after), reached)",
         "if true then ((.ok outcome, after), reached)"),
        ("discard-allocation-effects", "next.execute input operations (action.success input state) reached",
         "next.execute input operations (action.success input state) effects"),
        ("allocation-fault-is-oom", "| .error fault => ((.error fault, state), reached)\n    | .ok false",
         "| .error _ => ((.ok (some .allocationFailure), state), reached)\n    | .ok false"),
    ):
        if source.count(before) != 1:
            raise ValueError("ambiguous insertion mutation: " + name)
        records.append(mutation_check(output, "insertion-" + name, source.replace(before, after), False, env, lean))

    # Re-extract actual source mutations and check the complete ownership
    # condition, not merely a changed digest or a parser rejection.
    original = extract_storage.SOURCE.read_bytes()
    variants = [("source-unchanged", original, True)]
    variants += [("source-" + name, mutate(original, before, after), False)
                 for name, (before, after, _) in MUTATIONS.items()]
    for name, native, accepted in variants:
        generated = extract_storage.extract(native).decode()
        body = generated.split("def insertProgram : Program :=\n", 1)[1].split("\ndef representativeProgram", 1)[0]
        candidate = ("import Compiler.Extraction.StorageExecutionProofs\n"
                     "namespace Compiler.Extraction.Storage\n"
                     "def mutant : Program :=\n" + body + "\n"
                     "example : mutant.condition ⟨true, true, fun _ => false⟩ "
                     "(InsertionPost ⟨true, true, fun _ => false⟩) {} ∧ "
                     "mutant.condition ⟨false, true, fun _ => false⟩ "
                     "(InsertionPost ⟨false, true, fun _ => false⟩) {} := by\n"
                     "  simp [mutant, Program.condition, InsertionPost, Test.eval, Command.allocation, Command.success,\n"
                     "    State.setFlag, State.move, State.argument, Cleanup.run, Release.run, SafeResult, Published, Released] <;> decide\n"
                     "end Compiler.Extraction.Storage\n")
        records.append(mutation_check(output, name, candidate, accepted, env, lean))
    for record in records:
        diagnostic = (output / (record["name"] + ".stdout")).read_text()
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant|failed to synthesize",
                     diagnostic, re.I):
            raise ValueError("insertion control hit a resource, syntax or elaboration failure: " + record["name"])
        if record["name"] not in {"insertion-unchanged", "source-unchanged"} and not re.search(
                r"unsolved goals|Type mismatch|Tactic [^\n]*(?:failed|proved)|Dependent elimination failed|Application type mismatch",
                diagnostic, re.I):
            raise ValueError("insertion negative control has no semantic proof failure: " + record["name"])
    return records


def check(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.insertion-execution-acceptance.v1", "status": "failed", "jobs": 4,
              "proofScope": "sourceBoundInsertionControlAndGraphProjectionWithEffectfulCleanup",
              "completeInsertionControlVerified": False, "nativeInsertionMemoryVerified": False,
              "physicalCallerInsertionContractsDerived": False, "wholeCompilerVerified": False,
              "remaining": ["native clone, vector, hash-map and typed-memory refinement",
                            "complete physical caller insertion attachment", "recursive constructor simulation and induction"]}
    module, roots = MODULE, CLAIMS
    queries = getattr(args, "queries", False)
    caller = getattr(args, "caller", False) or queries
    item_creation = getattr(args, "item_creation", False) or caller
    clone_insertion = getattr(args, "clone_insertion", False) or item_creation
    item_lifetime = getattr(args, "item_lifetime", False) or clone_insertion
    payload_insertion = getattr(args, "payload_insertion", False) or item_lifetime
    payload = getattr(args, "payload", False) or payload_insertion
    destructor = getattr(args, "destructor", False) or payload
    if destructor:
        import expression_deinit_checks
        module, roots = expression_deinit_checks.MODULE, roots + expression_deinit_checks.CLAIMS
        report.update(schema="oksolc.insertion-destructor-acceptance.v1",
                      proofScope="sourceBoundInsertionControlWithTypedArgumentRollback",
                      sourceBoundArgumentDestructionVerified=False, nativeItemDestructionVerified=False,
                      universalRollbackAdmissionVerified=False)
        report["remaining"] += ["native item destruction, allocation death and separation", "universal reached rollback descriptor admission"]
    if payload:
        import assembly_item_deinit_checks
        import check_argument_memory
        module = assembly_item_deinit_checks.MODULE
        roots += check_argument_memory.CLAIMS + assembly_item_deinit_checks.CLAIMS
        report.update(schema="oksolc.item-payload-destructor-acceptance.v1",
                      proofScope="sourceBoundItemPayloadCleanupAndInsertionArgumentCleanup",
                      sourceBoundPayloadDestructionVerified=False, payloadCallbackIntegrated=False,
                      nativeDescriptorProjectionVerified=False, itemAllocationDestructionVerified=False)
        report["remaining"] += ["attach payload cleanup to the effectful expression destructor",
                                "native optional-field descriptor projection"]
    if payload_insertion:
        import expression_payload_checks
        module, roots = expression_payload_checks.MODULE, roots + expression_payload_checks.CLAIMS
        report.update(schema="oksolc.payload-insertion-acceptance.v1",
                      proofScope="sourceBoundInsertionRollbackWithPayloadAndArgumentMemory")
        report["remaining"].remove("attach payload cleanup to the effectful expression destructor")
    if item_lifetime:
        import expression_lifetime_checks
        import capture_item_layout
        import capture_item_fields
        module, roots = expression_lifetime_checks.MODULE, roots + expression_lifetime_checks.CLAIMS
        report.update(schema="oksolc.expression-lifetime-acceptance.v1",
                      proofScope="sourceBoundInsertionRollbackWithPayloadItemAndArgumentLifetimes",
                      completeExpressionLifetimeVerified=False)
        report["remaining"].remove("native item destruction, allocation death and separation")
        report["remaining"] += ["native item fields, initialization and ownership construction",
                                "nominal allocation layout outside the captured native profiles"]
    if clone_insertion:
        import assembly_clone_physical_checks
        module, roots = assembly_clone_physical_checks.MODULE, roots + assembly_clone_physical_checks.CLAIMS
        report.update(schema="oksolc.clone-insertion-acceptance.v1",
                      proofScope="sourceBoundCloneAndInsertionRollbackUnderTypedAllocationCopyReleaseContracts",
                      sourceBoundCloneVerified=False, cloneSuppliesPayloadOwnership=False,
                      nativeByteCopyImplementationVerified=False, nativeFieldAssignmentVerified=False,
                      nativeItemCreationVerified=False)
        report["remaining"].remove("native clone, vector, hash-map and typed-memory refinement")
        report["remaining"] += ["native clone field projection/assignment and vector/hash-map memory refinement"]
    if item_creation:
        import assembly_item_creation_checks
        module, roots = assembly_item_creation_checks.MODULE, roots + assembly_item_creation_checks.CLAIMS
        report.update(schema="oksolc.item-creation-insertion-acceptance.v1",
                      proofScope="sourceBoundCreationCloneAndInsertionRollbackUnderTypedHostContracts",
                      itemCreationCallbackIntegrated=False, creationSuppliesObjectOwnership=False,
                      cloneResultAssignmentIntegrated=False, installedCloneAppendQueriesIntegrated=False)
        report["remaining"].remove("native item fields, initialization and ownership construction")
        report["remaining"] += ["initial native source-field and pointee correspondence across recursive callers and universal source caller admission"]
    if caller:
        import insertion_caller_checks
        import publication_caller_checks
        module = insertion_caller_checks.MODULE
        roots = list(dict.fromkeys(roots + publication_caller_checks.CLAIMS + insertion_caller_checks.CLAIMS))
        report.update(schema="oksolc.physical-insertion-caller-acceptance.v1",
                      proofScope="admittedSourceBoundPhysicalCallersWithConcreteInsertionAndPublication",
                      physicalCallerPublicationContractsDerived=False)
        report["remaining"].remove("complete physical caller insertion attachment")
        report["remaining"] += ["native descriptor/field/container binding and universal output admission"]
    if queries:
        import interner_query_checks
        import capture_interner_queries
        module = interner_query_checks.MODULE
        roots = list(dict.fromkeys(roots + interner_query_checks.CLAIMS))
        report.update(schema="oksolc.physical-query-caller-acceptance.v1",
                      proofScope="sourceBoundQueriesAndRepresentativeReadsInAdmittedPhysicalCallers",
                      sourceBoundCallerQueriesIntegrated=False, representativeReadContractsDerived=False,
                      terminalCallersWithoutRecursivePremisesVerified=False,
                      nativeQueryFieldRefinementVerified=False)
    try:
        report["inputs"] = inputs()
        env, _, tools = lean_check.toolchain(args.lean_bin, 4)
        report["tools"] = tools
        for name, script in (("source-admission", "test_compiler_storage.py"),
                             ("coverage-map", "check_verification_map.py"),
                             ("coverage-map-tests", "test_verification_map.py")):
            run(output, name, [sys.executable, "test/lean/" + script], cwd=ROOT, env=env)
        if extract_storage.extract(extract_storage.SOURCE.read_bytes()) != extract_storage.OUTPUT.read_bytes():
            raise ValueError("insertion extraction is stale")
        report["insertionProfileSha256"] = digest(extract_storage.OUTPUT)
        if queries:
            run(output, "query-admission", [sys.executable, "test/lean/test_compiler_queries.py"], cwd=ROOT, env=env)
            interner_query_checks.binding()
            report["queryProfileSha256"] = digest(interner_query_checks.extraction.OUTPUT)
        if caller:
            import extract_owned_keys
            import production_normalization_checks
            report["normalizationSourceBinding"] = production_normalization_checks.bindings()
            for layer in ("owned_keys", "interner", "constructor", "dispatch", "folding", "nested", "cache"):
                run(output, layer + "-admission", [sys.executable, "test/lean/test_compiler_" + layer + ".py"], cwd=ROOT, env=env)
            if extract_owned_keys.extract(extract_owned_keys.SOURCE.read_bytes()) != extract_owned_keys.OUTPUT.read_bytes():
                raise ValueError("owned-key extraction is stale")
            report["publicationProfileSha256"] = digest(extract_owned_keys.OUTPUT)
        if item_creation:
            import extract_constructor
            if not caller:
                run(output, "constructor-admission", [sys.executable, "test/lean/test_compiler_constructor.py"], cwd=ROOT, env=env)
            if extract_constructor.extract(extract_constructor.SOURCE.read_bytes(), extract_constructor.ITEMS.read_bytes(),
                                           extract_constructor.OPCODES.read_bytes()) != extract_constructor.OUTPUT.read_bytes():
                raise ValueError("complete item constructor extraction is stale")
            report["constructorProfileSha256"] = digest(extract_constructor.OUTPUT)
            if args.zig is None or args.zig_tree is None:
                raise ValueError("--item-creation requires --zig and --zig-tree for the native source binding")
            report["cloneQuerySourceBindings"] = assembly_item_creation_checks.assembly_clone_query_checks.bindings(args.zig_tree / "lib")
            run(output, "shift-input-admission", [sys.executable, "test/lean/test_rule_shift_input.py"], cwd=ROOT, env=env)
            run(output, "shift-input-native", [sys.executable, "test/lean/check_rule_shift_input.py", "--zig", args.zig,
                "--zig-lib-dir", args.zig_tree / "lib", "--output", output / "shift-input-native"], cwd=ROOT, env=env)
            report["shiftInputNativeControlsSha256"] = digest(output / "shift-input-native/report.json")
        if destructor:
            import extract_expression_deinit
            run(output, "destructor-admission", [sys.executable, "test/lean/test_expression_deinit.py"], cwd=ROOT, env=env)
            if extract_expression_deinit.extract(extract_storage.SOURCE.read_bytes()) != extract_expression_deinit.OUTPUT.read_bytes():
                raise ValueError("expression destructor extraction is stale")
            report["destructorProfileSha256"] = digest(extract_expression_deinit.OUTPUT)
        if payload:
            import extract_assembly_item_deinit
            run(output, "payload-admission", [sys.executable, "test/lean/test_assembly_item_deinit.py"], cwd=ROOT, env=env)
            if extract_assembly_item_deinit.extract(extract_assembly_item_deinit.SOURCE.read_bytes()) != extract_assembly_item_deinit.OUTPUT.read_bytes():
                raise ValueError("item payload destructor extraction is stale")
            report["payloadProfileSha256"] = digest(extract_assembly_item_deinit.OUTPUT)
        if clone_insertion:
            import extract_assembly_clone
            run(output, "clone-admission", [sys.executable, "test/lean/test_compiler_assembly_clone.py"], cwd=ROOT, env=env)
            if extract_assembly_clone.extract(extract_assembly_clone.SOURCE.read_bytes()) != extract_assembly_clone.OUTPUT.read_bytes():
                raise ValueError("item clone extraction is stale")
            report["cloneProfileSha256"] = digest(extract_assembly_clone.OUTPUT)
        clients = []
        if item_lifetime:
            if args.zig is None or args.zig_tree is None:
                raise ValueError("--item-lifetime requires --zig and --zig-tree for the native layout binding")
            run(output, "layout-admission", [sys.executable, "test/lean/test_item_layout.py"], cwd=ROOT, env=env)
            run(output, "item-fields-admission", [sys.executable, "test/lean/test_item_fields.py"], cwd=ROOT, env=env)
            clients = ["Compiler.ZigAir." + name for name in (
                "MemoryExecutionTests", "MemorySliceTests", "MemoryShapeTests", "MemoryExpSafetyTests")]
            clients += ["Compiler.Extraction.InternerPhysicalDispatchProductionTests"]
        run(output, "preflight", [tools["lake"]["path"], "build", module, "Compiler.Algebraic.Audit", *clients], cwd=ROOT / "lean", env=env)
        if item_lifetime:
            report["nativeLayout"] = capture_item_layout.capture(output / "native-layout", args.zig, args.zig_tree)
            report["nativeItemFields"] = capture_item_fields.capture(output / "native-item-fields", args.zig, args.zig_tree)
        if queries:
            report["nativeQueries"] = capture_interner_queries.capture(output / "native-queries", args.zig, args.zig_tree)
        report["audit"] = audit(output, env, tools["lean"]["path"], module, roots)
        report["controls"] = controls(output, env, tools["lean"]["path"])
        if destructor:
            report["destructorDependencies"] = expression_deinit_checks.audit(output)
            report["destructorControls"] = expression_deinit_checks.controls(output, env, tools["lean"]["path"])
        if payload:
            report["payloadDependencies"] = assembly_item_deinit_checks.audit(output)
            report["payloadControls"] = assembly_item_deinit_checks.controls(output, env, tools["lean"]["path"])
            report["releaseControls"] = check_argument_memory.controls(output, env, tools["lean"]["path"])
        if payload_insertion:
            report["payloadInsertionDependencies"] = expression_payload_checks.audit(output)
            report["payloadInsertionControls"] = expression_payload_checks.controls(output, env, tools["lean"]["path"])
        if item_lifetime:
            report["itemLifetimeDependencies"] = expression_lifetime_checks.audit(output)
            report["itemLifetimeControls"] = expression_lifetime_checks.controls(output, env, tools["lean"]["path"])
        if clone_insertion:
            report["cloneDependencies"] = assembly_clone_physical_checks.audit(output)
            report["cloneControls"] = assembly_clone_physical_checks.controls(output, env, tools["lean"]["path"])
        if item_creation:
            report["creationDependencies"] = assembly_item_creation_checks.audit(output)
            report["creationControls"] = assembly_item_creation_checks.controls(output, env, tools["lean"]["path"])
            import check_zig_air_memory_proofs
            report["optionalMemoryControls"] = check_zig_air_memory_proofs.invariant_controls(output, env, tools["lean"]["path"])
        if caller:
            report["callerDependencies"] = insertion_caller_checks.audit(output)
            report["callerControls"] = insertion_caller_checks.controls(output, env, tools["lean"]["path"])
            report["publicationDependencies"] = publication_caller_checks.audit(output)
            report["publicationControls"] = publication_caller_checks.controls(output, env, tools["lean"]["path"])
        if queries:
            report["queryDependencies"] = interner_query_checks.audit(output)
            report["queryControls"] = interner_query_checks.controls(output, env, tools["lean"]["path"])
        proof, artifacts = prove.check_module(module, roots, lean_bin=args.lean_bin, jobs=4, fresh=True)
        directory = output / "proof"
        directory.mkdir()
        for name, data in artifacts.items():
            (directory / name).write_bytes(data)
        write_json(directory / "report.json", proof)
        report["proofReportSha256"] = digest(directory / "report.json")
        if (proof.get("status") != "passed" or proof.get("freshKernelReplay") is not True or
                proof.get("replayIncludesImports") is not True or proof.get("auditedDeclarations") != roots):
            raise ValueError("insertion audit or fresh kernel replay failed")
        if inputs() != report["inputs"]:
            raise ValueError("insertion acceptance inputs changed")
        report.update(status="passed", completeInsertionControlVerified=True, auditedDeclarations=len(roots))
        if destructor:
            report.update(sourceBoundArgumentDestructionVerified=True)
        if payload:
            report.update(sourceBoundPayloadDestructionVerified=True)
        if payload_insertion:
            report.update(payloadCallbackIntegrated=True)
        if item_lifetime:
            report.update(itemAllocationDestructionVerified=True, completeExpressionLifetimeVerified=True)
        if clone_insertion:
            report.update(sourceBoundCloneVerified=True, cloneSuppliesPayloadOwnership=True)
        if item_creation:
            report.update(itemCreationCallbackIntegrated=True, creationSuppliesObjectOwnership=True,
                          cloneResultAssignmentIntegrated=True, installedCloneAppendQueriesIntegrated=True)
        if caller:
            report.update(physicalCallerInsertionContractsDerived=True, physicalCallerPublicationContractsDerived=True)
        if queries:
            report.update(sourceBoundCallerQueriesIntegrated=True, representativeReadContractsDerived=True,
                          terminalCallersWithoutRecursivePremisesVerified=True)
    finally:
        write_json(output / "report.json", report)
    if queries:
        print("Source-bound queries and representative reads compose into both complete physical callers; native fields, containers, universal admission and recursive constructor simulation remain open.")
        return
    if caller:
        print("Complete admitted physical callers derive insertion/publication contracts from one execution; native fields, containers, universal admission and recursive constructor simulation remain open.")
        return
    if item_creation:
        print("Creation, clone and complete typed field assignment compose with insertion cleanup under initial source correspondence and host contracts; recursive source/graph correspondence, containers and universal caller admission remain open.")
        return
    if clone_insertion:
        print("Source clone supplies the payload owned by insertion rollback; native fields, creation, containers and universal caller admission remain open.")
        return
    if item_lifetime:
        print("Insertion rollback consumes payload, item and argument lifetimes under captured layout/release contracts; native fields and universal caller admission remain open.")
        return
    if payload_insertion:
        print("Insertion rollback uses checked payload and argument cleanup; native item allocation and caller admission remain open.")
        return
    if payload:
        print("Item payload and insertion argument cleanup checked separately; their callback connection and item allocation destruction remain open.")
        return
    print("Insertion rollback uses checked argument destruction; native item ownership and caller refinement remain open." if destructor else
          "Complete insertion control and graph projection checked; native memory and physical caller attachment remain open.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--queries", action="store_true", help="bind production queries and representative readers in both complete physical callers; includes --caller")
    parser.add_argument("--caller", action="store_true", help="derive insertion/publication contracts in both complete physical callers under explicit admission")
    parser.add_argument("--item-creation", action="store_true", help="derive insertion object ownership from checked allocation, then compose clone and cleanup")
    parser.add_argument("--clone-insertion", action="store_true", help="attach source clone and checked byte duplication to insertion cleanup")
    parser.add_argument("--item-lifetime", action="store_true", help="compose nominal item allocation release into the complete rollback destructor")
    parser.add_argument("--zig", type=Path, help="native Zig 0.17.0 compiler for item layout capture")
    parser.add_argument("--zig-tree", type=Path, help="clean pinned Zig 0.17.0 checkout supplying the standard library")
    parser.add_argument("--payload-insertion", action="store_true", help="attach memory-changing item payload cleanup to insertion rollback")
    parser.add_argument("--payload", action="store_true", help="also check the complete item payload destructor; its insertion connection remains open")
    parser.add_argument("--destructor", action="store_true", help="attach the source-bound expression destructor to insertion rollback")
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    check(parser.parse_args())
