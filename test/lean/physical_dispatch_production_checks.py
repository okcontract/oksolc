#!/usr/bin/env python3
"""Check complete physical caller composition with the shared dispatcher.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import json
import re
import constructor_frame_checks
import borrowed_constructor_checks
import borrowed_query_checks
import native_force_checks
import native_find_checks
import native_find_caller_checks
import constructor_inventory
import check_native_invocation as interface

from check_argument_memory import ROOT, NS
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
from physical_dispatch_checks import RECURSIVE

MODULE = native_find_checks.MODULE
CLAIMS = [RECURSIVE + name for name in ("ownership_contracts", "caller_contracts_cursor", "caller_contracts", "production_verified_cursor", "production_verified")]
CLAIMS += [RECURSIVE + "ProductionTests." + name for name in (
    "graph_ownership", "graph_semantics", "source_represented", "graph_valid", "production_contract",
    "success_observation", "publication_failure_observation", "cutoff_observation", "normalization_failure_observation",
    "force_observation", "production_closed", "success_verified", "cursor_failure_sound", "cursor_production_contract",
    "cursor_failure_observation", "cursor_failure_closed")]
CLAIMS += constructor_frame_checks.CLAIMS
CLAIMS += borrowed_constructor_checks.CLAIMS
CLAIMS += borrowed_query_checks.CLAIMS
CLAIMS += native_force_checks.CLAIMS
CLAIMS += native_find_checks.CLAIMS
CLAIMS += native_find_caller_checks.CLAIMS


def audit(output):
    rows = json.loads((output / "audit.json").read_bytes())["claims"]
    claims = {c["theorem"]: set(c["dependencies"]) for c in rows}
    owned = NS + "Normalization.OwnedCall."
    required = {
        RECURSIVE + "ownership_contracts": {RECURSIVE + "simplify_borrows", owned + "GraphContracts", owned + "Contracts"},
        RECURSIVE + "caller_contracts_cursor": {RECURSIVE + "simplify_verified_cursor", RECURSIVE + "projectionAt",
            "Compiler.Extraction.Dispatch.Effects.simplify", owned + "Semantic.GraphContracts"},
        RECURSIVE + "caller_contracts": {RECURSIVE + "caller_contracts_cursor"},
        RECURSIVE + "production_verified": {RECURSIVE + "production_verified_cursor", RECURSIVE + "caller_contracts_cursor", RECURSIVE + "callbacks",
            owned + "Semantic.production_verified", owned + "Caller.initialize_verified", owned + "finish",
            NS + "Normalization.caller_buffer", NS + "Normalization.take_refines", NS + "Normalization.deinit_refines",
            "Compiler.Extraction.Dispatch.default_key_simplify_safe"},
        RECURSIVE + "production_verified_cursor": {RECURSIVE + "caller_contracts_cursor", owned + "Semantic.production_verified"},
        RECURSIVE + "ProductionTests.cursor_failure_closed": {RECURSIVE + "production_verified_cursor",
            RECURSIVE + "PreservationTests.advance_projects_held", owned + "Semantic.Verified.closed"},
        RECURSIVE + "ProductionTests.success_verified": {RECURSIVE + "production_verified",
            RECURSIVE + "PreservationTests.counted_projects", "Compiler.Extraction.Recursive.unfold_safe",
            owned + "Semantic.Verified.closed", RECURSIVE + "ProductionTests.success_observation"},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError("production dispatcher composition lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    statements = {c["theorem"]: c["statement"] for c in rows}
    checked_statements = []
    for short in ("caller_contracts_cursor", "production_verified_cursor"):
        statement = statements[RECURSIVE + short]
        entries, _, _ = interface.domains(statement)
        needed = {"cursor", "model", "coupled", "correct", "addresses", "shifts", "coherent", "graph"}
        needed |= {"memory"} if short == "caller_contracts_cursor" else {"ownership", "good", "allocated", "admitted", "valid", "evaluated"}
        if not needed <= entries.keys():
            raise ValueError("observed production endpoint lost an original obligation: " + short)
        coupled = interface.step.constants_below(statement, entries["coupled"][0])
        if not {RECURSIVE + "projectionAt", RECURSIVE + "cursorGraph", owned + "Held", RECURSIVE + "constructors"} <= coupled:
            raise ValueError("observed endpoint lost exact child/resource/live-borrow relation: " + short)
        if RECURSIVE + "projection" in coupled:
            raise ValueError("observed endpoint still requires raw graph child simulation")
        forbidden = {owned + "Semantic.Verified", owned + "Semantic.Ensures", owned + "Closed", RECURSIVE + short}
        for name, (root, _) in entries.items():
            if interface.step.constants_below(statement, root) & forbidden:
                raise ValueError("observed endpoint assumes its enclosing preservation: " + short + "." + name)
        if any(part.endswith("Tests") for dep in claims[RECURSIVE + short] for part in dep.split(".")):
            raise ValueError("observed production endpoint depends on a fixture")
        checked_statements.append(RECURSIVE + short)
    return {"checkedDependencies": sorted(required), "checkedStatements": checked_statements,
            "conditionalObservedCursorCompositionVerified": True, "physicalDispatcherCallerCompositionVerified": True,
            "constructorFrame": constructor_frame_checks.audit(claims),
            "borrowedConstructor": borrowed_constructor_checks.audit(claims),
            "borrowedQuery": borrowed_query_checks.audit(claims),
            "nativeForce": native_force_checks.audit(claims),
            "nativeForceStatements": native_force_checks.audit_statements(rows),
            "nativeFind": native_find_checks.audit(claims),
            "nativeFindStatements": native_find_checks.audit_statements(rows),
            "nativeFindCaller": native_find_caller_checks.audit(claims),
            "nativeFindCallerStatements": native_find_caller_checks.audit_statements(rows),
            "physicalRecursivePreservationVerified": False,
            "pendingObligations": ["initial native graph/query/ownership and complete constructor input admission",
                                   "compiler-wide production integration and termination"]}


def controls(output, env, lean):
    directory = ROOT / "lean/Compiler/Extraction"
    imports = "import Compiler.Extraction.InternerPhysicalDispatchPreservationTests\n"
    model = without_imports((directory / "InternerPhysicalDispatchProduction.lean").read_text())
    tests = without_imports((directory / "InternerPhysicalDispatchProductionTests.lean").read_text())
    records = [mutation_check(output, "dispatcher-production-unchanged", imports + model + tests, True, env, lean)]
    # Isolate executable attachment observations for negative controls: changing
    # the full theorem's target can make definitional equality expand the entire
    # caller before reporting a mismatch. The full proof and fixtures are checked
    # unchanged above and in fresh replay; this diagnostic subset is not acceptance.
    setup = tests[:tests.index("/-- Every finite logical unfolding")]
    observations = tests[tests.index("theorem success_observation :"):tests.index("theorem production_closed")]
    fixture = setup + observations + tests[tests.index("\nend Compiler."):]
    records.append(mutation_check(output, "dispatcher-production-observations-unchanged",
                                  imports + model + fixture, True, env, lean))
    for name, before, after in (
        ("use-seed-simplifier", "callbacks (seed fail) Compiler.Extraction.Recursive.Tests.reads 64 (PreservationTests.physical depth)", "seed fail"),
        ("alias-source-as-scratch", "def buffer : View := ⟨caller.memory.memory.nextId, 0, 2⟩", "def buffer : View := source"),
        ("discard-scratch-allocation", "def world : World Nat := { caller with memory := { caller.memory with memory := before.memory } }",
         "def world : World Nat := caller"),
        ("omit-caller-cleanup", "Caller.find external 160 7 (actual fail depth) q source buffer request world",
         "Caller.findBody external 160 7 (actual fail depth) q source buffer request ⟨world, { lookup := none }⟩"),
        ("force-unequal-id", "def forceId : NodeId := 42", "def forceId : NodeId := 1"),
        ("unrelated-constructors", "(PreservationTests.physical depth)", "(fun _ => pure 0)"),
    ):
        if fixture.count(before) != 1:
            raise ValueError("ambiguous production dispatcher mutation: " + name)
        records.append(mutation_check(output, "dispatcher-production-" + name,
                                      imports + model + fixture.replace(before, after), False, env, lean))
    for record in records:
        diagnostic = (output / (record["name"] + ".stdout")).read_text()
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant", diagnostic, re.I):
            raise ValueError("production dispatcher control hit a resource or syntax failure: " + record["name"])
        if not record["expectedAcceptance"] and not re.search(
                r"error: (?:unsolved goals|Application type mismatch|Type mismatch|Tactic[^\n]*failed)", diagnostic):
            raise ValueError("production dispatcher control lacks a semantic proof failure: " + record["name"])
    return (records + cursor_controls(output, env, lean) + constructor_frame_checks.controls(output, env, lean) + borrowed_constructor_checks.controls(output, env, lean)
            + borrowed_query_checks.controls(output, env, lean) + native_force_checks.controls(output, env, lean)
            + native_find_checks.controls(output, env, lean) + native_find_caller_checks.controls(output, env, lean))


def cursor_mutations():
    directory = ROOT / "lean/Compiler/Extraction"
    meaning = (directory / "InternerPhysicalMeaning.lean").read_text()
    meaning = meaning[meaning.index("theorem Ensures.cursor_iff"):meaning.index("theorem Ensures.error")]
    preservation = (directory / "InternerPhysicalDispatchPreservation.lean").read_text()
    preservation = preservation[preservation.index("theorem ProjectsAt.safe_cursor"):preservation.index("/-- Transfer the existing universal word proof")]
    production = without_imports((directory / "InternerPhysicalDispatchProduction.lean").read_text())
    owned = NS + "Normalization.OwnedCall."
    opened = "open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul\nopen Compiler.ZigAir.Memory.WordArray\n"
    source = "import Compiler.Extraction.InternerPhysicalDispatchProductionTests\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n"
    source += "namespace " + owned + "Semantic\n" + opened + meaning + "\nend " + owned + "Semantic\n"
    source += "namespace " + RECURSIVE[:-1] + "\n" + opened + preservation + "\nend " + RECURSIVE[:-1] + "\n" + production
    for name in ("cursor_iff", "safe_cursor", "simplify_verified_cursor", "ownership_contracts", "caller_contracts_cursor",
                 "caller_contracts", "production_verified_cursor", "production_verified"):
        source = re.sub(r"(?<!Semantic\.)\b" + name + r"\b", name + "Mutation", source)
    mutations = [
        ("lose-postcondition", "(fun value heap => post value heap.read)", "(fun _ _ => True)", 4),
        ("use-initial-reads", "(physical before).2.graph\n      (fun value heap => post value heap.read) :=", "(physical before).2.graph\n      (fun value _ => post value before.graph.read) :=", 1),
        ("use-initial-graph", "(physical before).2.graph\n      (fun value heap", "before.graph\n      (fun value heap", 1),
        ("wrong-value", "after.read id = some expected", "after.read id = some (expected + 1)", 1),
        ("wrong-request-value", "(fun id after => after.read id = some value)", "(fun id after => after.read id = some (value + 1))", 2),
        ("omit-word-contract", "(correct : Associative.ConstructorSound (Dispatch.wordBaseMeaning env other) model)", "(correct : True)", 5),
        ("omit-address-contract", "(addresses : AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) model.operation)", "(addresses : True)", 5),
        ("omit-shift-contract", "(shifts : ArithmeticShift.Constructs (AddressMask.addressMeaning env other) model.operation)", "(shifts : True)", 5),
        ("misbind-resource-position", "(projectionAt (cursorGraph cursor)", "(projectionAt (cursorGraph (fun _ => 0))", 5),
        ("misbind-child", ".Constructors (constructors find) model)", ".Constructors (constructors (fun _ => pure 0)) model)", 5),
        ("misbind-force-value", "before.graph.read id = some value →", "before.graph.read id = some (value + 1) →", 2),
    ]
    return source, mutations


def cursor_controls(output, env, lean):
    source, mutations = cursor_mutations()
    records = [mutation_check(output, "dispatcher-cursor-unchanged", source, True, env, lean)]
    for name, before, after, count in mutations:
        if source.count(before) != count:
            raise ValueError("ambiguous dispatcher cursor control: " + name + ": " + str(source.count(before)))
        records.append(mutation_check(output, "dispatcher-cursor-" + name, source.replace(before, after), False, env, lean))
    for record in records:
        diagnostic = (output / (record["name"] + ".stdout")).read_text()
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant|already been declared", diagnostic, re.I):
            raise ValueError("dispatcher cursor control hit a resource or syntax failure: " + record["name"])
    return records


def check_component(args):
    """Replay this proof component without claiming fresh native source capture."""
    import check_word_swap as harness
    import check_argument_memory as python_inputs
    import check_recursive_nonempty as source_gate
    import physical_dispatch_preservation_checks as preservation
    from build_toolchain import digest, write_json

    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    claims = list(dict.fromkeys(preservation.CLAIMS + CLAIMS))
    report = {"schema": "oksolc.dispatcher-production-component.v1", "status": "failed", "jobs": 4,
              "scope": "conditional physical dispatcher composition and exact native force/find caller preservation",
              "preflightOnly": args.preflight, "nativeZigGateRun": False,
              "conditionalObservedCursorCompositionVerified": False,
              "exactNativeForceBodyVerified": False, "exactNativeFindWordsVerified": False, "exactNativeFindBodyVerified": False,
              "completeRecursiveConstructorsVerified": False, "composedProductionTheoremVerified": False,
              "wholeCompilerVerified": False}
    try:
        report["inputs"] = python_inputs.inputs()
        report["leanInputs"] = harness.lean_check.source_inputs()
        frozen = source_gate.inputs()
        library = args.zig_lib_dir.resolve()
        std, profiles = source_gate.std_inputs(library), source_gate.profiles(library)
        write_json(output / "inputs.json", frozen)
        write_json(output / "std-inputs.json", std)
        write_json(output / "source-profiles.json", profiles)
        env, _, report["tools"] = harness.lean_check.toolchain(args.lean_bin, 4)
        lean = report["tools"]["lean"]["path"]
        report["audit"] = harness.audit(output, env, lean, MODULE, claims)
        report["preservationInterfaces"] = preservation.audit(output)
        report["productionInterfaces"] = audit(output)
        report["controls"] = preservation.controls(output, env, lean) + controls(output, env, lean)
        print("Cached dispatcher audit and semantic controls passed.", flush=True)
        if not args.preflight:
            proof, artifacts = harness.prove.check_module(MODULE, claims, lean_bin=args.lean_bin, jobs=4, fresh=True, timeout=1800)
            for name, data in artifacts.items():
                (output / ("proof-" + name)).write_bytes(data)
            if (proof.get("status") != "passed" or proof.get("freshKernelReplay") is not True
                    or proof.get("replayIncludesImports") is not True or proof.get("buildInputs") != report["leanInputs"]
                    or proof.get("auditedDeclarations") != claims):
                raise ValueError("fresh imported dispatcher replay failed or inputs differ: " + str(proof.get("failure")))
            report["proof"] = {"sha256": digest(output / "proof-report.json"), "roots": len(claims),
                               "freshKernelReplay": True, "replayIncludesImports": True}
        if (report["inputs"] != python_inputs.inputs() or report["leanInputs"] != harness.lean_check.source_inputs()
                or frozen != source_gate.inputs() or std != source_gate.std_inputs(library) or profiles != source_gate.profiles(library)):
            raise ValueError("dispatcher component inputs changed during the run")
        report["frozenNativeInputs"] = len(frozen)
        report["zigLibrary"] = {"path": str(library), "inputs": len(std), "sha256": digest(output / "std-inputs.json")}
        report["conditionalObservedCursorCompositionVerified"] = not args.preflight
        report["exactNativeForceBodyVerified"] = not args.preflight
        report["exactNativeFindWordsVerified"] = not args.preflight
        report["exactNativeFindBodyVerified"] = not args.preflight
        report["status"] = "passed"
    finally:
        write_json(output / "report.json", report)
    print(json.dumps({"status": report["status"], "roots": len(claims), "controls": len(report["controls"]),
                      "preflightOnly": args.preflight}))
