#!/usr/bin/env python3
"""Check source-bound borrowed dispatcher calls into the complete caller.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import json
import re

import extract_dispatch
import extract_shift_masks
from check_argument_memory import ROOT, NS
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

BORROWED = NS + "Normalization.OwnedCall.Recursive.BorrowedConstructor."
CLAIMS = [BORROWED + name for name in ("operation_forwards", "operation_verified")]
CLAIMS += [BORROWED + "Tests." + name for name in (
    "byte_borrow", "comparison_borrows", "arithmetic_borrows", "shift_mask_borrow",
    "production_success", "production_failure", "production_semantic_fault", "contract",
    "dispatch_reaches_child", "dispatcher_restores_good", "success_restores_good", "failure_restores_good")]


def bindings():
    checked = []
    for module in (extract_dispatch, extract_shift_masks):
        args = [module.nested.SOURCE.read_bytes(), module.nested.OPCODES.read_bytes(), module.nested.STORAGE.read_bytes()]
        if module is extract_dispatch:
            args.append(module.VERSIONS.read_bytes())
        if module.extract(*args) != module.OUTPUT.read_bytes():
            raise ValueError("stale borrowed dispatcher extraction")
        checked.append(str(module.OUTPUT.relative_to(ROOT)))
    dispatch = extract_dispatch.OUTPUT.read_text()
    observed = {opcode: dispatch.count("constructors.borrowedOperation inner.address op" + opcode + " inner.items debug")
                for opcode in ("BYTE", "EQ", "LT", "SLT", "GT", "SGT")}
    if observed != {"BYTE": 1, "EQ": 3, "LT": 1, "SLT": 1, "GT": 1, "SGT": 1} or (
            extract_shift_masks.OUTPUT.read_text().count("constructors.borrowedOperation shifted.address shrOpcode shifted.items debug") != 1):
        raise ValueError("borrowed source-model call inventory changed")
    return {"generatedModules": checked, "borrowedCallSites": sum(observed.values()) + 1,
            "inlineCallSites": observed, "helperCallSites": {"removeCoveredShiftMask": 1},
            "argumentStorage": "operationArguments full-array address forwarded through borrowedOperation to ConstructorFrame.find",
            "boundary": "Native graph query/storage refinement, temporary arrays and complete recursive simulation remain compiler obligations."}


def audit(claims):
    owned = NS + "Normalization.OwnedCall."
    required = {
        BORROWED + "operation_verified": {BORROWED + "caller", owned + "ConstructorFrame.operation_verified",
            owned + "ConstructorFrame.find", owned + "Semantic.production_verified", NS + "Normalization.Valid.cleanup",
            "Compiler.Extraction.Associative.Constructors.borrowedOperation"},
        BORROWED + "Tests.byte_borrow": {"Compiler.Extraction.Dispatch.binaryStageWithInputs", BORROWED + "Tests.record"},
        BORROWED + "Tests.comparison_borrows": {"Compiler.Extraction.Dispatch.unaryStageWithInputs", BORROWED + "Tests.record"},
        BORROWED + "Tests.arithmetic_borrows": {"Compiler.Extraction.Dispatch.unaryStageWithInputs", BORROWED + "Tests.record"},
        BORROWED + "Tests.shift_mask_borrow": {"Compiler.Extraction.ShiftMasks.removeCoveredShiftMask", BORROWED + "Tests.record"},
        BORROWED + "Tests.production_success": {BORROWED + "caller", owned + "Caller.find", owned + "finish",
            "Compiler.Extraction.Dispatch.unaryStageWithInputs", "Compiler.ZigAir.Memory.cleanup"},
        BORROWED + "Tests.dispatcher_restores_good": {BORROWED + "operation_verified", BORROWED + "Tests.dispatch_reaches_child"},
        BORROWED + "Tests.success_restores_good": {BORROWED + "operation_verified", BORROWED + "Tests.run"},
        BORROWED + "Tests.failure_restores_good": {BORROWED + "operation_verified", BORROWED + "Tests.run"},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError("borrowed constructor lost dependencies: " + name + ": " + ", ".join(sorted(needed - claims[name])))
    return {"checkedDependencies": sorted(required), "borrowedCallSiteProvenanceVerified": True,
            "borrowedCallerCompositionVerified": True, "completeRecursiveConstructorsVerified": False}


def controls(output, env, lean):
    directory = ROOT / "lean/Compiler/Extraction"
    imports = "import Compiler.Extraction.InternerConstructorFrameTests\nimport Compiler.Extraction.InternerPhysicalDispatch\nimport Compiler.Extraction.DispatchTests\n"
    model = without_imports((directory / "InternerBorrowedConstructor.lean").read_text())
    tests = without_imports((directory / "InternerBorrowedConstructorTests.lean").read_text())
    records = [mutation_check(output, "borrowed-constructor-unchanged", imports + model + tests, True, env, lean)]
    for name, before, after in (
            ("invented-address", "\n    borrowed ⟨address, 0, ids.length⟩", "\n    borrowed ⟨address + 1, 0, ids.length⟩"),
            ("shortened-view", "\n    borrowed ⟨address, 0, ids.length⟩", "\n    borrowed ⟨address, 0, 0⟩")):
        # The universal forwarding theorem detects these at the constructor
        # boundary, without expanding the complete caller to diagnose a mutant.
        physical = without_imports((directory / "InternerPhysicalDispatch.lean").read_text())
        if physical.count(before) != 1:
            raise ValueError("ambiguous borrowed view mutation")
        physical_imports = "import Compiler.Extraction.InternerPhysicalProduction\n"
        records.append(mutation_check(output, "borrowed-constructor-" + name,
            physical_imports + physical.replace(before, after), False, env, lean))

    # Give the emitted programs distinct namespaces: the fixtures and physical
    # constructor use the real imported interfaces. Only their dispatcher entry
    # is redirected to the diagnostic copy. Full originals are freshly replayed
    # by the production gate; these copies are never acceptance artifacts.
    dispatch = without_imports(extract_dispatch.OUTPUT.read_text())
    dispatch = dispatch.replace("namespace Compiler.Extraction.Dispatch\n",
        "namespace Compiler.Extraction.BorrowedMutatedDispatch\nopen Compiler.Extraction.Dispatch\n")
    dispatch = dispatch.replace("end Compiler.Extraction.Dispatch", "end Compiler.Extraction.BorrowedMutatedDispatch")
    fixture = tests.replace("Dispatch.simplify (", "Compiler.Extraction.BorrowedMutatedDispatch.simplify (")
    diagnostic = imports + model + dispatch + fixture
    records.append(mutation_check(output, "borrowed-dispatch-observations-unchanged", diagnostic, True, env, lean))
    for opcode in ("BYTE", "EQ", "LT", "SLT", "GT", "SGT"):
        before = "constructors.borrowedOperation inner.address op" + opcode + " inner.items debug"
        sites = dispatch.count(before)
        if sites != (3 if opcode == "EQ" else 1):
            raise ValueError("unexpected borrowed call inventory: " + opcode)
        for site in range(sites):
            position = [match.start() for match in re.finditer(re.escape(before), dispatch)][site]
            changed = dispatch[:position] + dispatch[position:].replace(before, "constructors.operation op" + opcode + " inner.items debug", 1)
            records.append(mutation_check(output, "borrowed-dispatch-drop-" + opcode.lower() + "-" + str(site),
                imports + model + changed + fixture, False, env, lean))
    shifts = without_imports(extract_shift_masks.OUTPUT.read_text())
    shifts = shifts.replace("namespace Compiler.Extraction.ShiftMasks\n",
        "namespace Compiler.Extraction.BorrowedMutatedShiftMasks\nopen Compiler.Extraction.ShiftMasks\n")
    shifts = shifts.replace("end Compiler.Extraction.ShiftMasks", "end Compiler.Extraction.BorrowedMutatedShiftMasks")
    shifted_dispatch = dispatch.replace("ShiftMasks.", "Compiler.Extraction.BorrowedMutatedShiftMasks.")
    before = "constructors.borrowedOperation shifted.address shrOpcode shifted.items debug"
    if shifts.count(before) != 1:
        raise ValueError("unexpected borrowed shift-mask inventory")
    records.append(mutation_check(output, "borrowed-shift-observations-unchanged",
        imports + model + shifts + shifted_dispatch + fixture, True, env, lean))
    records.append(mutation_check(output, "borrowed-dispatch-drop-shift",
        imports + model + shifts.replace(before, "constructors.operation shrOpcode shifted.items debug") + shifted_dispatch + fixture,
        False, env, lean))
    for record in records:
        diagnostic = (output / (record["name"] + ".stdout")).read_text()
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant", diagnostic, re.I):
            raise ValueError("borrowed constructor control hit a resource or syntax failure: " + record["name"])
    return records
