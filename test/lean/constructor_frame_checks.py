#!/usr/bin/env python3
"""Source binding and proof attachment for borrowed constructor call frames.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import re

import extract_constructor
from extract_compiler import Unsupported
from check_argument_memory import ROOT, NS
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
from build_toolchain import digest

FRAME = NS + "Normalization.OwnedCall.ConstructorFrame."
CLAIMS = [FRAME + name for name in (
    "operation_forwards", "represented_older", "represented_cleanup",
    "find_verified", "operation_verified")]
CLAIMS += [FRAME + "Tests." + name for name in (
    "success_observation", "failure_observation", "scratch_fault_retained", "contract",
    "success_preserves_borrow", "failure_preserves_borrow", "subslice_observation", "ordered_arguments",
    "capacity_before_scratch", "stack_exhaustion_is_rejected", "nested_parent_frame_survives",
    "success_restores_good", "failure_restores_good", "escaping_backed", "escaping_not_valid",
    "backing_does_not_imply_safe_return")]


def bindings():
    source, items, opcodes = (path.read_bytes() for path in
        (extract_constructor.SOURCE, extract_constructor.ITEMS, extract_constructor.OPCODES))
    if extract_constructor.extract(source, items, opcodes) != extract_constructor.OUTPUT.read_bytes():
        raise ValueError("constructor extraction is stale")
    before = b"return self.findDefault(&item, arguments);"
    if source.count(before) != 1:
        raise ValueError("ambiguous constructor forwarding boundary")
    controls = []
    for name, after in (
            ("empty-arguments", b"return self.findDefault(&item, &.{});"),
            ("shifted-view", b"return self.findDefault(&item, arguments[1..]);"),
            ("invented-copy", b"return self.findDefault(&item, try self.allocator.dupe(Id, arguments));")):
        try:
            extract_constructor.extract(source.replace(before, after), items, opcodes)
        except Unsupported as error:
            controls.append({"name": name, "admitted": False, "reason": str(error)})
        else:
            raise ValueError("unmodeled constructor argument storage was admitted: " + name)
    return {"sourceSha256": digest(extract_constructor.SOURCE), "programSha256": digest(extract_constructor.OUTPUT),
            "controls": controls, "argumentStorage": "original caller view forwarded unchanged",
            "boundary": "Source-bound makeOperation/findDefault request and complete find body under graph callbacks preserving the allocator-owned registry invariant. Dispatcher call-site provenance, native graph ownership and recursive simulation remain open."}


def audit(claims):
    owned = NS + "Normalization.OwnedCall."
    required = {
        FRAME + "operation_verified": {FRAME + "operation", FRAME + "find", FRAME + "find_verified",
            FRAME + "represented_cleanup", NS + "Normalization.Valid.cleanup", NS + "Normalization.Injected.cleanup",
            owned + "Semantic.production_verified",
            owned + "Caller.find", owned + "finish", "Compiler.Extraction.Interner.constructorCode",
            "Compiler.ZigAir.Memory.allocate", "Compiler.ZigAir.Memory.cleanup"},
        FRAME + "Tests.success_preserves_borrow": {FRAME + "operation_verified", FRAME + "Tests.success_observation"},
        FRAME + "Tests.failure_preserves_borrow": {FRAME + "operation_verified", FRAME + "Tests.failure_observation"},
        FRAME + "Tests.success_restores_good": {FRAME + "operation_verified", FRAME + "Tests.success_observation"},
        FRAME + "Tests.failure_restores_good": {FRAME + "operation_verified", FRAME + "Tests.failure_observation"},
        FRAME + "Tests.escaping_not_valid": {FRAME + "Tests.escaping", NS + "Normalization.Injected"},
        FRAME + "Tests.backing_does_not_imply_safe_return": {FRAME + "Tests.escaping",
            NS + "Normalization.Backed", "Compiler.ZigAir.Memory.cleanup"},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError("constructor frame lost dependencies: " + name + ": " + ", ".join(sorted(needed - claims[name])))
    return {"checkedDependencies": sorted(required), "borrowedArgumentFrameVerified": True,
            "modeledRegistryLifetimeVerified": True, "ordinaryReturnRestoresGood": True,
            "completeRecursiveConstructorsVerified": False, "globalRegistryLifetimeVerified": False}


def controls(output, env, lean):
    directory = ROOT / "lean/Compiler/Extraction"
    imports = "import Compiler.Extraction.InternerPhysicalTests\n"
    model = without_imports((directory / "InternerConstructorFrame.lean").read_text())
    tests = without_imports((directory / "InternerConstructorFrameTests.lean").read_text())
    records = [mutation_check(output, "constructor-frame-unchanged", imports + model + tests, True, env, lean)]
    # Corruption diagnostics use the executable observations only. Full proofs,
    # clients and dependency replay above remain mandatory for acceptance.
    control = model[:model.index("\ntheorem operation_forwards")]
    control += "\nend Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorFrame\n"
    observations = tests[:tests.index("\ntheorem contract")]
    observations += tests[tests.index("\ndef subslice"):tests.index("\ntheorem success_restores_good")]
    observations += "\nend Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorFrame.Tests\n"
    records.append(mutation_check(output, "constructor-frame-observations-unchanged", imports + control + observations, True, env, lean))
    for name, before, after in (
            ("omit-frame-cleanup", "Compiler.ZigAir.Memory.cleanup mark ran.2.world.memory.memory", "ran.2.world.memory.memory"),
            ("erase-parent-frame", "Compiler.ZigAir.Memory.cleanup mark", "Compiler.ZigAir.Memory.cleanup 0"),
            ("rewind-lifetimes", "memory := Compiler.ZigAir.Memory.cleanup mark ran.2.world.memory.memory",
             "memory := { Compiler.ZigAir.Memory.cleanup mark ran.2.world.memory.memory with nextId := mark }"),
            ("cleanup-semantic-fault", "if ordinary ran.1 then", "if true then"),
            ("discard-reached-effects", "memory := Compiler.ZigAir.Memory.cleanup mark ran.2.world.memory.memory",
             "effects := before.memory.effects, memory := Compiler.ZigAir.Memory.cleanup mark ran.2.world.memory.memory"),
            ("capacity-after-scratch", "if q.atCapacity before.graph then (.error (.language .capacity), ⟨before, { lookup := none }⟩) else", ""),
            ("shift-borrowed-view", "  find external budget allocator p q source (Interner.constructorCode.operationRequest opcode values)\n",
             "  find external budget allocator p q { source with first := 0 } (Interner.constructorCode.operationRequest opcode values)\n"),
            ("reversed-operands", "  find external budget allocator p q source (Interner.constructorCode.operationRequest opcode values)\n",
             "  find external budget allocator p q source (Interner.constructorCode.operationRequest opcode values.reverse)\n")):
        if control.count(before) != 1:
            raise ValueError("ambiguous constructor frame mutation: " + name)
        records.append(mutation_check(output, "constructor-frame-" + name,
            imports + control.replace(before, after) + observations, False, env, lean))
    for record in records:
        text = (output / (record["name"] + ".stdout")).read_text()
        if re.search(r"maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant", text, re.I):
            raise ValueError("constructor frame control hit a resource or syntax failure: " + record["name"])
        if not record["expectedAcceptance"] and not re.search(r"error: (?:unsolved goals|Application type mismatch|Type mismatch|Tactic[^\n]*failed)", text):
            raise ValueError("constructor frame control lacks a semantic proof failure: " + record["name"])
    return records
