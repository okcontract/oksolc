/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPhysicalFixtures

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Semantic.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open Normalization.Tests

def meaning := Folding.wordMeaning Compiler.Extraction.Recursive.Tests.base
def wordGraph : Interner.Heap where
  read := fun id => some (if id = 42 then 42 else if id = 3 then 32 else 10)
  table := fun _ => none
def caller : World Nat := ⟨wordGraph, original⟩
def source : View := ⟨0, 0, 2⟩
def buffer : View := ⟨caller.memory.memory.nextId, 0, 2⟩
def request : Interner.Request := ⟨⟨1, some 1, 0⟩, [3, 1], 77⟩
def world : World Nat := { caller with memory := { caller.memory with memory := before.memory } }
def found := Caller.find success 160 7 (callbacks meaning 42) Caller.Tests.queries source buffer request world
def forced := Caller.force success 160 7 (callbacks meaning 42) Caller.Tests.queries source buffer 42 request.item request.arguments world
def missed := Caller.find success 160 7 (callbacks meaning 1) Caller.Tests.queries source buffer request world

theorem graph_valid : Interner.Invariant meaning wordGraph := ⟨(by intro key id impossible; cases impossible), trivial⟩

theorem source_represented : Represents original.memory source request.arguments := by
  refine ⟨rfl, ?_⟩
  intro index inside
  have bound : index < 2 := inside
  have cases : index = 0 ∨ index = 1 := by omega
  rcases cases with zero | one
  · subst index; rfl'
  · subst index; rfl'

theorem request_value : request.item.eval meaning wordGraph.read request.arguments request.sequence = some 42 := by rfl'
theorem force_value : request.item.eval meaning wordGraph.read request.arguments 0 = some 42 := by rfl'

/-- These observations bind success, correct value, both actual frees, original
argument preservation and detached handoff to the same physical execution. -/
theorem found_observation : found.1 = .ok 42 ∧ found.2.world.graph.read 42 = some 42 ∧
    found.2.world.memory.heap 4 = none ∧ found.2.world.memory.heap 7 = none ∧
    found.2.world.memory.effects = 225 ∧ found.2.scope.lookup = none ∧ found.2.scope.handedOff = true :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem forced_observation : forced.1 = .ok () ∧ forced.2.world.memory.heap 4 = none ∧
    forced.2.scope.lookup = none ∧ forced.2.scope.handedOff = true := ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem miss_observation : missed.1 = .error (.language .outOfMemory) ∧
    missed.2.world.memory.heap 4 = none ∧ missed.2.world.memory.heap 7 = none ∧ missed.2.scope.handedOff = true :=
  ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem unequal_representative : world.graph.read 1 ≠ request.item.eval meaning world.graph.read request.arguments 0 := by decide

/-- Concrete attachment to the composed production theorem; every callback
memory and semantic contract is discharged by the fixture implementation. -/
theorem production_contract (known : NodeId) :
    Verified success 7 source request.arguments meaning (Caller.findBody success 160 7 (callbacks meaning known) Caller.Tests.queries source buffer request) world
      (fun id after => after.read id = some 42) ∧
    Verified success 7 source request.arguments meaning (Caller.forceBody success 160 7 (callbacks meaning known) Caller.Tests.queries source buffer 42 request.item request.arguments) world
      (fun _ _ => True) := by
  have checked := production_verified success 160 7 (callbacks meaning known) Caller.Tests.queries source request 42 caller before.memory _
    Compiler.Extraction.Recursive.Tests.base 42 ⟨original_valid, source_represented⟩ actual_caller_allocation (external_admitted _)
    (ownership meaning known source request.arguments) (semantics meaning known source request.arguments) graph_valid request_value
  exact ⟨checked.1, checked.2 force_value (by rfl')⟩

theorem production_success :
    Verified success 7 source request.arguments meaning (Caller.findBody success 160 7 (callbacks meaning 42) Caller.Tests.queries source buffer request) world
      (fun id after => after.read id = some 42) ∧ found.1 = .ok 42 :=
  ⟨(production_contract 42).1, found_observation.1⟩

theorem production_force :
    Verified success 7 source request.arguments meaning (Caller.forceBody success 160 7 (callbacks meaning 42) Caller.Tests.queries source buffer 42 request.item request.arguments) world
      (fun _ _ => True) ∧ forced.1 = .ok () :=
  ⟨(production_contract 42).2, forced_observation.1⟩

theorem production_failure :
    Verified success 7 source request.arguments meaning (Caller.findBody success 160 7 (callbacks meaning 1) Caller.Tests.queries source buffer request) world
      (fun id after => after.read id = some 42) ∧ missed.1 = .error (.language .outOfMemory) :=
  ⟨(production_contract 1).1, miss_observation.1⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Semantic.Tests
