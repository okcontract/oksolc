/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRuleUnaryProofs
import Compiler.Extraction.InternerTemporaryUnaryTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryUnary.RuleLiteral.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open Normalization.Tests

def nestedSource : View := ⟨0, 1, 1⟩
def exponentSource : View := ⟨0, 0, 2⟩
def caller := TemporaryUnary.Tests.semanticCaller
def run (site : Site) (source : View) (parity : NodeId := 1) (external : External Nat := success) :=
  zigLiteral site external 160 7 (Semantic.Tests.callbacks Semantic.Tests.meaning 99) Caller.Tests.queries source parity caller

/-- Observe the physical ID at the constructor callback, even when different
IDs denote the same nonzero word. These callbacks are a provenance fixture. -/
def observedCallbacks : Primitives Nat := { Semantic.Tests.callbacks Semantic.Tests.meaning 99 with
  simplify := fun key slice before =>
    if Compiler.ZigAir.Memory.load before.memory.memory ((view slice).pointer 0) = .ok (number 1) then
      (Semantic.Tests.callbacks Semantic.Tests.meaning 99).simplify key slice before
    else (.error .missingHandle, before) }
def observed (site : Site) (source : View) :=
  zigLiteral site success 160 7 observedCallbacks Caller.Tests.queries source 1 caller

theorem physical_operand_is_observed : (observed .nestedIszero nestedSource).1 = .ok 99 ∧
    (observed .zeroBaseExponent exponentSource).1 = .ok 99 := ⟨by rfl', by rfl'⟩

theorem nested_word_is_loaded : run .nestedIszero nestedSource =
    TemporaryUnary.Tests.semanticRun := by rfl'

theorem exponent_word_is_loaded : run .zeroBaseExponent exponentSource =
    TemporaryUnary.Tests.semanticRun := by rfl'

theorem parity_id_is_used : run .parity ⟨0, 0, 0⟩ = TemporaryUnary.Tests.semanticRun := by rfl'

theorem original_borrow_survives :
    (run .nestedIszero nestedSource).2.memory.memory.heap.lookup 0 = original.memory.heap.lookup 0 ∧
    (run .zeroBaseExponent exponentSource).2.memory.memory.heap.lookup 0 = original.memory.heap.lookup 0 := ⟨by rfl', by rfl'⟩

theorem ordinary_success_unwinds : (run .nestedIszero nestedSource).1 = .ok 99 ∧
    (run .nestedIszero nestedSource).2.memory.memory.heap.lookup 3 = none ∧
    4 < (run .nestedIszero nestedSource).2.memory.memory.nextId := ⟨by rfl', by rfl', by decide +kernel⟩

theorem ordinary_oom_unwinds : (run .zeroBaseExponent exponentSource 1 (external (fun _ => true))).1 =
    .error (.language .outOfMemory) ∧
    (run .zeroBaseExponent exponentSource 1 (external (fun _ => true))).2.memory.memory.heap = original.memory.heap :=
  ⟨by rfl', by rfl'⟩

theorem bounds_reject_before_allocation : run .nestedIszero ⟨0, 1, 0⟩ =
    (.error (.memory (.preparation (.memory .sourceBounds))), caller) := by rfl'

theorem missing_memory_rejects_before_allocation : run .zeroBaseExponent ⟨99, 0, 2⟩ =
    (.error (.memory (.preparation (.memory .unallocated))), caller) := by rfl'

theorem unread_word_rejects_before_allocation : run .nestedIszero ⟨0, 3, 1⟩ =
    (.error (.memory (.preparation (.memory .memoryValidity))), caller) := by rfl'

def grown (before : World Nat) : World Nat := { before with
  graph := { before.graph with read := fun id => if id = 98 then some 11 else before.graph.read id },
  memory := { before.memory with effects := before.memory.effects + 13 } }
def child (result : Except Fault NodeId) : GraphAction Nat NodeId := fun before => (result, grown before)
def afterChild (result : Except Fault NodeId := .ok 1) (external : External Nat := success) :=
  afterParity (child result) external 160 7 (Semantic.Tests.callbacks Semantic.Tests.meaning 99) Caller.Tests.queries caller

theorem child_oom_keeps_growth_without_allocation : afterChild (.error (.language .outOfMemory)) =
    (.error (.language .outOfMemory), grown caller) := child_error _ _ _ _ _ _ _ _ _ rfl

theorem child_rejection_keeps_growth_without_allocation : afterChild (.error .missingHandle) =
    (.error .missingHandle, grown caller) := child_error _ _ _ _ _ _ _ _ _ rfl

theorem child_success_uses_returned_id_and_world : afterChild =
    invoke success 160 7 (Semantic.Tests.callbacks Semantic.Tests.meaning 99) Caller.Tests.queries
      (Interner.buildOpcode .ISZERO) 1 (grown caller) := child_return _ _ _ _ _ _ _ _ _ rfl

theorem later_oom_preserves_growth_and_unwinds : (afterChild (.ok 1) (external (fun _ => true))).1 =
    .error (.language .outOfMemory) ∧ (afterChild (.ok 1) (external (fun _ => true))).2.graph.read 98 = some 11 ∧
    (afterChild (.ok 1) (external (fun _ => true))).2.memory.memory.heap = original.memory.heap :=
  ⟨by rfl', by rfl', by rfl'⟩

theorem nested_source_represented : Represents original.memory nestedSource [1] := by
  refine ⟨rfl, ?_⟩
  intro index inside
  have zero : index = 0 := by change index < 1 at inside; omega
  subst index
  rfl'

theorem nonvacuous_borrowed_constructor_contract : (run .nestedIszero nestedSource).1 = .ok 99 ∧
    Valid (run .nestedIszero nestedSource).2.memory ∧
    Semantic.Ensures Semantic.Tests.meaning caller.graph (run .nestedIszero nestedSource).1
      (run .nestedIszero nestedSource).2.graph (fun id graph => graph.read id = some 0) := by
  have checked := BorrowedInput.invoke_verified success 160 7 (Semantic.Tests.callbacks Semantic.Tests.meaning 99)
    Caller.Tests.queries (Interner.buildOpcode .ISZERO) nestedSource [1] 0 (by decide) caller _
    TemporaryUnary.Tests.unaryMemory Compiler.Extraction.Recursive.Tests.base 0 original_valid nested_source_represented
    TemporaryUnary.Tests.actual_allocation (external_admitted _) (Semantic.Tests.ownership _ _) (Semantic.Tests.semantics _ _)
    ⟨(by intro _ _ impossible; cases impossible), trivial⟩ (by rfl')
  exact ⟨by rfl', checked (by rfl')⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryUnary.RuleLiteral.Tests
