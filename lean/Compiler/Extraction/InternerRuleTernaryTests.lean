/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRuleTernaryProofs
import Compiler.Extraction.InternerTemporaryUnaryTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryTernary.RuleLiteral.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open Normalization.Tests

def source : View := ⟨0, 0, 2⟩
def ternaryMemory : Compiler.ZigAir.Memory.State :=
  ⟨(3, { scratchCell with type := .array 3 word }) :: original.memory.heap, 4, 64⟩
def prepared := (prepare 3 1 2 Semantic.Tests.caller).2
def target : View := ⟨3, 0, 3⟩

theorem actual_allocation : Compiler.ZigAir.Memory.allocate original.memory (.array 3 word) =
    .ok (.pointer (.pointer true false (.array 3 word)) ⟨3, 0⟩, ternaryMemory) := by rfl'

theorem initialized_all_three : (prepare 3 1 2 Semantic.Tests.caller).1 = .ok target ∧
    Compiler.ZigAir.Memory.load prepared.memory.memory (target.pointer 0) = .ok (number 3) ∧
    Compiler.ZigAir.Memory.load prepared.memory.memory (target.pointer 1) = .ok (number 1) ∧
    Compiler.ZigAir.Memory.load prepared.memory.memory (target.pointer 2) = .ok (number 2) :=
  ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem good_is_derived : Good target [3, 1, 2] prepared := by
  obtain ⟨after, ran, good, _⟩ := prepare_verified 3 1 2 Semantic.Tests.caller _ ternaryMemory original_valid actual_allocation
  have same : prepared = after := congrArg Prod.snd ran
  exact same.symm ▸ good

theorem older_allocations_preserved : prepared.memory.memory.heap.lookup 0 = original.memory.heap.lookup 0 ∧
    prepared.memory.memory.heap.lookup 2 = original.memory.heap.lookup 2 ∧
    prepared.memory.heap = original.heap ∧ prepared.graph = Semantic.Tests.caller.graph := ⟨by rfl', by rfl', rfl, rfl⟩

def caller : World Nat := { Semantic.Tests.caller with graph := { Semantic.Tests.wordGraph with
  read := fun id => if id = 99 then some 2 else if id = 98 then some 0 else Semantic.Tests.wordGraph.read id } }
def run (site : Site := .addition) (source : View := source) (external : External Nat := success) :=
  zigLiteral site external 160 7 (Semantic.Tests.callbacks Semantic.Tests.meaning (if site == .addition then 99 else 98))
    Caller.Tests.queries source 2 caller

theorem both_literal_results : (run .addition).1 = .ok 99 ∧ (run .multiplication).1 = .ok 98 := ⟨by rfl', by rfl'⟩
theorem offset_borrow_succeeds : (run .multiplication ⟨0, 1, 2⟩).1 = .ok 98 ∧
    (run .multiplication ⟨0, 1, 2⟩).2.memory.memory.heap.lookup 0 = original.memory.heap.lookup 0 := ⟨by rfl', by rfl'⟩
theorem success_unwinds : (run).2.memory.memory.heap = original.memory.heap ∧
    (run).2.memory.memory.nextId > 4 := ⟨by rfl', by decide +kernel⟩
theorem ordinary_oom_unwinds : (run .addition source (external (fun _ => true))).1 = .error (.language .outOfMemory) ∧
    (run .addition source (external (fun _ => true))).2.memory.memory.heap = original.memory.heap := ⟨by rfl', by rfl'⟩

/-- Provenance remains observable when logical words coincide. -/
def observedCallbacks : Primitives Nat := { Semantic.Tests.callbacks Semantic.Tests.meaning 99 with
  simplify := fun key slice before =>
    if Compiler.ZigAir.Memory.load before.memory.memory ((view slice).pointer 0) = .ok (number 3) ∧
       Compiler.ZigAir.Memory.load before.memory.memory ((view slice).pointer 1) = .ok (number 1) ∧
       Compiler.ZigAir.Memory.load before.memory.memory ((view slice).pointer 2) = .ok (number 2) then
      (Semantic.Tests.callbacks Semantic.Tests.meaning 99).simplify key slice before
    else (.error .missingHandle, before) }
def observed := zigLiteral .addition success 160 7 observedCallbacks Caller.Tests.queries source 2 caller
theorem physical_ids_observed : observed.1 = .ok 99 := by rfl'

theorem short_length_rejects_before_allocation : run .addition ⟨0, 0, 1⟩ =
    (.error (.memory (.preparation (.memory .sourceBounds))), caller) := by rfl'
theorem long_length_rejects_before_allocation : run .addition ⟨0, 0, 3⟩ =
    (.error (.memory (.preparation (.memory .sourceBounds))), caller) := by rfl'
theorem first_load_rejects_before_allocation : run .addition ⟨99, 0, 2⟩ =
    (.error (.memory (.preparation (.memory .unallocated))), caller) := by rfl'
theorem second_load_rejects_before_allocation : run .addition ⟨0, 2, 2⟩ =
    (.error (.memory (.preparation (.memory .memoryValidity))), caller) := by rfl'

theorem stack_limit_remains_rejection : zigLiteral .addition success 160 7
    (Semantic.Tests.callbacks Semantic.Tests.meaning 99) Caller.Tests.queries source 2 TemporaryUnary.Tests.exhausted =
    (.error (.memory (.preparation (.memory .outOfMemory))), TemporaryUnary.Tests.exhausted) ∧
    ordinary (zigLiteral .addition success 160 7 (Semantic.Tests.callbacks Semantic.Tests.meaning 99)
      Caller.Tests.queries source 2 TemporaryUnary.Tests.exhausted).1 = false := ⟨by rfl', by rfl'⟩

def pairWorld : World Nat := { caller with memory := { original with memory := before.memory } }
def prefixReject := writeTriple ⟨3, 0, 3⟩ 3 1 2 pairWorld
theorem third_store_rejects_with_pair_prefix : prefixReject.1 = .error (.memory (.preparation (.memory .memoryValidity))) ∧
    Compiler.ZigAir.Memory.load prefixReject.2.memory.memory ((⟨3, 0, 2⟩ : View).pointer 0) = .ok (number 3) ∧
    Compiler.ZigAir.Memory.load prefixReject.2.memory.memory ((⟨3, 0, 2⟩ : View).pointer 1) = .ok (number 1) :=
  ⟨by rfl', by rfl', by rfl'⟩

def parent := (TemporaryArguments.prepare 3 1 caller).2
def nested := zigLiteral .addition success 160 7 (Semantic.Tests.callbacks Semantic.Tests.meaning 99)
  Caller.Tests.queries ⟨3, 0, 2⟩ 2 parent
theorem parent_stack_borrow_survives : nested.1 = .ok 99 ∧
    nested.2.memory.memory.heap.lookup 3 = parent.memory.memory.heap.lookup 3 ∧
    nested.2.memory.memory.nextId > parent.memory.memory.nextId := ⟨by rfl', by rfl', by decide +kernel⟩

theorem source_represented : Represents original.memory source [3, 1] := by
  refine ⟨rfl, ?_⟩
  intro index inside
  have alternatives : index = 0 ∨ index = 1 := by change index < 2 at inside; omega
  rcases alternatives with zero | one <;> subst index <;> rfl'

theorem addition_body : run = borrowed success 160 7 (Semantic.Tests.callbacks Semantic.Tests.meaning 99)
    Caller.Tests.queries (opcode .addition) source 2 caller := rfl

theorem nonvacuous_borrowed_constructor_contract : run.1 = .ok 99 ∧ Valid run.2.memory ∧
    Semantic.Ensures Semantic.Tests.meaning caller.graph run.1 run.2.graph (fun id graph => graph.read id = some 2) := by
  have checked := borrowed_verified success 160 7 (Semantic.Tests.callbacks Semantic.Tests.meaning 99)
    Caller.Tests.queries (opcode .addition) source 3 1 2 caller _ ternaryMemory
    Compiler.Extraction.Recursive.Tests.base 2 original_valid source_represented actual_allocation
    (external_admitted _) (Semantic.Tests.ownership _ _) (Semantic.Tests.semantics _ _)
    ⟨(by intro _ _ impossible; cases impossible), trivial⟩ (by rfl')
  have completed : ordinary (borrowed success 160 7 (Semantic.Tests.callbacks Semantic.Tests.meaning 99)
      Caller.Tests.queries (opcode .addition) source 2 caller).1 = true := by
    rw [← addition_body, both_literal_results.1]
    rfl
  rw [addition_body]
  exact ⟨addition_body ▸ both_literal_results.1, checked completed⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryTernary.RuleLiteral.Tests
