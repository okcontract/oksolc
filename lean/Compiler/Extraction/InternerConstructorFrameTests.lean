/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorFrame
import Compiler.Extraction.InternerPhysicalTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorFrame.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open Normalization.Tests

def run (known : NodeId) (budget : Nat := 160) :=
  operation success budget 7 (Semantic.Tests.callbacks Semantic.Tests.meaning known) Caller.Tests.queries
    Semantic.Tests.source 1 [3, 1] Semantic.Tests.caller

theorem success_observation : (run 42).1 = .ok 42 ∧ (run 42).2.world.graph.read 42 = some 42 ∧
    (run 42).2.world.memory.effects = 225 ∧ (run 42).2.world.memory.memory.heap = original.memory.heap ∧
    (run 42).2.world.memory.memory.nextId = 7 := ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem failure_observation : (run 1).1 = .error (.language .outOfMemory) ∧
    (run 1).2.world.memory.effects = 225 ∧ (run 1).2.world.memory.memory.heap = original.memory.heap :=
  ⟨by rfl', by rfl', by rfl'⟩

theorem scratch_fault_retained : (run 42 0).1 = .error (.memory (.preparation .incomplete)) ∧
    ((run 42 0).2.world.memory.memory.heap.lookup 3).isSome = true := ⟨by rfl', by rfl'⟩

theorem contract (known : NodeId) (budget : Nat) :
    Post Semantic.Tests.meaning Semantic.Tests.source [3, 1] Semantic.Tests.caller (run known budget) 42 :=
  operation_verified success budget 7 (Semantic.Tests.callbacks Semantic.Tests.meaning known) Caller.Tests.queries
    Semantic.Tests.source 1 [3, 1] Semantic.Tests.caller Compiler.Extraction.Recursive.Tests.base 42
    ⟨original_valid, Semantic.Tests.source_represented⟩ (external_admitted _)
    (Semantic.Tests.ownership _ _ _ _) (Semantic.Tests.semantics _ _ _ _) Semantic.Tests.graph_valid (by rfl')

theorem success_preserves_borrow : Represents (run 42).2.world.memory.memory Semantic.Tests.source [3, 1] := by
  have completed : ordinary (run 42).1 = true := by rw [success_observation.1]; rfl
  exact (contract 42 160 completed).1.2

theorem failure_preserves_borrow : Represents (run 1).2.world.memory.memory Semantic.Tests.source [3, 1] := by
  have completed : ordinary (run 1).1 = true := by rw [failure_observation.1]; rfl
  exact (contract 1 160 completed).1.2

def subslice : View := ⟨0, 1, 1⟩
/-- Observe the physical operand at the callback boundary, before the existing
fixture consumes it. This distinguishes an offset view from equal logical IDs. -/
def subCallbacks : Primitives Nat :=
  { Semantic.Tests.callbacks Semantic.Tests.meaning 42 with simplify := fun key slice before =>
    if (Compiler.ZigAir.Memory.load before.memory.memory ((view slice).pointer 0)) = .ok (number 1) then
      (Semantic.Tests.callbacks Semantic.Tests.meaning 42).simplify key slice before
    else (.error .missingHandle, before) }
def subcall := operation success 160 7 subCallbacks Caller.Tests.queries
  subslice 0x19 [1] Semantic.Tests.caller

theorem subslice_observation : subcall.1 = .error (.language .outOfMemory) ∧
    subcall.2.world.memory.effects = 215 ∧ subcall.2.world.memory.memory.heap = original.memory.heap :=
  ⟨by rfl', by rfl', by rfl'⟩

def orderedWorld : World Nat := { Semantic.Tests.caller with graph := { Semantic.Tests.wordGraph with
  read := fun id => some (if id = 42 then 22 else if id = 3 then 32 else 10) } }
def orderedCall := operation success 160 7 (Semantic.Tests.callbacks Semantic.Tests.meaning 42) Caller.Tests.queries
  Semantic.Tests.source 3 [3, 1] orderedWorld

theorem ordered_arguments : orderedCall.1 = .ok 42 ∧ orderedCall.2.world.graph.read 42 = some 22 :=
  ⟨by rfl', by rfl'⟩

def exhausted : World Nat := { Semantic.Tests.caller with memory := { original with
  memory := { original.memory with nextAddress := Compiler.ZigAir.Memory.addressLimit - 4 } } }
def full := operation success 160 7 (Semantic.Tests.callbacks Semantic.Tests.meaning 42)
  { Caller.Tests.queries with atCapacity := fun _ => true } Semantic.Tests.source 1 [3, 1] exhausted
def noStack := operation success 160 7 (Semantic.Tests.callbacks Semantic.Tests.meaning 42)
  Caller.Tests.queries Semantic.Tests.source 1 [3, 1] exhausted

theorem capacity_before_scratch : full.1 = .error (.language .capacity) ∧ full.2.world = exhausted := ⟨rfl, rfl⟩

theorem stack_exhaustion_is_rejected : noStack.1 = .error (.memory (.preparation (.memory .outOfMemory))) ∧
    ordinary noStack.1 = false ∧ noStack.2.world = exhausted := ⟨by rfl', by rfl', by rfl'⟩

def innerCall (known : NodeId) := operation success 160 7
  (Semantic.Tests.callbacks Semantic.Tests.meaning known) Caller.Tests.queries
  Semantic.Tests.source 1 [3, 1] Semantic.Tests.world

theorem nested_parent_frame_survives :
    (innerCall 42).2.world.memory.memory.heap.lookup 3 = some scratchCell ∧
    (innerCall 42).2.world.memory.memory.heap = before.memory.heap ∧
    (innerCall 1).2.world.memory.memory.heap = before.memory.heap := ⟨by rfl', by rfl', by rfl'⟩

theorem success_restores_good : Good Semantic.Tests.source [3, 1] (run 42).2.world := by
  have completed : ordinary (run 42).1 = true := by rw [success_observation.1]; rfl
  exact (contract 42 160 completed).1

theorem failure_restores_good : Good Semantic.Tests.source [3, 1] (run 1).2.world := by
  have completed : ordinary (run 1).1 = true := by rw [failure_observation.1]; rfl
  exact (contract 1 160 completed).1

/-- Existence alone allows escaping stack-backed registry entries; the persistent
invariant rejects them before execution. This is an invariant counterexample,
not evidence that the native compiler creates such an entry. -/
def escaping : Session Unit :=
  ⟨fun id => if id = 0 then some ⟨7, .bytes 8⟩ else none,
    ⟨[(0, ⟨4, .array 2 word, [], true, true⟩)], 1, 12⟩, ()⟩

theorem escaping_backed : Backed escaping.heap escaping.memory := by
  intro id block stored
  by_cases selected : id = 0
  · subst id; exact ⟨_, rfl⟩
  · simp [escaping, selected] at stored

theorem escaping_not_valid : ¬Valid escaping := by
  intro valid
  obtain ⟨cell, found, persistent⟩ := valid.injected 0 ⟨7, .bytes 8⟩ rfl
  have same : cell = ⟨4, .array 2 word, [], true, true⟩ := Option.some.inj found.symm
  cases same
  cases persistent

theorem backing_does_not_imply_safe_return :
    ¬Backed escaping.heap (Compiler.ZigAir.Memory.cleanup 0 escaping.memory) := by
  intro injected
  obtain ⟨cell, impossible⟩ := injected 0 ⟨7, .bytes 8⟩ rfl
  cases impossible

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorFrame.Tests
