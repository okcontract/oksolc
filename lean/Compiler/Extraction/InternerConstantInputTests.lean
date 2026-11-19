/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursivePublicationTests
import Compiler.Extraction.InternerReachablePrefixTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ConstantInputTests
open Compiler.Algebraic Contract.Yul

abbrev initial (safety : Bool) := ReachablePrefixTests.before safety 3

/-- The existing constructor call with its actual arbitrary Push value. -/
def call (safety : Bool) (value : Word) : RecursiveTests.Call :=
  ⟨Interner.constructorCode.constantRequest value, ⟨0, 0, 0⟩, initial safety⟩

def allocated (safety : Bool) :=
  ((Compiler.ZigAir.Memory.allocate (initial safety).memory.memory AssemblyItem.viewType).toOption.map Prod.snd).getD
    (initial safety).memory.memory

/-- A capacity witness only. The actual scratch allocation below runs after
complete field assignment and retains that reached heap. -/
def scratchReference (safety : Bool) :=
  ((Compiler.ZigAir.Memory.allocate (allocated safety) (.array 2 Compiler.ZigAir.Memory.WordArray.word)).toOption.map Prod.snd).getD
    (allocated safety)

theorem allocations (safety : Bool) :
    Compiler.ZigAir.Memory.allocate (initial safety).memory.memory AssemblyItem.viewType =
      .ok (.pointer (.pointer true false AssemblyItem.viewType) ⟨(initial safety).memory.memory.nextId, 0⟩, allocated safety) ∧
    Compiler.ZigAir.Memory.allocate (allocated safety) (.array 2 Compiler.ZigAir.Memory.WordArray.word) =
      .ok (.pointer (.pointer true false (.array 2 Compiler.ZigAir.Memory.WordArray.word))
        ⟨(initial safety).memory.memory.nextId + 1, 0⟩, scratchReference safety) := by
  cases safety <;> constructor <;> insertion_kernel_rfl

attribute [local irreducible] ReachablePrefixTests.before

/-- Typed assignment derives the complete native item for every word. -/
theorem prepared (safety : Bool) (value : Word) :
    prepare (call safety value).request.item RecursiveTests.debug (initial safety) =
      (.ok (call safety value).address, (call safety value).constructed) ∧
    Prepared (call safety value).request.item RecursiveTests.debug (initial safety) (call safety value).constructed := by
  have prior := (ReachablePrefixTests.initialized_prefix safety 3 (by decide)).facts
  obtain ⟨after, made, post⟩ := prepare_verified (call safety value).request.item RecursiveTests.debug (initial safety)
    _ _ prior.valid (by change (2 : Int) ∈ AssemblyItem.itemTagValues; decide)
    AssemblyItem.Initializers.Tests.debug_valid (allocations safety).1
  have same : after = (call safety value).constructed := (congrArg Prod.snd made).symm
  rw [same] at made post
  exact ⟨made, post⟩

/-- Assignment preserves the allocation counter; reuse only the capacity
witness and derive the actual scratch pointer, heap and lifetime. -/
theorem stack (safety : Bool) (value : Word) :
    Compiler.ZigAir.Memory.allocate (call safety value).constructed.memory.memory
      (.array 2 Compiler.ZigAir.Memory.WordArray.word) =
      .ok (.pointer (.pointer true false (.array 2 Compiler.ZigAir.Memory.WordArray.word))
        ⟨(call safety value).before.memory.memory.nextId + 1, 0⟩, (call safety value).stack) ∧
    (call safety value).stack.nextAddress = (scratchReference safety).nextAddress := by
  have current := (prepared safety value).2
  obtain ⟨p, allocationMemory, allocation, counter⟩ := current.allocation
  have same : allocationMemory = allocated safety :=
    congrArg Prod.snd (Except.ok.inj (allocation.symm.trans (allocations safety).1))
  have address : (call safety value).constructed.memory.memory.nextAddress = (allocated safety).nextAddress :=
    counter.trans (congrArg Compiler.ZigAir.Memory.State.nextAddress same)
  have valid := Compiler.ZigAir.Memory.allocate_preserves_valid _ _ _ _ (allocations safety).1
  obtain ⟨pointer, scratch, ran, counter⟩ := Compiler.ZigAir.Memory.allocate_at_same_address _ _ _ current.valid.memory valid address _ _ (allocations safety).2
  have shape := Compiler.ZigAir.Memory.allocate_pointer _ _ _ _ ran
  have stack : (call safety value).stack = scratch := by
    unfold RecursiveTests.Call.stack
    rw [ran]; rfl
  rw [shape.1, current.nextId, ← stack] at ran
  exact ⟨ran, (congrArg Compiler.ZigAir.Memory.State.nextAddress stack).trans counter⟩

attribute [local irreducible] RecursiveTests.Call.constructed RecursiveTests.Call.stack

/-- Push keeps the empty source view; taking the empty owner retains its
actual reached counter and performs no hidden allocation or copy. -/
theorem normalized (safety : Bool) (value : Word) :
    (call safety value).prepared.1 = .ok [] ∧
    (call safety value).taken.1 = .ok () ∧
    (call safety value).taken.2.scope =
      ⟨some (call safety value).lookup, some (call safety value).normalized, false⟩ ∧
    (call safety value).taken.2.world =
      { (call safety value).constructed with memory :=
        { (call safety value).constructed.memory with memory := (call safety value).stack } } :=
  (call safety value).normalized_empty rfl rfl rfl (prepared safety value).2 (stack safety value).1

theorem missed (safety : Bool) (value : Word) :
    (call safety value).before.graph.table (call safety value).key = none := by
  have functions : (fun value : Word => (call safety value).before.graph.table (call safety value).key) =
      (fun _ : Word => (none : Option NodeId)) := by
    cases safety <;> insertion_kernel_rfl
  exact congrFun functions value

/-- Assemble the caller prefix from native preparation, allocation and
ownership, without evaluating an arbitrary word through the whole state. -/
theorem observed (safety : Bool) (value : Word) :
    (call safety value).observations = (call safety value).expected := by
  have prepared := prepared safety value
  have normalized := normalized safety value
  simp only [RecursiveTests.Call.observations, RecursiveTests.Call.expected, Prod.mk.injEq]
  exact ⟨congrArg Prod.fst prepared.1, prepared.2.nextId, (stack safety value).1,
    normalized.1, normalized.2.1, normalized.2.2.1, missed safety value, rfl⟩

theorem established (safety : Bool) (value : Word) :
    (call safety value).Established safety ReachablePrefixTests.backing 5 (ReachablePrefixTests.cells safety 3) := by
  have prior := ReachablePrefixTests.initialized_prefix safety 3 (by decide)
  exact (call safety value).establish safety ReachablePrefixTests.backing 5 (ReachablePrefixTests.cells safety 3) prior.facts
    (by rw [prior.count]; decide) (RecursiveTests.empty_good _ prior.facts.valid)
    (by change (2 : Int) ∈ AssemblyItem.itemTagValues; decide) (observed safety value)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ConstantInputTests
