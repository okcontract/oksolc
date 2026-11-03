/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerGraphInitMemory
import Compiler.Extraction.InternerPublication

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.GraphInit.Ownership
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory

/-- The pinned `keyIterator` takes its zero-length branch on null metadata;
`FieldIterator.next` returns null before reading either undefined pointer.
This checked empty projection rejects nonempty and inconsistent fields. It is
not the still-open nonempty native bucket/ownership correspondence. -/
def keys (runtimeSafety : Bool) (memory : Compiler.ZigAir.Memory.State) (owner : Address) :
    Except Compiler.ZigAir.Memory.Fault OwnedKeys.Table := do
  Compiler.Extraction.ExpressionMap.Initialization.observeEmpty runtimeSafety memory owner
  .ok (fun _ => none)

/-- Construct ownership metadata for this newly initialized interner from the
native empty map. The input carries raw allocator effects, not an arbitrary
ownership table to erase. Existing caller allocations and effects are retained. -/
def run (runtimeSafety : Bool) (allocator : Nat) (before : Session σ) (owner sentinel : Address) :
    Except Compiler.ZigAir.Memory.Fault (Nat × World (Publication.Effects σ)) := do
  let initialized ← OwnerMemory.run runtimeSafety allocator before owner sentinel
  let table ← keys runtimeSafety initialized.2.memory.memory owner
  .ok (initialized.1, ⟨initialized.2.graph,
    ⟨initialized.2.memory.heap, initialized.2.memory.memory, ⟨table, initialized.2.memory.effects⟩⟩⟩)

structure Established (runtimeSafety : Bool) (allocator : Nat) (before : Session σ)
    (after : World (Publication.Effects σ)) (lifetime : Nat) (sentinel : Address) (meaning : Meaning) : Prop where
  valid : Valid after.memory
  invariant : Interner.Invariant meaning after.graph
  resident : Memory.GraphResident allocator after.memory.heap []
  representatives : after.graph.representatives = some []
  header : Compiler.Extraction.RepresentativeArray.readHeader after.memory.memory
    (Compiler.Extraction.RepresentativeArray.Owner.headerAddress ⟨lifetime, 0⟩) =
      .ok (.slice Compiler.Extraction.RepresentativeArray.itemsType sentinel 0, .scalar (.int false 64 0))
  registry : after.memory.heap = before.heap
  effects : after.memory.effects.allocator = before.effects
  nextId : after.memory.memory.nextId = before.memory.nextId
  nextAddress : after.memory.memory.nextAddress = before.memory.nextAddress
  frame : ∀ other, other ≠ lifetime → after.memory.memory.heap.lookup other = before.memory.heap.lookup other
  queries : ∀ key, Compiler.Extraction.ExpressionMap.getEmpty runtimeSafety after.memory.memory ⟨lifetime, 0⟩ key =
    .ok (after.graph.table key)
  nativeKeys : keys runtimeSafety after.memory.memory ⟨lifetime, 0⟩ = .ok after.memory.effects.keys
  live : OwnedKeys.Live allocator ⟨after.memory.effects.keys, after.memory.heap⟩
  unique : OwnedKeys.Unique after.memory.effects.keys
  projection : OwnedKeys.view after.memory.effects.keys = after.graph.table
  shape : before.memory.heap.RetainsShape after.memory.memory.heap
  unlocked : Compiler.Extraction.RepresentativeArray.Owner.NativeLock.checkUnlocked runtimeSafety after.memory.memory ⟨lifetime, 0⟩ = .ok ()

/-- Native initialization derives the initial global ownership and semantic
projection needed by publication. No initialized table, live/unique predicate,
final graph correspondence or successful execution is assumed. -/
theorem initialize_verified (runtimeSafety : Bool) (allocator : Nat) (before : Session σ) (lifetime : Nat)
    (cell : Compiler.ZigAir.Memory.Allocation) (sentinel : Address) (meaning : Meaning) (valid : Valid before)
    (found : before.memory.heap.lookup lifetime = some cell)
    (typed : cell.type = Compiler.Extraction.RepresentativeArray.Owner.viewType runtimeSafety)
    (writable : cell.writable = true) (stack : cell.stack = true) :
    ∃ after, run runtimeSafety allocator before ⟨lifetime, 0⟩ sentinel = .ok (allocator, after) ∧
      Established runtimeSafety allocator before after lifetime sentinel meaning := by
  obtain ⟨initialized, executed, validAfter, invariant, resident, representatives, header, registry, effects,
    nextId, nextAddress, frame, count, queries, observed, shape, unlocked⟩ :=
    OwnerMemory.initialize_verified runtimeSafety allocator before lifetime cell sentinel meaning valid found typed writable stack
  have projected : keys runtimeSafety initialized.memory.memory ⟨lifetime, 0⟩ = .ok (fun _ => none) := by
    simp only [keys, observed, bind, Except.bind]
  let after : World (Publication.Effects σ) := ⟨initialized.graph,
    ⟨initialized.memory.heap, initialized.memory.memory, ⟨fun _ => none, initialized.memory.effects⟩⟩⟩
  refine ⟨after, ?_, ⟨validAfter.memory, validAfter.related, validAfter.injected⟩, invariant, resident,
    representatives, header, registry, effects, nextId, nextAddress, frame, queries, projected, ?_, ?_, ?_, shape, unlocked⟩
  · simp only [run, executed, projected, bind, Except.bind, after]
  · intro key entry impossible; cases impossible
  · intro a x b y impossible; cases impossible
  · funext key
    have native := Compiler.Extraction.ExpressionMap.empty_get runtimeSafety initialized.memory.memory ⟨lifetime, 0⟩ key count
    exact (Except.ok.inj ((queries key).symm.trans native)).symm

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.GraphInit.Ownership
