/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerOwnedProduction

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Lift the existing load frame to a represented caller slice. This is used
when a nested normalization operation has preserved every old allocation. -/
theorem represented_retained (before after : Compiler.ZigAir.Memory.State) (source : View) (values : List NodeId)
    (represented : Represents before source values)
    (frame : ∀ id cell, before.heap.lookup id = some cell → after.heap.lookup id = some cell) :
    Represents after source values := by
  refine ⟨represented.1, ?_⟩
  intro index inside
  have read := represented.2 index inside
  cases accessed : Compiler.ZigAir.Memory.access before (source.address index) ⟨4, 4⟩ false with
  | error fault =>
    simp [Compiler.ZigAir.Memory.load, View.pointer, word, Compiler.ZigAir.Memory.Ty.layout, accessed, bind, Except.bind] at read
  | ok cell =>
    have found := (Compiler.ZigAir.Memory.access_success_region before _ _ false cell accessed).1
    exact (Compiler.ZigAir.Memory.load_eq_of_lookup before after true false word _ ((frame _ _ found).trans found.symm)).trans read

theorem held_retained (allocator : Nat) (source : View) (values : List NodeId) (slice : ArgumentSlice) (before after : World σ)
    (held : Held allocator source values slice before) (valid : Valid after.memory)
    (memoryFrame : ∀ id cell, before.memory.memory.heap.lookup id = some cell → after.memory.memory.heap.lookup id = some cell)
    (heapFrame : ∀ id block, before.memory.heap id = some block → after.memory.heap id = some block) :
    Held allocator source values slice after := by
  refine ⟨⟨valid, represented_retained _ _ source values held.1.2 memoryFrame⟩, ?_, held.2.2⟩
  rcases held.2.1 with empty | live
  · exact Or.inl empty
  · exact Or.inr (heapFrame _ _ live)

/-- A nested complete normalization lifecycle borrows the parent's owned slice,
duplicates it, and cleans its own copy. It may fail allocation ordinarily;
neither path overwrites the parent's handle or reuses its cleanup flag. -/
def nested (external : External σ) (allocator : Nat) (slice : ArgumentSlice) : GraphAction σ Unit := fun before =>
  let (result, memory) := Normalization.run normalizationOwnershipCode external 0 allocator false (view slice) ⟨0, 0, 0⟩ slice.items .cleanup before.memory
  let reached := { before with memory }
  match result with
  | .error failure => (.error (memoryFault failure), reached)
  | .ok _ => (.ok (), reached)

/-- This concrete nested callback discharges its borrow contract from the
normalization implementation theorem, including ordinary OOM and reached
allocation/free effects. No callback frame is assumed for the child. -/
theorem nested_held (external : External σ) (allocator : Nat) (source : View) (values : List NodeId)
    (slice : ArgumentSlice) (before : World σ) (held : Held allocator source values slice before) (admitted : Admitted external) :
    let (result, after) := nested external allocator slice before
    ordinary result = true ∧ Held allocator source values slice after := by
  have represented : Represents before.memory.memory (view slice) slice.items := by
    by_cases empty : slice.items = []
    · exact ⟨rfl, by intro index inside; simp [empty] at inside⟩
    · exact (held.1.1.related allocator slice.address slice.items empty (held.2.1.resolve_left empty)).2
  have ready : Ready allocator (view slice) slice.items ⟨view slice, slice.items, none⟩ before.memory := by
    refine ⟨held.1.1, represented, represented, ?_, ?_⟩
    · intro owned impossible; cases impossible
    · intro _ owned impossible; cases impossible
  obtain ⟨result, memory, ran, post⟩ := continue_refines external allocator (view slice) slice.items
    .cleanup ⟨view slice, slice.items, none⟩ before.memory ready admitted
  have executed : Normalization.run normalizationOwnershipCode external 0 allocator false (view slice) ⟨0, 0, 0⟩ slice.items .cleanup before.memory =
      (result, memory) := by simpa only [Normalization.run, init, Bool.not_false, Bool.true_or, ↓reduceIte] using ran
  have framed (id cell) (found : before.memory.memory.heap.lookup id = some cell) :=
    post.frame id cell found (by intro owned impossible; cases impossible)
  have preserved : Held allocator source values slice ({ before with memory } : World σ) := by
    apply held_retained allocator source values slice before _ held post.valid (fun id cell found => (framed id cell found).1)
    intro id block stored
    obtain ⟨cell, found, _persistent⟩ := held.1.1.injected id block stored
    exact (framed id cell found).2.trans stored
  simp only [nested, executed]
  cases result with
  | ok outcome => exact ⟨rfl, preserved⟩
  | error failure =>
    cases failure with
    | outOfMemory => exact ⟨rfl, preserved⟩
    | allocation | preparation | release => exact False.elim post.outcome

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
