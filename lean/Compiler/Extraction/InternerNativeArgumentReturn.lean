/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeFrames

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage

theorem FramePost.project {frame : World σ → Prop} {actual : Except Fault α × State σ}
    (post : FramePost frame actual) :
    ordinary actual.1 = true → frame actual.2.world := fun completed => (post completed).2

/-- Retire an actual argument wrapper's original mark after ordinary return.
The reached graph may have grown or relocated; the enclosing parent supplies
only its cleanup law. Semantic clients share this native frame proof. -/
theorem FramePost.unwind {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {parent : World (Publication.Effects σ) → Prop} {actual : Except Fault NodeId × State (Publication.Effects σ)}
    (post : FramePost (GraphFrame safety allocator owner rows parent) actual)
    (mark : Nat) (older : owner < mark)
    (localParent : ∀ world, parent world → parent { world with memory := { world.memory with
      memory := Compiler.ZigAir.Memory.cleanup mark world.memory.memory } }) :
    let returned := TemporaryArguments.unwind mark actual
    ordinary returned.1 = true → GraphFrame safety allocator owner rows parent returned.2 := by
  dsimp only
  intro completed
  change ordinary actual.1 = true at completed
  obtain ⟨_, frame⟩ := post completed
  obtain ⟨added, data, capacity, facts⟩ := frame.1
  simp only [TemporaryArguments.unwind, completed, ↓reduceIte]
  exact ⟨⟨added, data, capacity, facts.cleanup mark older⟩, localParent _ frame.2⟩

/-- Empty literal wrappers have no argument allocation to retire. Both return
routes use the same actual result and reached native world. -/
theorem FramePost.returned {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {parent : World (Publication.Effects σ) → Prop} {actual : Except Fault NodeId × State (Publication.Effects σ)}
    (post : FramePost (GraphFrame safety allocator owner rows parent) actual)
    (values : List NodeId) (mark : Nat) (older : owner < mark)
    (localParent : ∀ world, parent world → parent { world with memory := { world.memory with
      memory := Compiler.ZigAir.Memory.cleanup mark world.memory.memory } }) :
    let returned := Arguments.returned values mark actual
    ordinary returned.1 = true → GraphFrame safety allocator owner rows parent returned.2 := by
  unfold Arguments.returned
  split
  · exact post.project
  · exact post.unwind mark older localParent

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
