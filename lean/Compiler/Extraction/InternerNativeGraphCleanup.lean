/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeGraphFrame
import Compiler.Extraction.InternerOwnedCleanup

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Native graph preservation through the existing caller cleanup. A transferred
owner is retained; a private owner is released in the actual reached world.
The key table is framed by the existing publication allocator wrapper. -/
theorem Facts.cleanup_post {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before after : OwnedCall.State (Publication.Effects σ)}
    {rows : List Storage.Cell} {source : View} {values : List NodeId}
    (facts : Facts safety allocator owner data capacity before.world rows)
    (host : External σ) (owned : ArgumentSlice)
    (post : CleanupPost (Publication.external host) allocator source values owned before after)
    (live : before.scope.handedOff = false → SliceValid allocator before.world.memory.heap owned)
    (privateKey : before.scope.handedOff = false → OwnedKeys.Apart before.world.memory.effects.keys
      (fun address => owned.items ≠ [] ∧ address = owned.address))
    (privateOperands : before.scope.handedOff = false → owned.items ≠ [] →
      ∀ row ∈ rows, row.arguments ≠ [] → owned.address ≠ row.argumentsAddress) :
    Facts safety allocator owner data capacity after.world rows ∧
      after.world.memory.effects.keys = before.world.memory.effects.keys := by
  cases handed : before.scope.handedOff with
  | true => rw [post.handedOff handed]; exact ⟨facts, rfl⟩
  | false =>
    have freed := (post.freed handed).1
    obtain ⟨memory, ran, _, released, freeEffects⟩ := free_valid (Publication.external host) allocator owned
      before.world.memory facts.valid (live handed)
    have same : memory = after.world.memory := congrArg Prod.snd (ran.symm.trans freed)
    rw [same] at released freeEffects
    have keys : after.world.memory.effects.keys = before.world.memory.effects.keys := by
      rw [freeEffects]; split <;> rfl
    refine ⟨?_, keys⟩
    have world : after.world = { before.world with memory := after.world.memory } :=
      congrArg (fun graph => (⟨graph, after.world.memory⟩ : World (Publication.Effects σ))) post.graph
    rw [world]
    by_cases empty : owned.items = []
    · have unchanged : free (Publication.external host) allocator owned before.world.memory =
          (.ok (), before.world.memory) := free_empty _ _ _ _ empty
      have same : before.world.memory = after.world.memory := congrArg Prod.snd (unchanged.symm.trans freed)
      rw [← same]
      exact facts
    · exact facts.release owned after.world.memory empty (live handed) (privateKey handed)
        (privateOperands handed empty) post.good.1 released keys

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
