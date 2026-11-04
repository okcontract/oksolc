/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeGraphPublication
import Compiler.Extraction.InternerNativeGraphCleanup

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- The production publication/handoff/outer-defer continuation, starting at
the world actually returned by children. Admission, replacement, OOM cleanup
and native graph preservation follow from that reached frame. Neither the
pre-child graph nor an enclosing preservation conclusion is a premise. -/
theorem Facts.finish_publication {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : OwnedCall.State (Publication.Effects σ)}
    {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before.world rows)
    (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ) (source : View) (values : List NodeId)
    (key : Key) (owned : ArgumentSlice) (handle : Handle) (id : NodeId) (accepted : Bool) (effects : σ)
    (scope : before.scope = ⟨some handle, some owned, false⟩) (detached : handle.owned = none)
    (aligned : key.arguments = owned.items) (held : Held allocator source values owned before.world)
    (custody : Caller.GraphCustody allocator owned rows before.world.memory)
    (privateSource : Caller.SourcePrivate source before.world.memory.effects.keys)
    (response : hostProbe key (Publication.forget before.world.memory) = (accepted, effects)) :
    ∃ published after,
      Publication.publish hostProbe host allocator source key owned id before.world =
        (if accepted then .ok () else .error (.language .outOfMemory), published) ∧
      (let (result, reached) :=
          (do let _ ← graph (fun slice => Publication.publish hostProbe host allocator source key slice id)
              handoff
              pure id : Action (Publication.Effects σ) NodeId) before
       OwnedCall.finish (Publication.external host) allocator result reached) =
        (if accepted then .ok id else .error (.language .outOfMemory), after) ∧
      OwnedCall.finish (Publication.external host) allocator
        (if accepted then .ok id else .error (.language .outOfMemory) : Except Fault NodeId)
        ⟨published, { before.scope with handedOff := accepted }⟩ =
          (if accepted then .ok id else .error (.language .outOfMemory), after) ∧
      Facts safety allocator owner data capacity after.world rows ∧
      CleanupPost (Publication.external host) allocator source values owned
        ⟨published, { before.scope with handedOff := accepted }⟩ after ∧
      after.world.memory.effects.keys = (if accepted then
        OwnedKeys.store before.world.memory.effects.keys key ⟨owned.address, id⟩ else before.world.memory.effects.keys) ∧
      (if accepted then SliceValid allocator after.world.memory.heap owned else Consumed owned after.world.memory) ∧
      (accepted = false → Caller.GraphCustody allocator owned rows published.memory) := by
  have publication := facts.publish hostProbe host source values key owned id accepted effects aligned held custody privateSource response
  let published := (Publication.publish hostProbe host allocator source key owned id before.world).2
  let reached : OwnedCall.State (Publication.Effects σ) := ⟨published, { before.scope with handedOff := accepted }⟩
  let result : Except Fault NodeId := if accepted then .ok id else .error (.language .outOfMemory)
  have called : Publication.publish hostProbe host allocator source key owned id before.world =
      (if accepted then .ok () else .error (.language .outOfMemory), published) := Prod.ext publication.1 rfl
  have pubFacts := publication.2.1
  have pubHeld := publication.2.2.1
  obtain ⟨after, finished, post⟩ := finish_taken (Publication.external host) allocator source values owned handle reached result
    (by cases accepted <;> rfl) (by simp only [reached, scope]) detached (by simp only [reached, scope])
    pubHeld.1 (fun _ => pubHeld.2.1) pubHeld.2.2
  have preserved := pubFacts.cleanup_post host owned post (fun _ => pubHeld.2.1)
    (by
      intro failed
      change accepted = false at failed
      rw [show published.memory.effects.keys = before.world.memory.effects.keys by
        simpa only [failed, Bool.false_eq_true, ↓reduceIte] using publication.2.2.2]
      exact custody.apart)
    (fun _ => custody.operands)
  refine ⟨published, after, called, ?_, finished, ?_, post, ?_⟩
  · cases accepted <;>
      simpa only [Effect.bind, graph, scope, called, handoff, Pure.pure, reached, result, scope] using finished
  · exact preserved.1
  · refine ⟨preserved.2.trans publication.2.2.2, ?_, ?_⟩
    · cases accepted with
      | true =>
        rw [post.handedOff rfl]
        exact pubHeld.2.1
      | false => exact (post.freed rfl).2
    · intro refused
      refine ⟨⟨pubHeld.2.1, ?_⟩, custody.operands⟩
      rw [publication.2.2.2, refused]
      exact custody.apart

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
