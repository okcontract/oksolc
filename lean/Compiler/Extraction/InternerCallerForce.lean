/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInit

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

theorem publish_post (allocator : Nat) (p : Primitives σ) (source : View) (values : List NodeId)
    (contracts : Contracts allocator source values p) (key : Key) (slice : ArgumentSlice) (remaining : Handle)
    (id : NodeId) (before : World σ) (aligned : key.arguments = slice.items) (held : Held allocator source values slice before) :
    Post allocator source values slice remaining
      ((do let _ ← graph (fun slice => p.publish key slice id); handoff : Action σ Unit)
        ⟨before, ⟨some remaining, some slice, false⟩⟩) := by
  cases published : p.publish key slice id before with
  | mk result after =>
    have publication := contracts.publish key slice id before aligned held
    rw [published] at publication
    cases result with
    | error fault =>
      simp only [bind, Effect.bind, graph, published, Post]
      exact ⟨trivial, trivial, fun completed => ⟨(publication completed).1, fun _ => (publication completed).2 fault rfl⟩⟩
    | ok returned =>
      cases returned
      simp only [bind, Effect.bind, graph, published, handoff, Post]
      exact ⟨trivial, trivial, fun _ => ⟨(publication rfl).1, by intro impossible; cases impossible⟩⟩

theorem force_owned_split (external : External σ) (allocator : Nat) (p : Primitives σ) (request : Interner.Request)
    (id : NodeId) (handle : Handle) (before : World σ) :
    Interner.forceCode.controlOwned (OwnedCall.execution external allocator p) request handle.values id
        ⟨before, { lookup := some handle }⟩ =
      let (result, memory) := takeOwned normalizationOwnershipCode external allocator handle before.memory
      let world := { before with memory }
      match result with
      | .error failure => (.error (memoryFault failure), ⟨world, { lookup := some handle }⟩)
      | .ok (slice, remaining) =>
        let after : State σ := ⟨world, ⟨some remaining, some slice, false⟩⟩
        match Interner.makeKey request handle.values with
        | .error error => (.error (.language error), after)
        | .ok key => (do let _ ← graph (fun slice => p.publish key slice (Interner.forceCode.published.run id)); handoff : Action σ Unit) after := by
  cases taken : takeOwned normalizationOwnershipCode external allocator handle before.memory with
  | mk result memory =>
    cases result with
    | error failure => simp [Interner.ForceCode.controlOwned, OwnedCall.execution, take, taken, bind, Effect.bind]
    | ok pair =>
      rcases pair with ⟨slice, remaining⟩
      cases keyed : Interner.makeKey request handle.values <;>
        simp [Interner.ForceCode.controlOwned, OwnedCall.execution, take, taken, keyed, bind, Effect.bind, Except.mapError]

theorem force_owned_ready (external : External σ) (allocator : Nat) (p : Primitives σ) (request : Interner.Request)
    (id : NodeId) (handle : Handle) (source : View) (values : List NodeId) (before : World σ)
    (ready : Ready allocator source values handle before.memory) (admitted : Admitted external)
    (contracts : Contracts allocator source values p) :
    let execution := Interner.forceCode.controlOwned (OwnedCall.execution external allocator p) request handle.values id
      ⟨before, { lookup := some handle }⟩
    ordinary execution.1 = true → ReadyToClose allocator source values execution.2 := by
  rw [force_owned_split]
  obtain ⟨result, memory, taken, post⟩ := take_refines external allocator source values handle before.memory ready admitted
  rw [taken]
  cases result with
  | error failure =>
    cases failure with
    | outOfMemory =>
      refine fun _ => ⟨⟨post.2.2.2.valid, post.2.2.2.source⟩, ⟨handle, rfl, post.1⟩, ?_, ?_⟩
      · intro slice impossible; cases impossible
      · intro slice impossible; cases impossible
    | allocation | preparation | release => exact False.elim post
  | ok pair =>
    rcases pair with ⟨slice, remaining⟩
    have held : Held allocator source values slice ({ before with memory } : World σ) :=
      ⟨⟨post.ready.valid, post.ready.source⟩, post.live, post.separate⟩
    cases keyed : Interner.makeKey request handle.values with
    | error error =>
      refine fun _ => ⟨held.1, ⟨remaining, rfl, post.detached⟩, ?_, ?_⟩
      · intro output same _; cases same; exact held.2.1
      · intro output same; cases same; exact post.separate
    | ok key =>
      dsimp only
      intro completed
      have aligned := (key_arguments request handle.values key keyed).trans post.values.symm
      exact post_ready allocator source values slice remaining _
        (publish_post allocator p source values contracts key slice remaining (Interner.forceCode.published.run id) _ aligned held)
        post.detached post.separate completed

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
