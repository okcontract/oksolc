/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerOwnedCleanup

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

structure ReadyToClose (allocator : Nat) (source : View) (values : List NodeId) (before : State σ) : Prop where
  good : Good source values before.world
  detached : ∃ handle, before.scope.lookup = some handle ∧ handle.owned = none
  live : ∀ slice, before.scope.slice = some slice → before.scope.handedOff = false →
    SliceValid allocator before.world.memory.heap slice
  separate : ∀ slice, before.scope.slice = some slice → values ≠ [] → source.allocation ≠ slice.address

/-- The callback key carries the exact list whose physical ownership is being
transferred. No assumption about the key or final normalization is introduced. -/
theorem key_arguments (request : Interner.Request) (values : List NodeId) (key : Key)
    (made : Interner.makeKey request values = .ok key) : key.arguments = values := by
  by_cases operation : keyCode.instructionTest.run request.item = true
  · cases instruction : request.item.instruction with
    | none => simp [Interner.makeKey, KeyCode.run, operation, instruction] at made
    | some opcode =>
      simp [Interner.makeKey, KeyCode.run, operation, instruction] at made
      cases made
      rfl
  · simp [Interner.makeKey, KeyCode.run, operation] at made
    cases made
    rfl

theorem post_ready (allocator : Nat) (source : View) (values : List NodeId) (slice : ArgumentSlice) (handle : Handle)
    (execution : Except Fault α × State σ) (post : Post allocator source values slice handle execution)
    (detached : handle.owned = none) (apart : values ≠ [] → source.allocation ≠ slice.address)
    (completed : ordinary execution.1 = true) : ReadyToClose allocator source values execution.2 := by
  refine ⟨(post.2.2 completed).1, ⟨handle, post.1, detached⟩, ?_, ?_⟩
  · intro output same
    rw [post.2.1] at same; cases same
    exact (post.2.2 completed).2
  · intro output same
    rw [post.2.1] at same; cases same
    exact apart

theorem body_split (external : External σ) (allocator : Nat) (p : Primitives σ) (request : Interner.Request)
    (deterministic : Bool) (handle : Handle) (before : World σ) :
    body external allocator p request handle.values deterministic ⟨before, { lookup := some handle }⟩ =
      let (result, memory) := takeOwned normalizationOwnershipCode external allocator handle before.memory
      let world := { before with memory }
      match result with
      | .error failure => (.error (memoryFault failure), ⟨world, { lookup := some handle }⟩)
      | .ok (slice, remaining) =>
        let after : State σ := ⟨world, ⟨some remaining, some slice, false⟩⟩
        match Interner.makeKey request handle.values with
        | .error error => (.error (.language error), after)
        | .ok key => Interner.findCode.controlMiss (execution external allocator p) request key deterministic after := by
  cases taken : takeOwned normalizationOwnershipCode external allocator handle before.memory with
  | mk result memory =>
    cases result with
    | error failure => simp [body, Interner.FindCode.controlOwned, execution, take, taken, bind, Effect.bind]
    | ok pair =>
      rcases pair with ⟨slice, remaining⟩
      cases keyed : Interner.makeKey request handle.values <;>
        simp [body, Interner.FindCode.controlOwned, execution, take, taken, keyed, bind, Effect.bind, Except.mapError]

/-- The actual successful take and key construction select the only miss
obligation. Allocation failure and invalid keys use the existing cleanup proofs. -/
theorem body_ready_at (external : External σ) (allocator : Nat) (p : Primitives σ) (request : Interner.Request)
    (deterministic : Bool) (handle : Handle) (source : View) (values : List NodeId) (before : World σ)
    (ready : Ready allocator source values handle before.memory) (admitted : Admitted external)
    (miss : ∀ memory slice remaining key,
      takeOwned normalizationOwnershipCode external allocator handle before.memory = (.ok (slice, remaining), memory) →
      Interner.makeKey request handle.values = .ok key → key.arguments = slice.items →
      Held allocator source values slice ({before with memory} : World σ) →
      Post allocator source values slice remaining
        (Interner.findCode.controlMiss (execution external allocator p) request key deterministic
          ⟨{before with memory}, ⟨some remaining, some slice, false⟩⟩)) :
    let execution := body external allocator p request handle.values deterministic ⟨before, { lookup := some handle }⟩
    ordinary execution.1 = true → ReadyToClose allocator source values execution.2 := by
  rw [body_split]
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
        (miss memory slice remaining key taken keyed aligned held)
        post.detached post.separate completed

/-- Uniform graph contracts specialize the same reached-miss composition. -/
theorem body_ready (external : External σ) (allocator : Nat) (p : Primitives σ) (request : Interner.Request)
    (deterministic : Bool) (handle : Handle) (source : View) (values : List NodeId) (before : World σ)
    (ready : Ready allocator source values handle before.memory) (admitted : Admitted external)
    (contracts : Contracts allocator source values p) :
    let execution := body external allocator p request handle.values deterministic ⟨before, { lookup := some handle }⟩
    ordinary execution.1 = true → ReadyToClose allocator source values execution.2 :=
  body_ready_at external allocator p request deterministic handle source values before ready admitted
    (fun memory slice remaining key _ _ aligned held =>
      miss_post external allocator p source values contracts request key slice remaining deterministic
        ({before with memory} : World σ) aligned held)

/-- No output slice means failed takeOwned, so detached lookup destruction
does not undo the allocator's ordinary-OOM effects. -/
theorem finish_ready (external : External σ) (allocator : Nat) (source : View) (values : List NodeId)
    (before : State σ) (result : Except Fault α) (ready : ReadyToClose allocator source values before)
    (completed : ordinary result = true) :
    ∃ after, finish external allocator result before = (result, after) ∧
      Good source values after.world ∧ Closed after.scope ∧ after.world.graph = before.world.graph ∧
      (before.scope.slice = none → after.world = before.world) ∧
      (∀ slice, before.scope.slice = some slice → CleanupPost external allocator source values slice before after) := by
  obtain ⟨handle, present, detached⟩ := ready.detached
  cases output : before.scope.slice with
  | none =>
    let after := { before with scope := { before.scope with lookup := none } }
    have closed : cleanup external allocator before = (.ok (), after) := by
      cases handed : before.scope.handedOff <;>
        simpa only [cleanup, handed, Bool.false_eq_true, ↓reduceIte, output, after] using
          deinit_detached external allocator before handle present detached
    exact ⟨after, by simp only [finish, completed, ↓reduceIte, closed], ready.good,
      ⟨rfl, Or.inr output⟩, rfl, fun _ => rfl, by intro slice impossible; cases impossible⟩
  | some slice =>
    obtain ⟨after, closed, post⟩ := finish_taken external allocator source values slice handle before result completed present detached
      output ready.good (ready.live slice output) (ready.separate slice output)
    refine ⟨after, closed, post.good, post.closed, post.graph, ?_, ?_⟩
    · intro impossible; cases impossible
    · intro other same; cases same; exact post

/-- The complete source-bound owned continuation preserves the actual body
result. Ordinary outcomes close caller ownership using the callback's reached
memory; semantic faults retain that exact state without deferred cleanup.
Graph contracts are explicit pending implementation obligations. -/
theorem run_verified (external : External σ) (allocator : Nat) (p : Primitives σ) (request : Interner.Request)
    (deterministic : Bool) (handle : Handle) (source : View) (values : List NodeId) (before : World σ)
    (ready : Ready allocator source values handle before.memory) (admitted : Admitted external)
    (contracts : Contracts allocator source values p) :
    let bodyResult := body external allocator p request handle.values deterministic ⟨before, { lookup := some handle }⟩
    let execution := run external allocator p request deterministic handle before
    execution.1 = bodyResult.1 ∧
      (ordinary bodyResult.1 = false → execution.2 = bodyResult.2) ∧
      (ordinary bodyResult.1 = true → Good source values execution.2.world ∧ Closed execution.2.scope ∧
        execution.2.world.graph = bodyResult.2.world.graph ∧
        (bodyResult.2.scope.slice = none → execution.2.world = bodyResult.2.world) ∧
        (∀ slice, bodyResult.2.scope.slice = some slice →
          CleanupPost external allocator source values slice bodyResult.2 execution.2)) := by
  have checked := body_ready external allocator p request deterministic handle source values before ready admitted contracts
  cases ran : body external allocator p request handle.values deterministic ⟨before, { lookup := some handle }⟩ with
  | mk result reached =>
    rw [ran] at checked
    simp only [run, ran]
    cases completed : ordinary result with
    | false => simp [finish_semantic external allocator result reached completed]
    | true =>
      obtain ⟨after, closed, post⟩ := finish_ready external allocator source values reached result (checked completed) completed
      simp only [closed]
      simpa using post

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
