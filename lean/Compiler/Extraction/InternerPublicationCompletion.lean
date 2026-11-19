/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerPublicationInput
import Compiler.Extraction.InternerPublicationSuccess

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Facts at the outer defer boundary of the production publication
continuation. The initial world precedes normalization; `taken` is the actual
world presented to publication. Native map/probe binding remains separate. -/
structure Completion (host : External σ) (allocator : Nat) (source : View)
    (request : Interner.Request) (key : Key) (owned : ArgumentSlice) (id : NodeId)
    (before taken : World (Effects σ)) (accepted : Bool) (effects : σ) (after : State (Effects σ)) : Prop where
  good : Good source request.arguments after.world
  scope : after.scope = if accepted then ⟨none, some owned, true⟩ else ⟨none, none, false⟩
  graph : after.world.graph = if accepted then { taken.graph with table := Cache.put equalityFields taken.graph.table key id } else taken.graph
  keys : after.world.memory.effects.keys = if accepted then OwnedKeys.store taken.memory.effects.keys key ⟨owned.address, id⟩ else taken.memory.effects.keys
  live : OwnedKeys.Live allocator ⟨after.world.memory.effects.keys, after.world.memory.heap⟩
  unique : OwnedKeys.Unique after.world.memory.effects.keys
  incoming : if accepted then SliceValid allocator after.world.memory.heap owned else Consumed owned after.world.memory
  nextId : after.world.memory.memory.nextId = taken.memory.memory.nextId
  nextAddress : after.world.memory.memory.nextAddress = taken.memory.memory.nextAddress
  effects : after.world.memory.effects.allocator = if accepted then
    match taken.memory.effects.keys key with
    | none => effects
    | some old => if key.arguments.isEmpty then effects else host.free (OwnedKeys.slice key old) { forget taken.memory with effects }
    else if owned.items.isEmpty then effects else host.free owned { forget taken.memory with effects }
  retired : accepted = true → ∀ old, taken.memory.effects.keys key = some old → key.arguments ≠ [] →
    after.world.memory.heap old.address = none ∧ after.world.memory.memory.heap.lookup old.address = none
  memory : ∀ address cell, before.memory.memory.heap.lookup address = some cell →
    (accepted = true → ∀ old, taken.memory.effects.keys key = some old → key.arguments ≠ [] → address ≠ old.address) →
    after.world.memory.memory.heap.lookup address = some cell
  registry : ∀ address block, before.memory.heap address = some block →
    (accepted = true → ∀ old, taken.memory.effects.keys key = some old → key.arguments ≠ [] → address ≠ old.address) →
    after.world.memory.heap address = some block

/-- Publication consumes ownership only on success. On probe OOM the actual
outer defer releases the incoming allocation, preserves all original native
storage and key owners, and retains the reached probe/free effects. -/
theorem complete_taken (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ)
    (allocator : Nat) (source : View) (request : Interner.Request) (values : List NodeId)
    (key : Key) (owned : ArgumentSlice) (remaining : Handle) (id : NodeId)
    (before : World (Effects σ)) (taken : State (Effects σ)) (accepted : Bool) (effects : σ)
    (origin : Caller.Origin allocator source request values before taken owned remaining)
    (input : Input allocator source key owned taken.world)
    (keys : taken.world.memory.effects.keys = before.memory.effects.keys)
    (live : OwnedKeys.Live allocator ⟨before.memory.effects.keys, before.memory.heap⟩)
    (unique : OwnedKeys.Unique before.memory.effects.keys)
    (response : hostProbe key (forget taken.world.memory) = (accepted, effects)) :
    ∃ after,
      (let (result, reached) := (do let _ ← graph (fun slice => publish hostProbe host allocator source key slice id); handoff : Action (Effects σ) Unit) taken
       finish (external host) allocator result reached) =
        (if accepted then .ok () else .error (.language .outOfMemory), after) ∧
      Completion host allocator source request key owned id before taken.world accepted effects after := by
  have held := origin.held
  have oldLive : OwnedKeys.Live allocator ⟨taken.world.memory.effects.keys, taken.world.memory.heap⟩ := by
    intro query entry found
    rw [keys] at found
    rcases live query entry found with empty | stored
    · exact Or.inl empty
    · exact Or.inr (origin.registry _ _ stored)
  have oldUnique : OwnedKeys.Unique taken.world.memory.effects.keys := by rw [keys]; exact unique
  have fresh : OwnedKeys.Fresh taken.world.memory.effects.keys key ⟨owned.address, id⟩ := by
    intro query entry found _ nonempty
    rw [keys] at found
    exact origin.fresh _ _ ((live query entry found).resolve_left nonempty)
  cases accepted with
  | false =>
    let probed : Session (Effects σ) := { taken.world.memory with effects := ⟨taken.world.memory.effects.keys, effects⟩ }
    have published := publish_oom hostProbe host allocator source key owned id taken.world effects
      (admit_complete _ _ _ _ _ input) response
    have probedValid : Valid probed := ⟨held.1.1.memory, held.1.1.related, held.1.1.injected⟩
    obtain ⟨memory, freed, valid, released, freeEffects⟩ := free_valid (external host) allocator owned probed probedValid held.2.1
    dsimp only [probed] at freed
    let after : State (Effects σ) := ⟨{ taken.world with memory }, ⟨none, none, false⟩⟩
    have sameKeys : memory.effects.keys = taken.world.memory.effects.keys := by
      rw [freeEffects]
      split <;> rfl
    refine ⟨after, ?_, ⟨?_, rfl, rfl, sameKeys, ?_, ?_, released_consumed released,
      released.nextId, released.nextAddress, ?_, ?_, ?_, ?_⟩⟩
    · simp only [Effect.bind, graph, origin.scope, published, finish, ordinary,
        Fault.recoverable, ↓reduceIte, cleanup, Bool.false_eq_true, freed, deinit, deinitialize, origin.detached]
      rfl
    · exact ⟨valid, released_source source request.arguments held.1.2 released held.2.2⟩
    · intro query entry found
      rw [sameKeys, keys] at found
      rcases live query entry found with empty | stored
      · exact Or.inl empty
      · exact Or.inr ((released.frame entry.address (Ne.symm (origin.fresh _ _ stored))).1.trans (origin.registry _ _ stored))
    · change OwnedKeys.Unique memory.effects.keys
      rw [sameKeys]; exact oldUnique
    · change memory.effects.allocator = _
      rw [freeEffects]
      split <;> rfl
    · intro impossible; cases impossible
    · intro address cell found _
      exact (released.frame address (Ne.symm (origin.freshNative address cell found))).2.trans (origin.memory address cell found)
    · intro address block stored _
      exact (released.frame address (Ne.symm (origin.fresh address block stored))).1.trans (origin.registry address block stored)
  | true =>
    obtain ⟨published, executed, completed, incoming⟩ := publish_success hostProbe host allocator source key owned id taken.world effects
      held.1.1 input held.2.1 response
    let world := (commit key id taken.world (.ok (), published)).2
    let after : State (Effects σ) := ⟨world, ⟨none, some owned, true⟩⟩
    have table : published.table = OwnedKeys.store taken.world.memory.effects.keys key ⟨owned.address, id⟩ :=
      congrArg OwnedKeys.State.table completed.logical
    have allLive : OwnedKeys.Live allocator published.logical := by
      rw [completed.logical]
      exact OwnedKeys.after_live allocator _ key ⟨owned.address, id⟩ oldLive oldUnique
        (by simpa only [OwnedKeys.slice, input.aligned] using held.2.1) fresh
    refine ⟨after, ?_, ⟨(completion_held host allocator source request.arguments key owned id taken.world _ published input held completed).1,
      rfl, rfl, table, allLive, ?_, incoming, completed.nextId, completed.nextAddress, ?_, ?_, ?_, ?_⟩⟩
    · simp only [Effect.bind, graph, origin.scope, executed, commit, Except.mapError, handoff,
        finish, ordinary, ↓reduceIte, cleanup, deinit, deinitialize, origin.detached]
      rfl
    · change OwnedKeys.Unique published.table
      rw [table]; exact OwnedKeys.store_unique _ key ⟨owned.address, id⟩ oldUnique fresh
    · change published.memory.effects.allocator = _
      rw [completed.effects]
      dsimp only
      cases taken.world.memory.effects.keys key with
      | none => rfl
      | some old => dsimp only; split <;> rfl
    · intro _ old found nonempty
      exact ⟨completed.registry_dead _ _ _ _ _ old found nonempty, completed.dead old found nonempty⟩
    · intro address cell found apart
      exact (completed.frame address (apart rfl)).trans (origin.memory address cell found)
    · intro address block stored apart
      exact (completed.registry_frame _ _ _ _ _ address (apart rfl)).trans (origin.registry address block stored)

theorem Completion.closed (host : External σ) (allocator : Nat) (source : View)
    (request : Interner.Request) (key : Key) (owned : ArgumentSlice) (id : NodeId)
    (before taken : World (Effects σ)) (accepted : Bool) (effects : σ) (after : State (Effects σ))
    (completed : Completion host allocator source request key owned id before taken accepted effects after) :
    Closed after.scope := by
  rw [completed.scope]
  cases accepted <;> simp [Closed]

/-- Preserve the value projection of the physical owned-key table through
both handoff and OOM cleanup. Establishing it initially remains graph work. -/
theorem Completion.linked (host : External σ) (allocator : Nat) (source : View)
    (request : Interner.Request) (key : Key) (owned : ArgumentSlice) (id : NodeId)
    (before taken : World (Effects σ)) (accepted : Bool) (effects : σ) (after : State (Effects σ))
    (completed : Completion host allocator source request key owned id before taken accepted effects after)
    (linked : taken.graph.table = OwnedKeys.view taken.memory.effects.keys) :
    after.world.graph.table = OwnedKeys.view after.world.memory.effects.keys := by
  rw [completed.graph, completed.keys]
  cases accepted with
  | false => exact linked
  | true =>
    exact (congrArg (fun table => Cache.put equalityFields table key id) linked).trans
      (OwnedKeys.view_store taken.memory.effects.keys key ⟨owned.address, id⟩).symm

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication
