/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPublication

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray

structure Input (allocator : Nat) (source : View) (key : Key) (owned : ArgumentSlice)
    (before : World (Effects σ)) : Prop where
  aligned : key.arguments = owned.items
  live : ∀ old, before.memory.effects.keys key = some old →
    SliceValid allocator before.memory.heap (OwnedKeys.slice key old)
  incoming : ∀ old, before.memory.effects.keys key = some old → key.arguments ≠ [] → owned.address ≠ old.address
  source : ∀ old, before.memory.effects.keys key = some old → key.arguments ≠ [] →
    source.length ≠ 0 → source.allocation ≠ old.address

/-- Preserve publication admission when the reached key table and its argument
owners are retained. Private allocator effects and the graph may have changed. -/
theorem Input.frame (allocator : Nat) (source : View) (key : Key) (owned : ArgumentSlice)
    (before after : World (Effects σ)) (input : Input allocator source key owned before)
    (keys : after.memory.effects.keys = before.memory.effects.keys)
    (arguments : ∀ slice, SliceValid allocator before.memory.heap slice → SliceValid allocator after.memory.heap slice) :
    Input allocator source key owned after := by
  refine ⟨input.aligned, ?_, ?_, ?_⟩
  · intro old found
    rw [keys] at found
    exact arguments _ (input.live old found)
  · intro old found nonempty
    rw [keys] at found
    exact input.incoming old found nonempty
  · intro old found nonempty sourceNonempty
    rw [keys] at found
    exact input.source old found nonempty sourceNonempty

theorem admit_sound (allocator : Nat) (source : View) (key : Key) (owned : ArgumentSlice)
    (before : World (Effects σ)) (accepted : admit allocator source key owned before = .ok ()) :
    Input allocator source key owned before := by
  by_cases aligned : key.arguments = owned.items
  · cases found : before.memory.effects.keys key with
    | none =>
      exact ⟨aligned, fun _ impossible => by simp [found] at impossible,
        fun _ impossible => by simp [found] at impossible, fun _ impossible => by simp [found] at impossible⟩
    | some old =>
      by_cases empty : key.arguments = []
      · exact ⟨aligned, fun _ _ => Or.inl empty, fun _ _ nonempty => False.elim (nonempty empty),
          fun _ _ nonempty => False.elim (nonempty empty)⟩
      · by_cases incoming : old.address = owned.address
        · simp [admit, ← aligned, found, empty, incoming] at accepted
        · by_cases sourceAlias : source.length ≠ 0 ∧ old.address = source.allocation
          · simp [admit, ← aligned, found, empty, sourceAlias] at accepted
            split at accepted <;> contradiction
          · have live : SliceValid allocator before.memory.heap (OwnedKeys.slice key old) := by
              cases allocated : before.memory.heap old.address with
              | none => simp [admit, ← aligned, found, empty, incoming, sourceAlias, allocated] at accepted
              | some allocation =>
                rcases allocation with ⟨owner, block⟩
                cases block with
                | item | representatives | bytes => simp [admit, ← aligned, found, empty, incoming, sourceAlias, allocated] at accepted
                | arguments values =>
                  by_cases matching : owner = allocator ∧ values = key.arguments
                  · rcases matching with ⟨rfl, rfl⟩; exact Or.inr allocated
                  · simp [admit, ← aligned, found, empty, incoming, sourceAlias, allocated, matching] at accepted
            refine ⟨aligned, ?_, ?_, ?_⟩
            · intro entry present
              have same := Option.some.inj (present.symm.trans found)
              subst entry; exact live
            · intro entry present _
              have same := Option.some.inj (present.symm.trans found)
              subst entry; exact Ne.symm incoming
            · intro entry present _ nonempty
              have same := Option.some.inj (present.symm.trans found)
              subst entry
              exact fun equal => sourceAlias ⟨nonempty, equal.symm⟩
  · simp [admit, aligned] at accepted

/-- The checker admits every state satisfying its stated local input contract.
This is completeness for that contract, not a proof that all native callers
establish it or that the contract characterizes every safe native execution. -/
theorem admit_complete (allocator : Nat) (source : View) (key : Key) (owned : ArgumentSlice)
    (before : World (Effects σ)) (input : Input allocator source key owned before) :
    admit allocator source key owned before = .ok () := by
  cases found : before.memory.effects.keys key with
  | none => simp [admit, input.aligned, found]
  | some old =>
    by_cases empty : key.arguments = []
    · simp [admit, ← input.aligned, found, empty]
    · have stored := (input.live old found).resolve_left empty
      change before.memory.heap old.address = some ⟨allocator, .arguments key.arguments⟩ at stored
      have incoming := Ne.symm (input.incoming old found empty)
      have sourceApart : ¬(source.length ≠ 0 ∧ old.address = source.allocation) :=
        fun alias => input.source old found empty alias.1 alias.2.symm
      simp [admit, ← input.aligned, found, empty, incoming, sourceApart, stored]

theorem external_admitted (host : External σ) (admitted : Admitted host) : Admitted (external host) := by
  intro site state values base reached valid nonempty called
  exact admitted site (forget state) values base reached.allocator valid nonempty
    (by simpa [external, forget, Prod.ext_iff] using congrArg (fun result => (result.1, result.2.allocator)) called)

/-- Failed probing precedes key release and publication. Retain its actual
allocator effects while framing both heaps and the existing key table. -/
theorem publish_oom (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ) (allocator : Nat)
    (source : View) (key : Key) (owned : ArgumentSlice) (id : NodeId) (before : World (Effects σ)) (effects : σ)
    (accepted : admit allocator source key owned before = .ok ())
    (response : hostProbe key (forget before.memory) = (false, effects)) :
    publish hostProbe host allocator source key owned id before =
      (.error (.language .outOfMemory),
        { before with memory := { before.memory with effects := { before.memory.effects with allocator := effects } } }) := by
  simp only [publish, accepted, body, OwnedKeys.Physical.run, OwnedKeys.Code.execute,
    OwnedKeys.Physical.operations, probe, physical, response, Bool.false_eq_true, ↓reduceIte,
    commit, Except.mapError, memoryFault]

theorem completion_held (host : External σ) (allocator : Nat) (source : View) (values : List NodeId)
    (key : Key) (owned : ArgumentSlice) (id : NodeId) (before : World (Effects σ)) (effects : Effects σ)
    (after : OwnedKeys.Physical.State (Effects σ))
    (input : Input allocator source key owned before) (held : Held allocator source values owned before)
    (completed : OwnedKeys.Physical.Completed (external host) key ⟨owned.address, id⟩
      ⟨before.memory.effects.keys, { before.memory with effects }⟩ after) :
    Held allocator source values owned (commit key id before (.ok (), after)).2 := by
  refine ⟨⟨⟨completed.valid.memory, completed.valid.related, completed.valid.injected⟩, ?_⟩, ?_, held.2.2⟩
  · by_cases empty : source.length = 0
    · refine ⟨held.1.2.1, ?_⟩
      intro index inside
      have length := held.1.2.1
      omega
    · exact represented_frame source values held.1.2 (completed.frame source.allocation
        (fun old found nonempty => input.source old found nonempty empty))
  · have heap := congrArg OwnedKeys.State.memory completed.logical
    change after.memory.heap = _ at heap
    change SliceValid allocator after.memory.heap owned
    rw [heap]
    exact OwnedKeys.retire_slice allocator _ key owned held.2.1
      (fun old found nonempty _ => input.incoming old found nonempty)

/-- The publication memory postcondition is derived from executable admission
and the source-bound body, rather than assumed as a graph callback contract. -/
theorem publish_held (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ) (allocator : Nat)
    (source : View) (values : List NodeId) (key : Key) (owned : ArgumentSlice) (id : NodeId)
    (before : World (Effects σ)) (held : Held allocator source values owned before)
    (ordinaryResult : ordinary (publish hostProbe host allocator source key owned id before).1 = true) :
    Held allocator source values owned (publish hostProbe host allocator source key owned id before).2 := by
  have accepted := ordinary_admitted hostProbe host allocator source key owned id before ordinaryResult
  have input := admit_sound allocator source key owned before accepted
  rw [accepted_body hostProbe host allocator source key owned id before accepted]
  have checked := OwnedKeys.Physical.run_local_spec (probe hostProbe) (external host) allocator key
    ⟨owned.address, id⟩ (physical before) held.1.1 input.live
  cases called : probe hostProbe key before.memory with
  | mk ok effects =>
    cases ok with
    | false =>
      simp only [physical, called, Bool.false_eq_true, ↓reduceIte] at checked
      simp only [body, physical, checked, commit, Except.mapError, memoryFault]
      exact ⟨⟨⟨held.1.1.memory, held.1.1.related, held.1.1.injected⟩, held.1.2⟩, held.2⟩
    | true =>
      simp only [physical, called, ↓reduceIte] at checked
      obtain ⟨after, ran, completed⟩ := checked
      simp only [body, physical, ran]
      exact completion_held host allocator source values key owned id before effects after input held completed

theorem publish_semantics (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ) (allocator : Nat)
    (source : View) (key : Key) (owned : ArgumentSlice) (id : NodeId) (before : World (Effects σ))
    (meaning : Meaning) (value : Word) (valid : Interner.Invariant meaning before.graph)
    (evaluated : key.eval meaning before.graph.read = some value) (actual : before.graph.read id = some value) :
    let executed := publish hostProbe host allocator source key owned id before
    Semantic.Ensures meaning before.graph executed.1 executed.2.graph (fun _ _ => True) := by
  cases accepted : admit allocator source key owned before with
  | error reason =>
    simp only [publish, accepted]
    exact Semantic.Ensures.error meaning before.graph _ _ valid
  | ok returned =>
    cases returned
    simp only [publish, accepted, body]
    cases ran : OwnedKeys.Physical.run (probe hostProbe) (external host) allocator key ⟨owned.address, id⟩ (physical before) with
    | mk result after =>
      cases result with
      | error fault => exact Semantic.Ensures.error meaning before.graph (memoryFault fault) _ valid
      | ok returned =>
        cases returned
        intro _
        exact ⟨⟨Cache.put_valid meaning before.graph.read before.graph.table valid.cache key id value evaluated actual,
          valid.representation⟩, fun _ _ found => found, trivial⟩

/-- The existing logical cache is exactly the value projection after a
successful publication, provided it was the projection before. -/
theorem completed_projection (key : Key) (owned : ArgumentSlice) (id : NodeId)
    (before : World (Effects σ)) (host : External σ) (effects : Effects σ)
    (after : OwnedKeys.Physical.State (Effects σ))
    (linked : before.graph.table = OwnedKeys.view before.memory.effects.keys)
    (completed : OwnedKeys.Physical.Completed (external host) key ⟨owned.address, id⟩
      ⟨before.memory.effects.keys, { before.memory with effects }⟩ after) :
    let world := (commit key id before (.ok (), after)).2
    world.graph.table = OwnedKeys.view world.memory.effects.keys := by
  have table := congrArg OwnedKeys.State.table completed.logical
  change after.table = OwnedKeys.store before.memory.effects.keys key ⟨owned.address, id⟩ at table
  change Cache.put equalityFields before.graph.table key id = OwnedKeys.view after.table
  rw [table, OwnedKeys.view_store, linked]

/-- Publication preserves the physical-table/semantic-cache connection on
ordinary success and OOM. Establishing this connection for every native graph
operation remains separate from the publication proof. -/
theorem publish_linked (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ) (allocator : Nat)
    (source : View) (key : Key) (owned : ArgumentSlice) (id : NodeId) (before : World (Effects σ))
    (valid : Valid before.memory) (linked : before.graph.table = OwnedKeys.view before.memory.effects.keys)
    (ordinaryResult : ordinary (publish hostProbe host allocator source key owned id before).1 = true) :
    let after := (publish hostProbe host allocator source key owned id before).2
    after.graph.table = OwnedKeys.view after.memory.effects.keys := by
  have accepted := ordinary_admitted hostProbe host allocator source key owned id before ordinaryResult
  have input := admit_sound allocator source key owned before accepted
  rw [accepted_body hostProbe host allocator source key owned id before accepted]
  have checked := OwnedKeys.Physical.run_local_spec (probe hostProbe) (external host) allocator key
    ⟨owned.address, id⟩ (physical before) valid input.live
  cases called : probe hostProbe key before.memory with
  | mk ok effects =>
    cases ok with
    | false =>
      simp only [physical, called, Bool.false_eq_true, ↓reduceIte] at checked
      simp only [body, physical, checked, commit]
      exact linked
    | true =>
      simp only [physical, called, ↓reduceIte] at checked
      obtain ⟨after, ran, completed⟩ := checked
      simp only [body, physical, ran]
      exact completed_projection key owned id before host effects after linked completed

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication
