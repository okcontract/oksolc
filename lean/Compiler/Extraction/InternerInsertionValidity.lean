/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionExecution

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open AssemblyClone (Value)

theorem ownsArguments_sound (allocator : Nat) (slice : ArgumentSlice) (heap : Memory.Heap)
    (accepted : ownsArguments allocator slice heap = true) : SliceValid allocator heap slice := by
  by_cases empty : slice.items = []
  · exact Or.inl empty
  · unfold ownsArguments at accepted
    simp only [List.isEmpty_eq_false_iff.mpr empty, Bool.false_eq_true, ↓reduceIte] at accepted
    split at accepted
    · rename_i owner values stored
      have matching := of_decide_eq_true accepted
      rcases matching with ⟨rfl, same⟩
      exact Or.inr (same ▸ stored)
    · contradiction

theorem borrowed_ready (allocator : Nat) (slice : ArgumentSlice) (before : Session σ)
    (valid : Valid before) (live : SliceValid allocator before.heap slice) :
    Ready allocator (view slice) slice.items ⟨view slice, slice.items, none⟩ before := by
  have represented : Represents before.memory (view slice) slice.items := by
    by_cases empty : slice.items = []
    · exact ⟨by simp [view, empty], fun _ impossible => False.elim (by simp [empty] at impossible)⟩
    · exact (valid.related allocator slice.address slice.items empty (live.resolve_left empty)).2
  exact ⟨valid, represented, represented, (fun _ impossible => by cases impossible),
    (fun _ _ impossible => by cases impossible)⟩

theorem duplicate_valid (ops : Operations σ) (allocator : Nat) (slice : ArgumentSlice)
    (before : Session (Publication.Effects σ)) (valid : Valid before)
    (live : SliceValid allocator before.heap slice) (admitted : Admitted ops.arguments) :
    Valid (takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view slice, slice.items, none⟩ before).2 := by
  obtain ⟨result, after, ran, post⟩ := take_refines (Publication.external ops.arguments) allocator
    (view slice) slice.items ⟨view slice, slice.items, none⟩ before (borrowed_ready allocator slice before valid live)
    (Publication.external_admitted ops.arguments admitted)
  rw [ran]
  cases result with
  | ok pair => exact post.ready.valid
  | error fault =>
    cases fault <;> simp only at post
    all_goals first | exact post.2.2.2.valid | contradiction

theorem publication_valid (ops : Operations σ) (allocator : Nat) (source : View) (key : Key)
    (slice : ArgumentSlice) (id : NodeId) (before : World (Publication.Effects σ)) (valid : Valid before.memory) :
    Valid (Publication.publish ops.probe ops.arguments allocator source key slice id before).2.memory := by
  cases accepted : Publication.admit allocator source key slice before with
  | error reason => simpa only [Publication.publish, accepted] using valid
  | ok returned =>
    cases returned
    have input := Publication.admit_sound allocator source key slice before accepted
    rw [Publication.accepted_body ops.probe ops.arguments allocator source key slice id before accepted]
    have checked := OwnedKeys.Physical.run_local_spec (Publication.probe ops.probe) (Publication.external ops.arguments)
      allocator key ⟨slice.address, id⟩ (Publication.physical before) valid input.live
    cases called : Publication.probe ops.probe key before.memory with
    | mk ok effects =>
      cases ok with
      | false =>
        simp only [Publication.physical, called, Bool.false_eq_true, ↓reduceIte] at checked
        simp only [Publication.body, Publication.physical, checked, Publication.commit, Except.mapError, memoryFault]
        exact ⟨valid.memory, valid.related, valid.injected⟩
      | true =>
        simp only [Publication.physical, called, ↓reduceIte] at checked
        obtain ⟨after, ran, completed⟩ := checked
        simp only [Publication.body, Publication.physical, ran, Publication.commit]
        exact ⟨completed.valid.memory, completed.valid.related, completed.valid.injected⟩

def StateValid (state : State Metadata σ) : Prop := Valid (memory state)

theorem item_preserves (ops : Operations σ) (allocator : Nat) (input : Value Metadata)
    (normalized : ArgumentSlice) (owner : Storage.State) (before : State Metadata σ) :
    Storage.Preserves (itemOperations ops allocator input normalized owner before) Normalization.Insertion.CreationValid := by
  apply Normalization.Insertion.creation_preserves
  constructor
  · intro _ _ _ _ _ _ impossible; cases impossible
  · intro _ _ _ _ _ impossible; cases impossible

theorem callbacks_preserve (ops : Operations σ) (allocator count : Nat) (source : View) (input : Value Metadata)
    (key : Key) (normalized : ArgumentSlice) (graph : Storage.State → State Metadata σ → Interner.Heap)
    (admitted : Admitted ops.arguments) :
    Storage.Preserves (callbacks ops allocator count source input key normalized graph) StateValid := by
  have liftedAttempt : ∀ site owner before result after, StateValid before →
      (let ran := (itemOperations ops allocator input normalized owner before).attempt site owner before.item
       (ran.1.mapError Rejection.creation, { before with item := ran.2 })) = (.ok result, after) → StateValid after := by
    intro site owner before result after initial called
    cases ran : (itemOperations ops allocator input normalized owner before).attempt site owner before.item with
    | mk response reached =>
      cases response with
      | error fault => simp [ran, Except.mapError] at called
      | ok accepted =>
        have post := (item_preserves ops allocator input normalized owner before).attempt site owner before.item accepted reached initial ran
        simp only [ran, Except.mapError, Prod.mk.injEq, Except.ok.injEq] at called
        exact called.2 ▸ post
  have liftedRelease : ∀ action owner before after, StateValid before →
      (let ran := (itemOperations ops allocator input normalized owner before).release action owner before.item
       (ran.1.mapError Rejection.creation, { before with item := ran.2 })) = (.ok (), after) → StateValid after := by
    intro action owner before after initial called
    cases ran : (itemOperations ops allocator input normalized owner before).release action owner before.item with
    | mk response reached =>
      cases response with
      | error fault => simp [ran, Except.mapError] at called
      | ok returned =>
        cases returned
        have post := (item_preserves ops allocator input normalized owner before).release action owner before.item reached initial ran
        simp only [ran, Except.mapError, Prod.mk.injEq] at called
        exact called.2 ▸ post
  constructor
  · intro site owner before result after initial called
    cases site with
    | arguments =>
      dsimp only [callbacks] at called
      split at called
      · simp at called
      · rename_i accepted
        have live := ownsArguments_sound allocator normalized (memory before).heap (by simpa using accepted)
        have post := duplicate_valid ops allocator normalized (memory before) initial live admitted
        cases ran : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
            ⟨view normalized, normalized.items, none⟩ (memory before) with
        | mk response reached =>
          rw [ran] at post
          cases response with
          | ok pair =>
            simp only [ran, Prod.mk.injEq, Except.ok.injEq] at called
            exact called.2 ▸ post
          | error fault =>
            cases fault <;> simp only [ran, Prod.mk.injEq, Except.ok.injEq, reduceCtorEq] at called
            all_goals first | exact called.2 ▸ post | contradiction
    | item => exact liftedAttempt .item owner before result after initial called
    | clone => exact liftedAttempt .clone owner before result after initial called
    | append =>
      dsimp only [callbacks] at called
      split at called
      · simp at called
      · have same := congrArg Prod.snd called
        dsimp only at same
        rw [← same]
        exact ⟨initial.memory, initial.related, initial.injected⟩
    | publish =>
      dsimp only [callbacks] at called
      have post := publication_valid ops allocator source key normalized (BitVec.ofNat 32 count) ⟨graph owner before, memory before⟩ initial
      cases ran : Publication.publish ops.probe ops.arguments allocator source key normalized (BitVec.ofNat 32 count)
          ⟨graph owner before, memory before⟩ with
      | mk response reached =>
        rw [ran] at post
        cases response with
        | ok returned => cases returned; simp only [ran, Prod.mk.injEq, Except.ok.injEq] at called; exact called.2 ▸ post
        | error fault =>
          cases fault <;> try { simp [ran] at called }
          rename_i error
          cases error <;> simp only [ran, Prod.mk.injEq, Except.ok.injEq, reduceCtorEq] at called
          all_goals first | exact called.2 ▸ post | contradiction
  · intro action owner before after initial called
    cases action with
    | normalized =>
      have post := Normalization.Insertion.arguments_release_valid (Publication.external ops.arguments) allocator normalized (memory before) initial
      have same := congrArg Prod.snd called
      dsimp only [callbacks] at same
      rw [← same]; exact post
    | arguments =>
      dsimp only [callbacks] at called
      cases present : arguments normalized owner before with
      | none => simp [present] at called
      | some slice =>
        simp only [present] at called
        have post := Normalization.Insertion.arguments_release_valid (Publication.external ops.arguments) allocator slice (memory before) initial
        have same := congrArg Prod.snd called
        dsimp only at same
        rw [← same]; exact post
    | allocation => exact liftedRelease .allocation owner before after initial called
    | value => exact liftedRelease .value owner before after initial called
    | lastValue =>
      dsimp only [callbacks] at called
      cases present : arguments normalized owner before with
      | none => simp [present] at called
      | some slice =>
        simp only [present] at called
        exact liftedRelease .lastValue owner before after initial called
    | pop =>
      have same := congrArg Prod.snd called
      change before = after at same
      exact same ▸ initial

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion
