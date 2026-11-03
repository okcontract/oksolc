/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerOrigin
import Compiler.Extraction.PublicationNormalizationEffects
import Compiler.Extraction.InternerPublicationProofs

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

theorem caller_init_keys (host : External σ) (budget allocator : Nat) (source buffer : View)
    (request : Interner.Request) (before : State (Effects σ)) :
    (Caller.initLookup (external host) budget allocator source buffer request before).2.world.memory.effects.keys =
      before.world.memory.effects.keys := by
  unfold Caller.initLookup
  cases Interner.Scoped.commutative request.item with
  | error fault => rfl
  | ok commutative =>
    dsimp only
    have same := init_keys host budget allocator commutative source buffer request.arguments before.world.memory
    cases ran : init normalizationOwnershipCode (external host) budget allocator commutative source buffer request.arguments before.world.memory with
    | mk result memory =>
      rw [ran] at same
      cases result <;> exact same

theorem caller_take_keys (host : External σ) (allocator : Nat) (before : State (Effects σ)) :
    (take (external host) allocator before).2.world.memory.effects.keys = before.world.memory.effects.keys := by
  unfold take
  cases before.scope.lookup with
  | none => rfl
  | some handle =>
    dsimp only
    have same := take_keys host allocator handle before.world.memory
    cases ran : takeOwned normalizationOwnershipCode (external host) allocator handle before.world.memory with
    | mk result memory =>
      rw [ran] at same
      cases result with
      | error fault => exact same
      | ok pair => rcases pair with ⟨slice, remaining⟩; exact same

/-- The caller establishes publication's incoming ownership from allocation
and normalization, before recursive simplification. Only the selected old key's
initial liveness and source separation remain graph invariants. In particular,
neither an already admitted publication nor normalized-slice liveness,
freshness, descriptor equality or a final key-table frame is assumed. -/
theorem caller_input (host : External σ) (budget allocator : Nat) (source : View)
    (request : Interner.Request) (before : World (Effects σ)) (memory : Compiler.ZigAir.Memory.State)
    (pointer : Compiler.ZigAir.Memory.Value) (values : List NodeId) (prepared after : State (Effects σ)) (key : Key)
    (good : Good source request.arguments before) (admitted : Admitted host)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (initialized : Caller.initLookup (external host) budget allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (taken : take (external host) allocator prepared = (.ok (), after))
    (made : Interner.makeKey request values = .ok key)
    (live : ∀ old, before.memory.effects.keys key = some old → SliceValid allocator before.memory.heap (OwnedKeys.slice key old))
    (sourceApart : ∀ old, before.memory.effects.keys key = some old → key.arguments ≠ [] →
      source.length ≠ 0 → source.allocation ≠ old.address) :
    ∃ slice remaining, Caller.Origin allocator source request values before after slice remaining ∧
      after.world.memory.effects.keys = before.memory.effects.keys ∧
      Input allocator source key slice after.world := by
  obtain ⟨slice, remaining, origin⟩ := Caller.take_origin (external host) budget allocator source request before memory pointer values prepared after
    good (external_admitted host admitted) allocated initialized taken
  have initKeys := caller_init_keys host budget allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request
    ⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩
  have takeKeys := caller_take_keys host allocator prepared
  rw [initialized] at initKeys
  rw [taken] at takeKeys
  have keys := takeKeys.trans initKeys
  refine ⟨slice, remaining, origin, keys, (key_arguments request values key made).trans origin.aligned.symm, ?_, ?_, ?_⟩
  · intro old found
    rw [keys] at found
    rcases live old found with empty | stored
    · exact Or.inl empty
    · exact Or.inr (origin.registry _ _ stored)
  · intro old found nonempty
    rw [keys] at found
    exact origin.fresh _ _ ((live old found).resolve_left nonempty)
  · intro old found nonempty sourceNonempty
    rw [keys] at found
    exact sourceApart old found nonempty sourceNonempty

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication
