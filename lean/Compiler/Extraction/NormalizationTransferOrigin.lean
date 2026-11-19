/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationMemoryCaller

namespace Compiler.Extraction.Memory.Arguments.Normalization
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Actual normalization and take establish ownership independent of every
original registry allocation. Borrowed handles duplicate at the reached fresh
lifetime; owned handles transfer the temporary created by this initializer.
Neither successful field reads nor final separation are supplied as premises. -/
theorem initialized_take_origin (external : External σ) (budget allocator : Nat) (commutative : Bool)
    (source buffer : View) (values : List NodeId) (before prepared after : Session σ)
    (handle remaining : Handle) (slice : ArgumentSlice)
    (valid : Valid before) (represented : Represents before.memory source values)
    (scratch : commutative = true → 2 ≤ source.length → source.length ≤ buffer.length → Scratch source buffer before)
    (admitted : Admitted external)
    (initialized : init normalizationOwnershipCode external budget allocator commutative source buffer values before = (.ok handle, prepared))
    (taken : takeOwned normalizationOwnershipCode external allocator handle prepared = (.ok (slice, remaining), after)) :
    Taken allocator source values handle prepared slice remaining after ∧
    slice.items = normalized commutative source values ∧
    Frame before buffer after ∧
    (∀ id block, before.heap id = some block → slice.address ≠ id) ∧
    (∀ id cell, before.memory.heap.lookup id = some cell → id ≠ buffer.allocation → slice.address ≠ id) := by
  obtain ⟨result, reached, ran, post⟩ := init_refines external budget allocator commutative source buffer values before
    valid represented scratch admitted
  have same := Prod.mk.inj (ran.symm.trans initialized)
  rcases same with ⟨rfl, same⟩
  subst reached
  obtain ⟨ready, normalizedValues⟩ := post
  have initial := init_frame external budget allocator commutative source buffer values before prepared handle
    valid represented scratch admitted initialized
  obtain ⟨result, reached, ran, post⟩ := take_refines external allocator source values handle prepared ready admitted
  have same := Prod.mk.inj (ran.symm.trans taken)
  rcases same with ⟨rfl, same⟩
  subst reached
  refine ⟨post, post.values.trans normalizedValues, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro id cell found apart
    exact (post.frame id cell (initial.memory id cell found apart)).1
  · intro id block stored
    have retained := initial.registry id block stored
    obtain ⟨cell, found, _⟩ := ready.valid.injected id block retained
    exact (post.frame id cell found).2.trans retained
  · intro id block stored
    cases owned : handle.owned with
    | none =>
      have retained := initial.registry id block stored
      obtain ⟨cell, found, _⟩ := ready.valid.injected id block retained
      have older := (Compiler.ZigAir.Memory.valid_lookup prepared.memory id cell ready.valid.memory found).1
      rw [post.freshBorrow owned]
      omega
    | some original =>
      rw [(post.moved original owned).1]
      obtain ⟨cell, found, _⟩ := valid.injected id block stored
      have absent := initial.freshOwned original owned
      intro equal
      rw [equal, found] at absent
      contradiction
  · intro id cell found apart
    cases owned : handle.owned with
    | none =>
      have retained := initial.memory id cell found apart
      have older := (Compiler.ZigAir.Memory.valid_lookup prepared.memory id cell ready.valid.memory retained).1
      rw [post.freshBorrow owned]
      omega
    | some original =>
      rw [(post.moved original owned).1]
      have absent := initial.freshOwned original owned
      intro equal
      rw [equal, found] at absent
      contradiction

end Compiler.Extraction.Memory.Arguments.Normalization
