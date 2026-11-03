/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionGrowingSuccessTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.CustodyTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Ownership comes from the initialized graph and the actual take, before the
caller has passed its normalized argument allocation to any child. -/
theorem normalized_custody (safety empty : Bool) :
    Caller.Custody 7 (normalized safety empty 4) (taken safety empty 4).2.world.memory :=
  ((initialized_prefix safety empty 4 (by decide)).caller_input (by decide)).custody

theorem normalized_words (safety empty : Bool) :
    Good (view (normalized safety empty 4)) (CallerInputTests.values empty) (taken safety empty 4).2.world := by
  have entry := (initialized_prefix safety empty 4 (by decide)).caller_input (by decide)
  exact (normalized_custody safety empty).good entry.origin.held.1.1 _

/-- Successful publication transfers a nonempty normalized buffer to the map;
it cannot still satisfy the private-buffer precondition for a later child. -/
theorem published_not_private (safety : Bool) :
    ¬Caller.Custody 7 (normalized safety false 4) (before safety false 5).memory := by
  intro custody
  have completed := growing_contract safety false
  have table := completed.2.2.2.2.2.2.2.2.2.1
  have found : (before safety false 5).memory.effects.keys (CallerInputTests.key false) =
      some ⟨(normalized safety false 4).address, 5⟩ := by
    rw [table, OwnedKeys.store]; simp only [↓reduceIte]
  exact custody.apart _ _ found (by decide) ⟨by change [0] ≠ []; decide, rfl⟩

/-- Empty slices carry no owned allocation, including when their sentinel
address is the same as a published key's address. -/
theorem empty_custody (address : Nat) (memory : Session (Publication.Effects σ)) :
    Caller.Custody 7 ⟨address, []⟩ memory := by
  exact ⟨Or.inl rfl, fun _ _ _ _ impossible => impossible.1 rfl⟩

/-- The first representative supplies a non-vacuous protected argument buffer;
its owner and key separation follow from the actual initialized prefix. -/
theorem parent_custody (safety empty : Bool) :
    Caller.Custody 7 (CallerInputTests.operands empty) (before safety empty 4).memory := by
  have prior := initialized_prefix safety empty 4 (by decide)
  have member : CallerFirstSuccessTests.row safety empty ∈ cells safety empty 4 :=
    List.mem_of_mem_head? (by rw [prior.first]; rfl)
  refine ⟨(prior.facts.resident _ member).2, ?_⟩
  intro query old found nonempty alias
  exact prior.facts.apart query old found nonempty ⟨_, member, alias⟩

theorem parent_after_growth (safety empty : Bool) :
    Caller.Custody 7 (CallerInputTests.operands empty) (before safety empty 5).memory ∧
      Good (parent empty) (CallerInputTests.values empty) (before safety empty 5) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, kept⟩ := growing_contract safety empty
  exact kept _ (parent_custody safety empty)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.CustodyTests
