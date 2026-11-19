/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationPreparedProofs
import Compiler.Extraction.NormalizationEffectTests

namespace Compiler.Extraction.Cache.NormalizationOwnership.PreparedTests

inductive Event where
  | allocate (site : Allocation)
  | prepare (origin : Origin)
  | release (owner : Owner) (owned dead : Bool)
  deriving DecidableEq, Repr
structure Trace where
  counter : Nat := 0
  events : List Event := []
  deriving DecidableEq, Repr
inductive Stop where | invalid | incomplete deriving DecidableEq, Repr

/-- Controlled external effects, not an implementation of a native allocator. -/
def primitives (limit : Nat) (stop : Option Stop := none) : PreparedPrimitives Trace Stop where
  allocate := fun site before => (before.counter < limit,
    ⟨before.counter + 1, before.events ++ [.allocate site]⟩)
  release := fun state before => ⟨before.counter + 10, before.events ++ [.release state.owner state.owned state.dead]⟩
  prepare := fun state before =>
    (match stop with | none => .ok () | some reason => .error reason,
      ⟨before.counter + 5, before.events ++ [.prepare state.origin]⟩)

def run (commutative : Bool) (length bufferLength limit : Nat) (exit : Exit) (stop : Option Stop := none) :=
  normalizationOwnershipCode.runPrepared commutative length bufferLength (primitives limit stop) exit ({} : Trace)

theorem safe (commutative : Bool) (length bufferLength limit : Nat) (exit : Exit) (stop : Option Stop) :
    PreparedSafe (run commutative length bufferLength limit exit stop).1 := run_prepared_safe _ _ _ _ _ _

def live : State := { origin := .allocation, owner := .lookup, owned := true }
theorem allocated_transfer : run true 3 2 99 .transfer =
    (.ok (.transferred, { origin := .allocation, owner := .caller, dead := true }),
      ⟨6, [.allocate .temporary, .prepare .allocation]⟩) := rfl
theorem allocated_lookup : run true 3 2 99 .lookup =
    (.ok (.lookup, { live with owner := .released, dead := true }),
      ⟨16, [.allocate .temporary, .prepare .allocation, .release .lookup true false]⟩) := rfl
theorem allocated_cleanup : run true 3 2 99 .cleanup =
    (.ok (.cleaned, { origin := .allocation, owner := .released, dead := true }),
      ⟨16, [.allocate .temporary, .prepare .allocation, .release .caller false false]⟩) := rfl
theorem scratch_duplicates_after_prepare : run true 3 3 99 .cleanup =
    (.ok (.cleaned, { origin := .scratch, owner := .released, dead := true }),
      ⟨16, [.prepare .scratch, .allocate .duplicate, .release .caller false false]⟩) := rfl
theorem post_prepare_allocation_failure : run true 3 3 2 .transfer =
    (.ok (.allocationFailure, { origin := .scratch, dead := true }),
      ⟨6, [.prepare .scratch, .allocate .duplicate]⟩) := rfl

theorem initial_projection_is_not_post_prepare_decision :
    (normalizationOwnershipCode.runWith true 3 3 (primitives 2).toPrimitives .transfer ({} : Trace)).1.1 = .transferred ∧
    (run true 3 3 2 .transfer).1 = .ok (.allocationFailure, { origin := .scratch, dead := true }) := ⟨rfl, rfl⟩
theorem failed_initializer_skips_prepare : run true 3 2 0 .cleanup =
    (.ok (.allocationFailure, { dead := true }), ⟨1, [.allocate .temporary]⟩) := rfl
theorem allocated_fault_keeps_live_token : run true 3 2 99 .cleanup (some .invalid) =
    (.error (.invalid, live), ⟨6, [.allocate .temporary, .prepare .allocation]⟩) := rfl
theorem fault_is_not_closed : Ready live ∧ ¬Safe (.lookup, live) := by
  constructor
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · simp [Safe, live]
theorem scratch_suspension_skips_transfer : run true 3 3 99 .transfer (some .incomplete) =
    (.error (.incomplete, { origin := .scratch }), ⟨5, [.prepare .scratch]⟩) := rfl
theorem borrowed_skips_faulting_prepare : run false 3 2 99 .transfer (some .invalid) =
    (.ok (.transferred, { owner := .caller, dead := true }), ⟨1, [.allocate .duplicate]⟩) := rfl
theorem singleton_skips_faulting_prepare : run true 1 0 99 .lookup (some .invalid) =
    (.ok (.lookup, { dead := true }), {}) := rfl
theorem empty_skips_faulting_prepare : run true 0 0 99 .lookup (some .invalid) =
    (.ok (.lookup, { dead := true }), {}) := rfl

end Compiler.Extraction.Cache.NormalizationOwnership.PreparedTests
