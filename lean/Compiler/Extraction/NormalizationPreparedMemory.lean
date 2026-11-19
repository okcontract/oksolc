/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationPreparedProofs
import Compiler.Extraction.InsertionSortCopied

namespace Compiler.Extraction.Cache.NormalizationOwnership
open Compiler.ZigAir.Memory.WordArray
open Compiler.Extraction.InsertionSort

/-- Allocator effects and destination selection remain explicit client inputs.
Preparation itself executes the typed copy and actual captured-swap caller. -/
def copiedPrimitives (budget : Nat) (source : View) (target : State → Compiler.ZigAir.Memory.State → View)
    (p : Primitives Compiler.ZigAir.Memory.State) : PreparedPrimitives Compiler.ZigAir.Memory.State Heap.Fault :=
  { toPrimitives := p, prepare := fun state before => Copied.run budget before source (target state before) }

theorem copied_ownership_safe (budget : Nat) (commutative : Bool) (bufferLength : Nat)
    (source : View) (target : State → Compiler.ZigAir.Memory.State → View) (p : Primitives Compiler.ZigAir.Memory.State)
    (exit : Exit) (before : Compiler.ZigAir.Memory.State) :
    PreparedSafe (normalizationOwnershipCode.runPrepared commutative source.length bufferLength
      (copiedPrimitives budget source target p) exit before).1 := run_prepared_safe _ _ _ _ _ _

/-- The ready selected view admits a finite uniform call budget. Later allocator
and cleanup effects run from the copied/sorted state, even when allocation
success depends on the counters changed by captured calls. Selection validity
is an explicit phase contract; this theorem does not verify the allocator. -/
theorem copied_run_settles (commutative : Bool) (bufferLength : Nat) (source : View)
    (target : State → Compiler.ZigAir.Memory.State → View) (p : Primitives Compiler.ZigAir.Memory.State) (exit : Exit)
    (before selected : Compiler.ZigAir.Memory.State) (state : State) (items : List Compiler.Algebraic.NodeId)
    (initialized : normalizationOwnershipCode.initWith commutative source.length bufferLength (p.allocate .temporary) before = (some state, selected))
    (needed : state.origin ≠ .input) (valid : selected.valid = true) (writable : Writable selected (target state selected))
    (represented : Represents selected source items) (lengths : source.length = (target state selected).length)
    (separate : Compiler.ZigAir.Memory.WordCopy.disjoint source (target state selected) = true) :
    ∃ result after, Captured.Settles (fun budget => normalizationOwnershipCode.runPrepared commutative source.length bufferLength
      (copiedPrimitives budget source target p) exit before) (result, after) ∧ PreparedSafe result := by
  obtain ⟨result, prepared, _, ⟨budget, settled⟩, _, _, _, _, effect⟩ :=
    Copied.run_refines selected source (target state selected) items valid writable represented lengths separate
  dsimp only at settled
  rcases effect with ⟨success, _⟩ | failed
  · subst result
    cases continued : normalizationOwnershipCode.continueWith p exit state prepared with
    | mk outcome after =>
      have run : ∀ fuel, budget ≤ fuel → normalizationOwnershipCode.runPrepared commutative source.length bufferLength
          (copiedPrimitives fuel source target p) exit before = (.ok outcome, after) := by
        intro fuel enough
        rw [prepared_success _ _ _ _ _ _ before selected prepared state initialized needed (settled fuel enough)]
        exact congrArg (fun value => (Except.ok value.1, value.2)) continued
      refine ⟨.ok outcome, after, ⟨budget, run⟩, ?_⟩
      have safe := copied_ownership_safe budget commutative bufferLength source target p exit before
      simpa only [run budget (Nat.le_refl budget)] using safe
  · subst result
    have run : ∀ fuel, budget ≤ fuel → normalizationOwnershipCode.runPrepared commutative source.length bufferLength
        (copiedPrimitives fuel source target p) exit before = (.error ((Heap.Fault.memory .outOfMemory), state), prepared) := by
      intro fuel enough
      exact prepared_fault _ _ _ _ _ _ before selected prepared state _ initialized needed (settled fuel enough)
    refine ⟨_, prepared, ⟨budget, run⟩, ?_⟩
    have safe := copied_ownership_safe budget commutative bufferLength source target p exit before
    simpa only [run budget (Nat.le_refl budget)] using safe

end Compiler.Extraction.Cache.NormalizationOwnership
