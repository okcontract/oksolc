/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationMemoryProofs

namespace Compiler.Extraction.Memory.Arguments.Normalization
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.InsertionSort
open Compiler.ZigAir.Memory.WordArray
open Compiler.Extraction.Cache

theorem prepare_settles (allocator bufferLength : Nat) (source target : View) (values : List NodeId)
    (allocated : Bool) (before : Session σ) (selected : Destination allocator source target values allocated before) :
    ∃ result after, Captured.Settles (fun budget => prepare normalizationOwnershipCode budget allocator bufferLength source target values allocated before)
      (result, after) ∧ result ≠ .error (.preparation .incomplete) := by
  obtain ⟨result, memory, _, ⟨budget, settled⟩, _, _, _, _, terminal⟩ := Copied.run_refines before.memory source target values
    selected.valid selected.writable selected.represented selected.lengths selected.disjoint
  let observed := prepare normalizationOwnershipCode budget allocator bufferLength source target values allocated before
  refine ⟨observed.1, observed.2, ⟨budget, ?_⟩, ?_⟩
  · intro fuel enough
    have first := settled budget (Nat.le_refl budget)
    have later := settled fuel enough
    simp only [observed, prepare, first, later]
  · dsimp only [observed]
    rw [show (prepare normalizationOwnershipCode budget allocator bufferLength source target values allocated before).1 =
      (match result with
       | .error reason => Except.error (Failure.preparation reason)
       | .ok () => .ok ⟨target, sortIds values,
           if normalizationOwnershipCode.ownTemporary.test source.length bufferLength then some ⟨target.allocation, sortIds values⟩ else none⟩) by
      simp only [prepare, settled budget (Nat.le_refl budget)]; cases result <;> rfl]
    rcases terminal with ⟨rfl, _⟩ | rfl <;> intro impossible <;> cases impossible

theorem init_settles (external : External σ) (allocator : Nat) (commutative : Bool) (source buffer : View)
    (values : List NodeId) (before : Session σ) (valid : Valid before) (represented : Represents before.memory source values)
    (scratch : commutative = true → 2 ≤ source.length → source.length ≤ buffer.length → Scratch source buffer before)
    (admitted : Admitted external) :
    ∃ result after, Captured.Settles (fun budget => init normalizationOwnershipCode external budget allocator commutative source buffer values before)
      (result, after) ∧ result ≠ .error (.preparation .incomplete) := by
  cases needed : !commutative || decide (source.length < normalizationOwnershipCode.threshold) with
  | true =>
    refine ⟨.ok ⟨source, values, none⟩, before, ⟨0, ?_⟩, by intro impossible; cases impossible⟩
    intro fuel _
    simp only [init, needed, ↓reduceIte]
  | false =>
    have conditions : commutative = true ∧ 2 ≤ source.length := by
      simpa [normalizationOwnershipCode, Bool.or_eq_false_iff, Bool.not_eq_false', Nat.not_lt] using needed
    by_cases fits : source.length ≤ buffer.length
    · have choice : normalizationOwnershipCode.useScratch.test source.length buffer.length = true := by
        simp [normalizationOwnershipCode, NormalizationOwnership.Comparison.test, fits]
      obtain ⟨result, after, ⟨budget, settled⟩, terminal⟩ := prepare_settles allocator buffer.length source
        (bufferPrefix buffer source.length) values false before
        (scratch_destination allocator source buffer values before valid represented (scratch conditions.1 conditions.2 fits) fits)
      refine ⟨result, after, ⟨budget, ?_⟩, terminal⟩
      intro fuel enough
      simpa only [init, needed, Bool.false_eq_true, ↓reduceIte, choice] using settled fuel enough
    · have choice : normalizationOwnershipCode.useScratch.test source.length buffer.length = false := by
        simp [normalizationOwnershipCode, NormalizationOwnership.Comparison.test, fits]
      have nonempty : values ≠ [] := by intro empty; rw [empty] at represented; have length := represented.1; simp at length; omega
      obtain ⟨reserved, allocated, reservedRun, selected⟩ := reserve_refines external allocator source values before valid represented nonempty admitted
      cases reserved with
      | error fault =>
        cases fault with
        | allocation | preparation | release => contradiction
        | outOfMemory =>
          refine ⟨.error .outOfMemory, allocated, ⟨0, ?_⟩, by intro impossible; cases impossible⟩
          intro fuel _
          simp only [init, needed, Bool.false_eq_true, ↓reduceIte, choice, reservedRun]
      | ok slice =>
        obtain ⟨result, after, ⟨budget, settled⟩, terminal⟩ := prepare_settles allocator buffer.length source (view slice) values true allocated selected
        refine ⟨result, after, ⟨budget, ?_⟩, terminal⟩
        intro fuel enough
        simpa only [init, needed, Bool.false_eq_true, ↓reduceIte, choice, reservedRun] using settled fuel enough

/-- The composed theorem is not satisfied solely by perpetually incomplete
observations. One finite uniform budget settles the whole lifecycle, including
all later state-dependent allocator/free callbacks, with its proved Post.
Captured stack-memory exhaustion remains an explicit semantic resource fault. -/
theorem run_settles (external : External σ) (allocator : Nat) (commutative : Bool) (source buffer : View)
    (values : List NodeId) (exit : NormalizationOwnership.Exit) (before : Session σ)
    (valid : Valid before) (represented : Represents before.memory source values)
    (scratch : commutative = true → 2 ≤ source.length → source.length ≤ buffer.length → Scratch source buffer before)
    (admitted : Admitted external) :
    ∃ result after budget, (∀ fuel, budget ≤ fuel →
      run normalizationOwnershipCode external fuel allocator commutative source buffer values exit before = (result, after) ∧
      Post external fuel allocator commutative source buffer values exit before result after) ∧
      result ≠ .error (.preparation .incomplete) := by
  obtain ⟨initialized, prepared, ⟨budget, settled⟩, terminal⟩ := init_settles external allocator commutative source buffer values before
    valid represented scratch admitted
  cases initialized with
  | error fault =>
    refine ⟨.error fault, prepared, budget, ?_, ?_⟩
    · intro fuel enough
      have executed : run normalizationOwnershipCode external fuel allocator commutative source buffer values exit before = (.error fault, prepared) := by
        simp only [run, settled fuel enough]
      exact ⟨executed, run_result external fuel allocator commutative source buffer values exit before prepared _ valid represented scratch admitted executed⟩
    · intro impossible
      have same := Except.error.inj impossible
      subst fault
      exact terminal rfl
  | ok handle =>
    obtain ⟨expected, initialAfter, checked, ready⟩ := init_refines external budget allocator commutative source buffer values before
      valid represented scratch admitted
    have same := Prod.mk.inj (checked.symm.trans (settled budget (Nat.le_refl budget)))
    rcases same with ⟨rfl, rfl⟩
    obtain ⟨result, after, continued, closed⟩ := continue_refines external allocator source values exit handle initialAfter ready.1 admitted
    refine ⟨result, after, budget, ?_, ?_⟩
    · intro fuel enough
      have executed : run normalizationOwnershipCode external fuel allocator commutative source buffer values exit before = (result, after) := by
        simp only [run, settled fuel enough, continued]
      exact ⟨executed, run_result external fuel allocator commutative source buffer values exit before after result valid represented scratch admitted executed⟩
    · intro incomplete
      rw [incomplete] at closed
      exact closed.outcome

end Compiler.Extraction.Memory.Arguments.Normalization
