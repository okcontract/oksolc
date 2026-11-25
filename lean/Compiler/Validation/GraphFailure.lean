/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Validation.GraphInventory

/-! Allocation-cut failure sweep certification for `ExpressionClasses`.

Each `Observation` records an execution of the production interner under a
deterministic allocation cut (`failureAt = some i` for `0 ≤ i < N`, followed by
the complete baseline `failureAt = none` with `N` allocations).

In contrast to vacuous `ordinary result = true` wrappers, `Failure.certifySweep`
proves in the Lean kernel that:
1. Every allocation cut `0 .. N - 1` produces a well-formed partial state whose
   completed prefix and retained CSE cache entries preserve exact EVM semantics;
2. The final baseline run (`failureAt = none`) is `.complete`, covers all
   `before.length` source nodes, and preserves root + full inventory semantics. -/
namespace Compiler.Validation.Failure
open Contract Contract.Yul

inductive Outcome where
  | complete
  | outOfMemory
  deriving DecidableEq, Repr

/-- Captured interner state at termination (either `.complete` or `.outOfMemory`). -/
structure Attempt where
  outcome : Outcome
  after : List Node
  ids : List Nat
  cache : List Inventory.Entry
  deriving DecidableEq, Repr

/-- Metadata + captured interner state for a single FailingAllocator cut. -/
structure Observation where
  failureAt : Option Nat
  successfulAllocations : Nat
  inducedFailure : Bool
  attempt : Attempt
  deriving DecidableEq, Repr

def Progress (before : List Node) (attempt : Attempt) : Prop :=
  match attempt.outcome with
  | .complete => attempt.ids.length = before.length
  | .outOfMemory => attempt.ids.length < before.length

instance (before : List Node) (attempt : Attempt) : Decidable (Progress before attempt) := by
  unfold Progress
  cases attempt.outcome <;> infer_instance

def validateAttempt (fuel : Nat) (before : List Node) (attempt : Attempt) : Bool :=
  decide (Progress before attempt) &&
    Inventory.validate fuel (before.take attempt.ids.length) attempt.after attempt.ids attempt.cache

/-- Every retained representative is well-formed; all completed source IDs and
all captured cache entries preserve their exact EVM meaning. -/
def Preserves (before : List Node) (attempt : Attempt)
    (ctx : Context) (locals : String → Word) : Prop :=
  Progress before attempt ∧
    Inventory.Preserves (before.take attempt.ids.length) attempt.after attempt.ids attempt.cache ctx locals

theorem attempt_sound (fuel : Nat) (before : List Node) (attempt : Attempt)
    (accepted : validateAttempt fuel before attempt = true)
    (ctx : Context) (locals : String → Word) :
    Preserves before attempt ctx locals := by
  simp only [validateAttempt, Bool.and_eq_true, decide_eq_true_eq] at accepted
  exact ⟨accepted.1, Inventory.validate_sound fuel _ _ _ _ accepted.2 ctx locals⟩

/-- Check that `cuts` is the contiguous allocation-cut prefix `0, 1, ..., cuts.length - 1`,
each inducing `.outOfMemory` at its exact `failureAt` index. -/
def checkCutIndices : Nat → List Observation → Bool
  | _, [] => true
  | idx, obs :: rest =>
    decide (obs.failureAt = some idx ∧ obs.successfulAllocations = idx ∧
      obs.inducedFailure = true ∧ obs.attempt.outcome = .outOfMemory) &&
      checkCutIndices (idx + 1) rest

theorem checkCutIndices_sound (idx : Nat) (cuts : List Observation)
    (ok : checkCutIndices idx cuts = true) :
    ∀ obs ∈ cuts, obs.inducedFailure = true ∧ obs.attempt.outcome = .outOfMemory := by
  induction cuts generalizing idx with
  | nil => intro _ h; cases h
  | cons obs rest ih =>
    simp only [checkCutIndices, Bool.and_eq_true, decide_eq_true_eq] at ok
    intro target hmem
    rcases List.mem_cons.mp hmem with rfl | hrest
    · exact ⟨ok.1.2.2.1, ok.1.2.2.2⟩
    · exact ih (idx + 1) ok.2 target hrest

/-- Full sweep validator: checks contiguous OOM cuts `0 .. N - 1`, a non-empty cut set
(`N > 0`), a `.complete` baseline with `N` allocations, and semantic preservation of
every observation in the sweep. -/
def validateSweep (fuel : Nat) (before : List Node) (beforeRoot : Nat)
    (observations : List Observation) : Bool :=
  match observations.reverse with
  | [] => false
  | baseline :: revCuts =>
    let cuts := revCuts.reverse
    let n := cuts.length
    decide (n > 0 ∧ baseline.failureAt = none ∧ baseline.successfulAllocations = n ∧
      baseline.inducedFailure = false ∧ baseline.attempt.outcome = .complete ∧
      beforeRoot < before.length) &&
      checkCutIndices 0 cuts &&
      observations.all (fun obs => validateAttempt fuel before obs.attempt)

theorem certifySweep (fuel : Nat) (before : List Node) (beforeRoot : Nat)
    (observations : List Observation)
    (accepted : validateSweep fuel before beforeRoot observations = true)
    (ctx : Context) (locals : String → Word) :
    (∀ obs ∈ observations, Preserves before obs.attempt ctx locals) ∧
    (∃ baseline ∈ observations,
      baseline.failureAt = none ∧
      baseline.attempt.outcome = .complete ∧
      Inventory.Preserves before baseline.attempt.after baseline.attempt.ids baseline.attempt.cache ctx locals ∧
      ∃ afterRoot value,
        baseline.attempt.ids[beforeRoot]? = some afterRoot ∧
        evaluate before beforeRoot ctx locals = some value ∧
        evaluate baseline.attempt.after afterRoot ctx locals = some value) := by
  unfold validateSweep at accepted
  cases hrev : observations.reverse with
  | nil => simp [hrev] at accepted
  | cons baseline revCuts =>
    simp only [hrev, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at accepted
    rcases accepted with ⟨⟨⟨_, hfailNone, _, _, hcomplete, hrootLt⟩, _⟩, hall⟩
    have hbaseMem : baseline ∈ observations := by
      have hm : baseline ∈ observations.reverse := by simp [hrev]
      exact List.mem_reverse.mp hm
    have hallSound : ∀ obs ∈ observations, Preserves before obs.attempt ctx locals :=
      fun obs hm => attempt_sound fuel before obs.attempt (hall obs hm) ctx locals
    refine ⟨hallSound, baseline, hbaseMem, hfailNone, hcomplete, ?_⟩
    have hbasePres := hallSound baseline hbaseMem
    have hlen : baseline.attempt.ids.length = before.length := by
      simpa [Progress, hcomplete] using hbasePres.1
    have hinv : Inventory.Preserves before baseline.attempt.after baseline.attempt.ids baseline.attempt.cache ctx locals := by
      have htake : before.take baseline.attempt.ids.length = before := by
        rw [hlen, List.take_length]
      simpa [htake] using hbasePres.2
    refine ⟨hinv, ?_⟩
    have hidLt : beforeRoot < baseline.attempt.ids.length := by omega
    let afterRoot := baseline.attempt.ids[beforeRoot]
    have hsel : baseline.attempt.ids[beforeRoot]? = some afterRoot := List.getElem?_eq_getElem hidLt
    obtain ⟨left, right, hsrc, hdst, hrel, _⟩ := hinv
    obtain ⟨value, hfirst, hsecond⟩ := Inventory.result_at left right baseline.attempt.ids hrel beforeRoot afterRoot hsel
    exact ⟨afterRoot, value, hsel, by simp [evaluate, hsrc, hfirst], by simp [evaluate, hdst, hsecond]⟩

#audit_contract_proof Compiler.Validation.Failure.attempt_sound
#audit_contract_proof Compiler.Validation.Failure.certifySweep

end Compiler.Validation.Failure
