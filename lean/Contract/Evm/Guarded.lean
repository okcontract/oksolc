/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Std

/-! Generic execution with gas sentries. Unlike a cost-only trace, `needed`
records a gas threshold that may exceed consumption (notably for SSTORE).
The state/result types are arbitrary, so the lemmas compose storage effects. -/
namespace Contract.Evm.Guarded

inductive Step (σ α : Type) where
  | next (cost guard : Nat) (state : σ)
  | halt (cost : Nat) (result : α)
  | fault
  | unsupported (opcode : UInt8)

inductive Trace (α : Type) where
  | finished (used needed : Nat) (result : α)
  | fault
  | unsupported (opcode : UInt8)
  | exhausted
  deriving DecidableEq, Repr

def Trace.charge (cost guard : Nat) : Trace α → Trace α
  | .finished used needed result => .finished (cost + used) (max guard (cost + needed)) result
  | other => other

def run (step : σ → Step σ α) : Nat → σ → Trace α
  | 0, _ => .exhausted
  | fuel + 1, state => match step state with
    | .next cost guard after => (run step fuel after).charge cost guard
    | .halt cost result => .finished cost cost result
    | .fault => .fault
    | .unsupported op => .unsupported op

inductive Metered (α : Type) where
  | finished (remaining : Nat) (result : α)
  | exceptional
  | unsupported (opcode : UInt8)
  | exhausted
  deriving DecidableEq, Repr

def runMetered (step : σ → Step σ α) : Nat → Nat → σ → Metered α
  | 0, _, _ => .exhausted
  | fuel + 1, gas, state => match step state with
    | .next cost guard after =>
      if cost ≤ gas ∧ guard ≤ gas then runMetered step fuel (gas - cost) after else .exceptional
    | .halt cost result => if cost ≤ gas then .finished (gas - cost) result else .exceptional
    | .fault => .exceptional
    | .unsupported op => .unsupported op

theorem run_more (step : σ → Step σ α) (fuel state used needed result extra)
    (h : run step fuel state = .finished used needed result) :
    run step (fuel + extra) state = .finished used needed result := by
  induction fuel generalizing state used needed with
  | zero => simp [run] at h
  | succ fuel ih =>
    rw [show fuel + 1 + extra = (fuel + extra) + 1 by omega, run]
    cases hs : step state with
    | next c guard after =>
      cases hr : run step fuel after <;> simp [run, hs, hr, Trace.charge] at h
      case finished rest need out =>
        obtain ⟨rfl, rfl, rfl⟩ := h
        simpa [Trace.charge] using congrArg (Trace.charge c guard) (ih after rest need hr)
    | halt c out => simpa [run, hs] using h
    | fault => simp [run, hs] at h
    | unsupported op => simp [run, hs] at h

theorem used_le_needed (step : σ → Step σ α) (fuel state used needed result)
    (h : run step fuel state = .finished used needed result) : used ≤ needed := by
  induction fuel generalizing state used needed with
  | zero => simp [run] at h
  | succ fuel ih =>
    cases hs : step state with
    | next c guard after =>
      cases hr : run step fuel after <;> simp [run, hs, hr, Trace.charge] at h
      case finished rest need out =>
        obtain ⟨rfl, rfl, rfl⟩ := h
        have := ih after rest need hr
        omega
    | halt c out => simp [run, hs] at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact Nat.le_refl _
    | fault => simp [run, hs] at h
    | unsupported op => simp [run, hs] at h

/-- A proved completed trace determines execution for *every* gas budget,
including sentry failures and OOG after intermediate state changes. -/
theorem metered_of_run (step : σ → Step σ α) (fuel state used needed result gas)
    (h : run step fuel state = .finished used needed result) :
    runMetered step fuel gas state =
      if needed ≤ gas then .finished (gas - used) result else .exceptional := by
  induction fuel generalizing state used needed gas with
  | zero => simp [run] at h
  | succ fuel ih =>
    cases hs : step state with
    | next c guard after =>
      cases hr : run step fuel after <;> simp [run, hs, hr, Trace.charge] at h
      case finished rest need out =>
        obtain ⟨rfl, rfl, rfl⟩ := h
        simp only [runMetered, hs]
        split
        · rw [ih after rest need (gas - c) hr]
          by_cases enough : need ≤ gas - c
          · rw [if_pos enough, if_pos (by omega)]
            congr 1 <;> omega
          · rw [if_neg enough, if_neg (by omega)]
        · rw [if_neg (by omega)]
    | halt c out =>
      simp [run, hs] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp [runMetered, hs]
    | fault => simp [run, hs] at h
    | unsupported op => simp [run, hs] at h

theorem metered_of_fault (step : σ → Step σ α) (fuel state gas)
    (h : run step fuel state = .fault) : runMetered step fuel gas state = .exceptional := by
  induction fuel generalizing state gas with
  | zero => simp [run] at h
  | succ fuel ih =>
    cases hs : step state with
    | next c guard after =>
      cases hr : run step fuel after <;> simp [run, hs, hr, Trace.charge] at h
      simp only [runMetered, hs]
      split
      · exact ih after (gas - c) hr
      · rfl
    | halt c out => simp [run, hs] at h
    | fault => simp [runMetered, hs]
    | unsupported op => simp [run, hs] at h

theorem fault_more (step : σ → Step σ α) (fuel state extra)
    (h : run step fuel state = .fault) : run step (fuel + extra) state = .fault := by
  induction fuel generalizing state with
  | zero => simp [run] at h
  | succ fuel ih =>
    rw [show fuel + 1 + extra = (fuel + extra) + 1 by omega, run]
    cases hs : step state with
    | next c guard after =>
      cases hr : run step fuel after <;> simp [run, hs, hr, Trace.charge] at h
      simpa only [Trace.charge] using congrArg (Trace.charge c guard) (ih after hr)
    | halt c out => simp [run, hs] at h
    | fault => rfl
    | unsupported op => simp [run, hs] at h

end Contract.Evm.Guarded
