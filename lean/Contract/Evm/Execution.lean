/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Evm.Subset

namespace Contract.Evm

theorem run_more (code input fuel state cost result extra)
    (h : run code input fuel state = .finished cost result) :
    run code input (fuel + extra) state = .finished cost result := by
  induction fuel generalizing state cost with
  | zero => simp [run] at h
  | succ fuel ih =>
    rw [show fuel + 1 + extra = (fuel + extra) + 1 by omega, run]
    cases hs : step code input state with
    | next c after =>
      cases hr : run code input fuel after <;> simp [run, hs, hr, Execution.charge] at h
      case finished rest out =>
        obtain ⟨rfl, rfl⟩ := h
        simpa [hs, Execution.charge] using
          congrArg (Execution.charge c) (ih after rest hr)
    | halt c out => simpa [run, hs] using h
    | fault => simp [run, hs] at h
    | unsupported op => simp [run, hs] at h

/-- A completed costed execution determines both success and the exact OOG
boundary. The artifact proof must discharge the costed execution premise; no
hypothesis assumes compiler correctness. -/
theorem metered_of_run (code input fuel state cost result gas)
    (h : run code input fuel state = .finished cost result) :
    runMetered code input fuel gas state =
      if cost ≤ gas then .finished (gas - cost) result else .exceptional := by
  induction fuel generalizing state cost gas with
  | zero => simp [run] at h
  | succ fuel ih =>
    cases hs : step code input state with
    | next c after =>
      cases hr : run code input fuel after <;> simp [run, hs, hr, Execution.charge] at h
      case finished rest out =>
        obtain ⟨rfl, rfl⟩ := h
        simp only [runMetered, hs]
        split
        · rw [ih after rest (gas - c) hr]
          by_cases enough : rest ≤ gas - c
          · simp only [if_pos enough, if_pos (show c + rest ≤ gas by omega)]
            congr 1 <;> omega
          · simp only [if_neg enough, if_neg (show ¬ c + rest ≤ gas by omega)]
        · rename_i hc
          rw [if_neg (by omega)]
    | halt c out =>
      simp [run, hs] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [runMetered, hs]
    | fault => simp [run, hs] at h
    | unsupported op => simp [run, hs] at h

end Contract.Evm
