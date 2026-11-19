/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationTraceReplay

namespace Compiler.Extraction.Cache.NormalizationOwnership.Trace

/-- Replay stops at the live prefix, including semantic preparation failure.
The suffix belongs to subsequent graph/caller operations and is untouched. -/
theorem init_replay (p : PreparedPrimitives σ ε) (mismatch : ε) (commutative : Bool)
    (length bufferLength : Nat) (before : σ) (suffix : List (Event ε)) :
    let execution := normalizationOwnershipCode.initPrepared commutative length bufferLength (record p) ⟨before, []⟩
    normalizationOwnershipCode.initPrepared commutative length bufferLength
      (replay (execution.2.events ++ suffix) mismatch) 0 = (execution.1, execution.2.events.length) := by
  cases needed : !commutative || decide (length < normalizationOwnershipCode.threshold) with
  | true => simp [Code.initPrepared, Code.initWith, needed]
  | false =>
    by_cases fits : length ≤ bufferLength
    · have choice : normalizationOwnershipCode.useScratch.test length bufferLength = true := by
        simp [normalizationOwnershipCode, Comparison.test, fits]
      have own : normalizationOwnershipCode.ownTemporary.test length bufferLength = false := by
        simp [normalizationOwnershipCode, Comparison.test, Nat.not_lt.mpr fits]
      cases prepared : p.prepare { origin := .scratch } before with
      | mk result reached =>
        cases result <;>
          simp [Code.initPrepared, Code.initWith, needed, choice, own, Nat.not_lt.mpr fits,
            record, replay, prepare, prepared]
    · have choice : normalizationOwnershipCode.useScratch.test length bufferLength = false := by
        simp [normalizationOwnershipCode, Comparison.test, fits]
      have own : normalizationOwnershipCode.ownTemporary.test length bufferLength = true := by
        simp [normalizationOwnershipCode, Comparison.test, Nat.lt_of_not_ge fits]
      cases allocated : p.allocate .temporary before with
      | mk succeeded selected =>
        cases succeeded with
        | false => simp [Code.initPrepared, Code.initWith, needed, choice, record, replay, allocate, allocated]
        | true =>
          cases prepared : p.prepare { origin := .allocation, owner := .lookup, owned := true } selected with
          | mk result reached =>
            cases result <;>
              simp [Code.initPrepared, Code.initWith, needed, choice, own, record, replay, allocate, prepare, allocated, prepared]

theorem init_replay_at (p : PreparedPrimitives σ ε) (mismatch : ε) (commutative : Bool)
    (length bufferLength : Nat) (before : σ) (leading suffix : List (Event ε)) :
    let execution := normalizationOwnershipCode.initPrepared commutative length bufferLength (record p) ⟨before, []⟩
    normalizationOwnershipCode.initPrepared commutative length bufferLength
      (replay (leading ++ (execution.2.events ++ suffix)) mismatch) leading.length =
      (execution.1, leading.length + execution.2.events.length) := by
  have replayed := init_replay p mismatch commutative length bufferLength before suffix
  have mapped := init_prepared_transport normalizationOwnershipCode
    (replay ((normalizationOwnershipCode.initPrepared commutative length bufferLength (record p) ⟨before, []⟩).2.events ++ suffix) mismatch)
    (replay (leading ++ ((normalizationOwnershipCode.initPrepared commutative length bufferLength (record p) ⟨before, []⟩).2.events ++ suffix)) mismatch)
    (fun cursor => leading.length + cursor) (replay_prefix _ leading mismatch) commutative length bufferLength 0
  rw [replayed] at mapped
  simpa only [Nat.add_zero] using mapped

end Compiler.Extraction.Cache.NormalizationOwnership.Trace
