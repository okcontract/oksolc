/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationTrace

namespace Compiler.Extraction.Cache.NormalizationOwnership.Trace

theorem move_owned (lookup : State) (expected next : Owner) : (lookup.move expected next).owned = lookup.owned := by
  unfold State.move
  split <;> rfl

/-- The suffix belongs to later invocations. Replaying this continuation
consumes exactly its recorded events, including failed duplication and cleanup. -/
theorem continue_replay (p : PreparedPrimitives σ ε) (mismatch : ε) (exit : Exit) (lookup : State)
    (before : σ) (suffix : List (Event ε)) :
    let execution := normalizationOwnershipCode.continueWith (record p).toPrimitives exit lookup ⟨before, []⟩
    normalizationOwnershipCode.continueWith (replay (execution.2.events ++ suffix) mismatch).toPrimitives exit lookup 0 =
      (execution.1, execution.2.events.length) := by
  cases exit with
  | lookup =>
    cases owned : lookup.owned <;>
      simp [Code.continueWith, Code.finishWith, Code.deinitWith, normalizationOwnershipCode, owned,
        record, replay, release]
  | transfer | cleanup =>
    cases owned : lookup.owned
    · cases allocated : p.allocate .duplicate before with
      | mk succeeded after =>
        cases succeeded <;>
          simp [Code.continueWith, Code.finishWith, Code.takeWith, Code.deinitWith, normalizationOwnershipCode, owned,
            record, replay, allocate, release, allocated, move_owned]
    · simp [Code.continueWith, Code.finishWith, Code.takeWith, Code.deinitWith, normalizationOwnershipCode, owned,
        record, replay, release, move_owned]

theorem continue_record_prefix (p : PreparedPrimitives σ ε) (exit : Exit) (lookup : State)
    (before : σ) (leading : List (Event ε)) :
    normalizationOwnershipCode.continueWith (record p).toPrimitives exit lookup ⟨before, leading⟩ =
      let execution := normalizationOwnershipCode.continueWith (record p).toPrimitives exit lookup ⟨before, []⟩
      (execution.1, prepend leading execution.2) := by
  simpa [prepend] using continue_transport normalizationOwnershipCode (record p) (record p) (prepend leading)
    (prefix_transport p leading) exit lookup ⟨before, []⟩

theorem continue_replay_prefix (p : PreparedPrimitives σ ε) (mismatch : ε) (exit : Exit) (lookup : State)
    (before : σ) (leading suffix : List (Event ε)) :
    let execution := normalizationOwnershipCode.continueWith (record p).toPrimitives exit lookup ⟨before, []⟩
    normalizationOwnershipCode.continueWith (replay (leading ++ (execution.2.events ++ suffix)) mismatch).toPrimitives
      exit lookup leading.length = (execution.1, leading.length + execution.2.events.length) := by
  have replayed := continue_replay p mismatch exit lookup before suffix
  have mapped := continue_transport normalizationOwnershipCode
    (replay ((normalizationOwnershipCode.continueWith (record p).toPrimitives exit lookup ⟨before, []⟩).2.events ++ suffix) mismatch)
    (replay (leading ++ ((normalizationOwnershipCode.continueWith (record p).toPrimitives exit lookup ⟨before, []⟩).2.events ++ suffix)) mismatch)
    (fun cursor => leading.length + cursor) (replay_prefix _ leading mismatch) exit lookup 0
  rw [replayed] at mapped
  simpa only [Nat.add_zero] using mapped

/-- A successful physical preparation may change all private effects. Replay
continues from those reached effects and consumes the same suffix of calls. -/
theorem prepared_replay (p : PreparedPrimitives σ ε) (mismatch : ε) (exit : Exit) (lookup : State)
    (before : σ) (leading suffix : List (Event ε)) :
    let (result, prepared) := (record p).prepare lookup ⟨before, leading⟩
    let execution : PreparedResult ε × Recorded σ ε := match result with
      | .error error => (.error (error, lookup), prepared)
      | .ok () =>
        let (result, after) := normalizationOwnershipCode.continueWith (record p).toPrimitives exit lookup prepared
        (.ok result, after)
    let q := replay (execution.2.events ++ suffix) mismatch
    let (result, prepared) := q.prepare lookup leading.length
    let replayed : PreparedResult ε × Nat := match result with
      | .error error => (.error (error, lookup), prepared)
      | .ok () =>
        let (result, after) := normalizationOwnershipCode.continueWith q.toPrimitives exit lookup prepared
        (.ok result, after)
    replayed = (execution.1, execution.2.events.length) := by
  cases prepared : p.prepare lookup before with
  | mk result reached =>
    have recorded : (record p).prepare lookup ⟨before, leading⟩ =
        (result, ⟨reached, leading ++ [.prepare lookup result]⟩) := by simp [record, prepared]
    cases result with
    | error error =>
      simp [recorded, replay, prepare]
    | ok returned =>
      cases returned
      have continued := continue_record_prefix p exit lookup reached (leading ++ [.prepare lookup (.ok ())])
      have replayed := continue_replay_prefix p mismatch exit lookup reached (leading ++ [.prepare lookup (.ok ())]) suffix
      cases completion : normalizationOwnershipCode.continueWith (record p).toPrimitives exit lookup ⟨reached, []⟩ with
      | mk outcome after =>
        rw [completion] at continued replayed
        have replayStep : (replay (((leading ++ [.prepare lookup (.ok ())]) ++ after.events) ++ suffix) mismatch).prepare
            lookup leading.length = (.ok (), leading.length + 1) := by simp [replay, prepare]
        simp only [recorded, continued, prepend, replayStep]
        simpa only [List.append_assoc, List.length_append, List.length_singleton, Nat.add_assoc] using
          congrArg (fun result : (Outcome × State) × Nat => (Except.ok result.1, result.2)) replayed

end Compiler.Extraction.Cache.NormalizationOwnership.Trace
