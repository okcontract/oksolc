/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationTraceInit

namespace Compiler.Extraction.Cache.NormalizationOwnership.Trace

/-- Every complete source-bound ownership execution replays at the same result
and consumes exactly its own events. The arbitrary suffix is left untouched.
The result includes preparation faults; replay does not reinterpret them as OOM. -/
theorem run_replay (p : PreparedPrimitives σ ε) (mismatch : ε) (commutative : Bool)
    (length bufferLength : Nat) (exit : Exit) (before : σ) (suffix : List (Event ε)) :
    let execution := normalizationOwnershipCode.runPrepared commutative length bufferLength (record p) exit ⟨before, []⟩
    normalizationOwnershipCode.runPrepared commutative length bufferLength
      (replay (execution.2.events ++ suffix) mismatch) exit 0 = (execution.1, execution.2.events.length) := by
  cases initialized : normalizationOwnershipCode.initPrepared commutative length bufferLength (record p) ⟨before, []⟩ with
  | mk result prepared =>
    cases result with
    | error failure =>
      have replayed := init_replay p mismatch commutative length bufferLength before suffix
      simp only [initialized] at replayed
      simp only [Code.runPrepared, initialized, replayed]
    | ok lookup =>
      cases lookup with
      | none =>
        have replayed := init_replay p mismatch commutative length bufferLength before suffix
        simp only [initialized] at replayed
        simp only [Code.runPrepared, initialized, replayed]
      | some lookup =>
        have recorded := continue_record_prefix p exit lookup prepared.effects prepared.events
        have replayed := continue_replay_prefix p mismatch exit lookup prepared.effects prepared.events suffix
        cases continued : normalizationOwnershipCode.continueWith (record p).toPrimitives exit lookup ⟨prepared.effects, []⟩ with
        | mk result after =>
          rw [continued] at recorded replayed
          have replayInit := init_replay p mismatch commutative length bufferLength before (after.events ++ suffix)
          simp only [initialized] at replayInit
          simp only [Code.runPrepared, initialized, recorded, prepend, List.append_assoc, replayInit,
            replayed, List.length_append]

end Compiler.Extraction.Cache.NormalizationOwnership.Trace
