/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationTrace

namespace Compiler.Extraction.Cache.NormalizationOwnership.Trace

theorem take_replay (p : PreparedPrimitives σ ε) (mismatch : ε) (lookup : State)
    (before : σ) (suffix : List (Event ε)) :
    let execution := normalizationOwnershipCode.takeWith ((record p).allocate .duplicate) lookup ⟨before, []⟩
    normalizationOwnershipCode.takeWith ((replay (execution.2.events ++ suffix) mismatch).allocate .duplicate)
      lookup 0 = (execution.1, execution.2.events.length) := by
  cases owned : lookup.owned
  · cases allocated : p.allocate .duplicate before with
    | mk succeeded after =>
      simp [Code.takeWith, owned, record, replay, allocate, allocated]
  · simp [Code.takeWith, owned]

theorem take_replay_at (p : PreparedPrimitives σ ε) (mismatch : ε) (lookup : State)
    (before : σ) (leading suffix : List (Event ε)) :
    let execution := normalizationOwnershipCode.takeWith ((record p).allocate .duplicate) lookup ⟨before, []⟩
    normalizationOwnershipCode.takeWith
      ((replay (leading ++ (execution.2.events ++ suffix)) mismatch).allocate .duplicate) lookup leading.length =
      (execution.1, leading.length + execution.2.events.length) := by
  have replayed := take_replay p mismatch lookup before suffix
  have mapped := take_transport normalizationOwnershipCode
    ((replay ((normalizationOwnershipCode.takeWith ((record p).allocate .duplicate) lookup ⟨before, []⟩).2.events ++ suffix) mismatch).allocate .duplicate)
    ((replay (leading ++ ((normalizationOwnershipCode.takeWith ((record p).allocate .duplicate) lookup ⟨before, []⟩).2.events ++ suffix)) mismatch).allocate .duplicate)
    (fun cursor => leading.length + cursor) (fun cursor => (replay_prefix _ leading mismatch).allocate .duplicate cursor) lookup 0
  rw [replayed] at mapped
  simpa only [Nat.add_zero] using mapped

end Compiler.Extraction.Cache.NormalizationOwnership.Trace
