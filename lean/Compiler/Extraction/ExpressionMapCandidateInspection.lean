/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapCandidate

namespace Compiler.Extraction.ExpressionMap.Candidate
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray Buckets
open Compiler.Extraction.Cache (Key)

/-- Factoring the common candidate does not change the previous execution,
including every rejected read and the order of short-circuit guards. -/
theorem run_unfold (state : State) (capacity : BitVec 32) (bucket index remaining : Nat)
    (fp : BitVec 7) (query : Key) (source : View) :
    run state capacity bucket index remaining fp query source = (do
      let bits ← Metadata.readByte state bucket index
      if Metadata.isFree bits || remaining == 0 then return .stop
      if Metadata.isUsed bits && bits.toNat % 128 == fp.toNat then
        if ← KeyComparison.run state capacity bucket index query source then
          let .scalar (.int false 32 id) ← Values.read state capacity bucket index | .error .unsupported
          return .hit (BitVec.ofInt 32 id)
      return .next) := by
  unfold run inspect
  cases read : Metadata.readByte state bucket index with
  | error fault => rfl
  | ok bits =>
    by_cases stop : (Metadata.isFree bits || remaining == 0) = true
    · simp [stop, bind, Except.bind, pure, Except.pure]
    · by_cases candidate : (Metadata.isUsed bits && bits.toNat % 128 == fp.toNat) = true
      · cases compared : KeyComparison.run state capacity bucket index query source with
        | error fault => simp [stop, candidate, bind, Except.bind, pure, Except.pure]
        | ok equal => cases equal <;> simp [stop, candidate, bind, Except.bind, pure, Except.pure]
                      rfl
      · simp [stop, candidate, bind, Except.bind, pure, Except.pure]

theorem inspect_metadata (state : State) (capacity : BitVec 32) (bucket index remaining : Nat)
    (fp : BitVec 7) (query : Key) (source : View) (bits : BitVec 8) (action : Action)
    (ran : inspect state capacity bucket index remaining fp query source = .ok (bits, action)) :
    Metadata.readByte state bucket index = .ok bits := by
  unfold inspect at ran
  cases read : Metadata.readByte state bucket index with
  | error fault => simp [read, bind, Except.bind] at ran
  | ok byte =>
    simp only [read, bind, Except.bind, pure, Except.pure] at ran
    split at ran
    · cases ran; rfl
    · split at ran
      · cases compared : KeyComparison.run state capacity bucket index query source with
        | error fault => simp [compared] at ran
        | ok equal => cases equal <;> simp_all
      · cases ran; rfl

theorem inspect_of_run (state : State) (capacity : BitVec 32) (bucket index remaining : Nat)
    (fp : BitVec 7) (query : Key) (source : View) (result : Result)
    (ran : run state capacity bucket index remaining fp query source = .ok result) :
    ∃ bits, inspect state capacity bucket index remaining fp query source = .ok (bits, result.action) := by
  unfold run at ran
  cases observed : inspect state capacity bucket index remaining fp query source with
  | error fault => simp [observed, bind, Except.bind] at ran
  | ok pair =>
    obtain ⟨bits, action⟩ := pair
    refine ⟨bits, ?_⟩
    simp only [observed, bind, Except.bind] at ran
    cases action with
    | stop => cases ran; rfl
    | next => cases ran; rfl
    | hit =>
      cases read : Values.read state capacity bucket index with
      | error fault => simp [read] at ran
      | ok value =>
        simp only [read, pure, Except.pure] at ran
        split at ran
        · cases ran; rfl
        · cases ran

/-- The general candidate proof supplies all inspection outcomes. getOrPut
can consume the shared decision without assuming or performing an ID read. -/
theorem inspect_verified (state : State) (capacity : BitVec 32) (bucket index remaining : Nat)
    (fp : BitVec 7) (query : Key) (source : View) (table : OwnedKeys.Table)
    (binding : Table.Binding place safety receiver bucket capacity state table)
    (inside : index < capacity.toNat) (queryRead : Represents state source query.arguments)
    (bounded : source.length * 4 < addressLimit) :
    ∃ bits result, inspect state capacity bucket index remaining fp query source = .ok (bits, result.action) ∧
      Metadata.readByte state bucket index = .ok bits ∧
      Correct state capacity bucket index remaining fp query table bits result := by
  obtain ⟨bits, result, read, ran, correct⟩ := run_verified state capacity bucket index remaining fp query source table binding inside queryRead bounded
  obtain ⟨observed, inspected⟩ := inspect_of_run state capacity bucket index remaining fp query source result ran
  have same := inspect_metadata state capacity bucket index remaining fp query source observed result.action inspected
  have equal := Except.ok.inj (read.symm.trans same)
  subst observed
  exact ⟨bits, result, inspected, read, correct⟩

end Compiler.Extraction.ExpressionMap.Candidate
