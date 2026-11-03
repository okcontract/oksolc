/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapProbePrefix

namespace Compiler.Extraction.ExpressionMap.Probe
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray Buckets
open Compiler.Extraction.Cache (Key)

inductive Outcome where
  | hit (index : Nat)
  | miss (index first : Nat)
  deriving DecidableEq, BEq

/-- Complete post-hash probe, including the final metadata read when limit is
zero. The miss retains the two native locals used by getOrPut's selection tail.
The impossible next-at-zero branch is a rejection, never a fabricated miss. -/
def loop (state : State) (capacity : BitVec 32) (bucket : Nat) (hash : BitVec 64)
    (query : Key) (source : View) (remaining index first : Nat) : Except Fault Outcome := do
  let (bits, action) ← Candidate.inspect state capacity bucket index remaining (fingerprint hash) query source
  match action with
  | .hit => .ok (.hit index)
  | .stop => .ok (.miss index first)
  | .next => match remaining with
    | 0 => .error .memoryValidity
    | n + 1 =>
      loop state capacity bucket hash query source n (advance capacity index)
        (remember capacity index first (fingerprint hash) bits)
termination_by remaining

def run (state : State) (capacity : BitVec 32) (bucket : Nat) (hash : BitVec 64)
    (query : Key) (source : View) : Except Fault Outcome :=
  loop state capacity bucket hash query source capacity.toNat (start capacity hash) capacity.toNat

def Outcome.index : Outcome → Option Nat
  | .hit index => some index
  | .miss _ _ => none

/-- getIndex has no tombstone local. Keep its execution separate and erase
that bookkeeping from the shared insertion proof below. -/
def lookupLoop (state : State) (capacity : BitVec 32) (bucket : Nat) (hash : BitVec 64)
    (query : Key) (source : View) (remaining index : Nat) : Except Fault (Option Nat) := do
  let (_, action) ← Candidate.inspect state capacity bucket index remaining (fingerprint hash) query source
  match action with
  | .hit => .ok (some index)
  | .stop => .ok none
  | .next => match remaining with
    | 0 => .error .memoryValidity
    | n + 1 => lookupLoop state capacity bucket hash query source n (advance capacity index)
termination_by remaining

theorem loop_lookup (state : State) (capacity : BitVec 32) (bucket : Nat) (hash : BitVec 64)
    (query : Key) (source : View) (remaining index first : Nat) :
    (loop state capacity bucket hash query source remaining index first).map Outcome.index =
      lookupLoop state capacity bucket hash query source remaining index := by
  induction remaining generalizing index first with
  | zero =>
    rw [loop, lookupLoop]
    cases inspected : Candidate.inspect state capacity bucket index 0 (fingerprint hash) query source with
    | error fault => rfl
    | ok pair => obtain ⟨bits, action⟩ := pair; cases action <;> rfl
  | succ remaining ih =>
    rw [loop, lookupLoop]
    cases inspected : Candidate.inspect state capacity bucket index (remaining + 1) (fingerprint hash) query source with
    | error fault => rfl
    | ok pair =>
      obtain ⟨bits, action⟩ := pair
      cases action with
      | stop | hit => rfl
      | next => exact ih (advance capacity index) (remember capacity index first (fingerprint hash) bits)

/-- Execution-derived prefix evidence, before using the map's routing invariant
to prove absence. A miss still may be exhaustion of a completely full map. -/
def Completed (state : State) (capacity : BitVec 32) (bucket : Nat) (hash : BitVec 64)
    (query : Key) (table : OwnedKeys.Table) : Outcome → Prop
  | .hit index => index < capacity.toNat ∧ Table.Used state bucket index ∧
      ∃ entry, table query = some entry ∧ Table.EntryView capacity bucket index state query entry
  | .miss index first => ∃ distance, distance ≤ capacity.toNat ∧ index = slot capacity hash distance ∧
      Passed state capacity bucket hash query table distance ∧ Remembered state capacity bucket hash distance first ∧
      (Metadata.observe state bucket index = .ok (true, false) ∨ distance = capacity.toNat)

theorem free_unused (bits : BitVec 8) (free : Metadata.isFree bits = true) : bits = 0 ∧ Metadata.isUsed bits = false := by
  have zero : bits = 0 := by simpa only [Metadata.isFree, beq_iff_eq] using free
  exact ⟨zero, zero ▸ rfl⟩

theorem loop_verified (state : State) (capacity : BitVec 32) (bucket : Nat) (hash : BitVec 64)
    (query : Key) (source : View) (table : OwnedKeys.Table)
    (binding : Table.Binding place safety receiver bucket capacity state table) (power : Power capacity)
    (queryRead : Represents state source query.arguments) (bounded : source.length * 4 < addressLimit)
    (remaining distance first : Nat) (budget : distance + remaining = capacity.toNat)
    (passed : Passed state capacity bucket hash query table distance)
    (remembered : Remembered state capacity bucket hash distance first) :
    ∃ outcome, loop state capacity bucket hash query source remaining (slot capacity hash distance) first = .ok outcome ∧
      Completed state capacity bucket hash query table outcome := by
  induction remaining generalizing distance first with
  | zero =>
    obtain ⟨bits, result, inspected, read, correct⟩ := Candidate.inspect_verified state capacity bucket (slot capacity hash distance)
      0 (fingerprint hash) query source table binding (slot_bound power) queryRead bounded
    cases result with
    | stop =>
      refine ⟨.miss (slot capacity hash distance) first, ?_, distance, by omega, rfl, passed, remembered, Or.inr (by omega)⟩
      rw [loop, inspected]; rfl
    | next => exact False.elim (correct.2.1 rfl)
    | hit id => exact False.elim (correct.2.1 rfl)
  | succ remaining ih =>
    obtain ⟨bits, result, inspected, read, correct⟩ := Candidate.inspect_verified state capacity bucket (slot capacity hash distance)
      (remaining + 1) (fingerprint hash) query source table binding (slot_bound power) queryRead bounded
    cases result with
    | stop =>
      have free : Metadata.isFree bits = true := correct.resolve_right (by omega)
      have observed : Metadata.observe state bucket (slot capacity hash distance) = .ok (true, false) := by
        simp [Metadata.observe_read_byte, read, Except.map, free, (free_unused bits free).2]
      refine ⟨.miss (slot capacity hash distance) first, ?_, distance, by omega, rfl, passed, remembered, Or.inl observed⟩
      rw [loop, inspected]; rfl
    | hit id =>
      obtain ⟨entry, found, _, view⟩ := correct.2.2.2.2
      have used : Table.Used state bucket (slot capacity hash distance) := by
        simp [Table.Used, Metadata.observe_read_byte, read, Except.map, correct.1, correct.2.2.1]
      refine ⟨.hit (slot capacity hash distance), ?_, slot_bound power, used, entry, found, view⟩
      rw [loop, inspected]; rfl
    | next =>
      have nextPassed := passed.succ budget read correct
      have nextRemembered := remembered.succ power read
      obtain ⟨outcome, ran, completed⟩ := ih (distance + 1)
        (remember capacity (slot capacity hash distance) first (fingerprint hash) bits) (by omega) nextPassed nextRemembered
      refine ⟨outcome, ?_, completed⟩
      rw [loop, inspected]
      simpa only [bind, Except.bind, Candidate.Result.action, slot_next power] using ran

theorem run_verified (state : State) (capacity : BitVec 32) (bucket : Nat) (hash : BitVec 64)
    (query : Key) (source : View) (table : OwnedKeys.Table)
    (binding : Table.Binding place safety receiver bucket capacity state table) (power : Power capacity)
    (queryRead : Represents state source query.arguments) (bounded : source.length * 4 < addressLimit) :
    ∃ outcome, run state capacity bucket hash query source = .ok outcome ∧
      Completed state capacity bucket hash query table outcome := by
  simpa only [run, slot_zero power] using loop_verified state capacity bucket hash query source table binding power
    queryRead bounded capacity.toNat 0 capacity.toNat (by omega) passed_zero remembered_zero

end Compiler.Extraction.ExpressionMap.Probe
