/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapKeyComparison
import Compiler.Extraction.ExpressionMapTable

namespace Compiler.Extraction.ExpressionMap.Candidate
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray
open Compiler.Extraction.Cache (Key)
open Buckets

inductive Result where
  | stop
  | next
  | hit (id : BitVec 32)
  deriving DecidableEq, BEq

inductive Action where
  | stop
  | next
  | hit
  deriving DecidableEq, BEq

/-- Shared read-only getIndex/getOrPut candidate. The latter returns pointers
on a hit and must not require the value read performed by getAdapted. -/
def inspect (state : State) (capacity : BitVec 32) (bucket index remaining : Nat)
    (fp : BitVec 7) (query : Key) (source : View) : Except Fault (BitVec 8 × Action) := do
  let bits ← Metadata.readByte state bucket index
  if Metadata.isFree bits || remaining == 0 then return (bits, .stop)
  if Metadata.isUsed bits && bits.toNat % 128 == fp.toNat then
    if ← KeyComparison.run state capacity bucket index query source then return (bits, .hit)
  return (bits, .next)

/-- One getIndex iteration and the getAdapted value read on a hit. The loop's
hash, starting index, remaining count and advancement are separate obligations.
A stopped or skipped candidate does not establish global key absence. -/
def run (state : State) (capacity : BitVec 32) (bucket index remaining : Nat)
    (fp : BitVec 7) (query : Key) (source : View) : Except Fault Result := do
  let (_, action) ← inspect state capacity bucket index remaining fp query source
  match action with
  | .stop => .ok .stop
  | .next => .ok .next
  | .hit =>
    let .scalar (.int false 32 id) ← Values.read state capacity bucket index | .error .unsupported
    return .hit (BitVec.ofInt 32 id)

/-- Exact local outcomes, with absence restricted to this candidate slot. -/
def Correct (state : State) (capacity : BitVec 32) (bucket index remaining : Nat)
    (fp : BitVec 7) (query : Key) (table : OwnedKeys.Table) (bits : BitVec 8) : Result → Prop
  | .stop => Metadata.isFree bits = true ∨ remaining = 0
  | .next => Metadata.isFree bits = false ∧ remaining ≠ 0 ∧
      (Metadata.isUsed bits = false ∨ bits.toNat % 128 ≠ fp.toNat ∨
        ∀ entry, ¬Table.EntryView capacity bucket index state query entry)
  | .hit id => Metadata.isFree bits = false ∧ remaining ≠ 0 ∧ Metadata.isUsed bits = true ∧
      bits.toNat % 128 = fp.toNat ∧ ∃ entry, table query = some entry ∧ entry.id = id ∧
        Table.EntryView capacity bucket index state query entry

def Result.action : Result → Action
  | .stop => .stop
  | .next => .next
  | .hit _ => .hit

theorem run_verified (state : State) (capacity : BitVec 32) (bucket index remaining : Nat)
    (fp : BitVec 7) (query : Key) (source : View) (table : OwnedKeys.Table)
    (binding : Table.Binding place safety receiver bucket capacity state table)
    (inside : index < capacity.toNat) (queryRead : Represents state source query.arguments)
    (bounded : source.length * 4 < addressLimit) :
    ∃ bits result, Metadata.readByte state bucket index = .ok bits ∧
      run state capacity bucket index remaining fp query source = .ok result ∧
      Correct state capacity bucket index remaining fp query table bits result := by
  obtain ⟨bits, read⟩ := binding.metadata index inside
  by_cases stop : Metadata.isFree bits = true ∨ remaining = 0
  · refine ⟨bits, .stop, read, ?_, stop⟩
    simp only [run, inspect, read, bind, Except.bind, pure, Except.pure]
    rcases stop with free | zero
    · simp [free]
    · simp [zero]
  · have free : Metadata.isFree bits = false := by cases h : Metadata.isFree bits <;> simp_all
    have left : remaining ≠ 0 := by omega
    by_cases used : Metadata.isUsed bits = true
    · by_cases fingerprint : bits.toNat % 128 = fp.toNat
      · have occupied : Table.Used state bucket index := by
          simp [Table.Used, Metadata.observe_read_byte, read, Except.map, free, used]
        obtain ⟨stored, entry, present, view⟩ := binding.slots index inside occupied
        have compared := KeyComparison.run_verified state capacity bucket index query stored source entry queryRead view
          ⟨bounded, KeyComparison.entry_byte_bound state capacity bucket index stored entry binding.layout.valid view⟩
        by_cases same : query = stored
        · subst stored
          refine ⟨bits, .hit entry.id, read, ?_, free, left, used, fingerprint, entry, present, rfl, view⟩
          simp [run, inspect, read, free, left, used, fingerprint, compared, view.stored.value, number, bind, Except.bind, pure, Except.pure]
        · refine ⟨bits, .next, read, ?_, free, left, Or.inr (Or.inr ?_)⟩
          · simp [run, inspect, read, free, left, used, fingerprint, compared, same, bind, Except.bind, pure, Except.pure]
          · intro other otherView; exact same (otherView.unique view).1
      · refine ⟨bits, .next, read, ?_, free, left, Or.inr (Or.inl fingerprint)⟩
        simp [run, inspect, read, free, left, used, fingerprint, bind, Except.bind, pure, Except.pure]
    · have unused : Metadata.isUsed bits = false := by cases h : Metadata.isUsed bits <;> simp_all
      refine ⟨bits, .next, read, ?_, free, left, Or.inl unused⟩
      simp [run, inspect, read, free, left, unused, bind, Except.bind, pure, Except.pure]

end Compiler.Extraction.ExpressionMap.Candidate
