/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapArgumentEquality
import Compiler.Extraction.ExpressionMapTableEntry
import Compiler.Extraction.CacheProofs

namespace Compiler.Extraction.ExpressionMap.KeyComparison
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray
open Compiler.Extraction.Cache (Key)
open Buckets

/-- Width-checked integer equality uses the existing scalar comparison
semantics. Equality of the captured c_int tag's bits is sign-independent. -/
def scalar (left right : Value) : Except Fault Bool :=
  match left, right with
  | .scalar (.int signed width a), .scalar (.int other size b) =>
    if signed = other ∧ width = size then .ok (Compiler.ZigAir.Scalar.Comparison.eq.eval a b)
    else .error .unsupported
  | _, _ => .error .unsupported

/-- The query is an existing by-value key and native slice descriptor. Stored
fields are selected through actual bucket headers; argument equality consumes
the stored descriptor and native words, never a supplied logical key result. -/
def field (state : State) (capacity : BitVec 32) (bucket index : Nat) (query : Key) (source : View) (slot : Cache.Field) :
    Except Fault Bool := do
  let stored ← KeyFields.read capacity bucket index slot state
  match slot with
  | .arguments =>
    let .slice (.slice false (.scalar (.int false 32))) address length := stored | .error .unsupported
    if address.offset % 4 ≠ 0 then .error .memoryValidity else
    ArgumentScan.run state source ⟨address.allocation, address.offset / 4, length⟩
  | _ => scalar (KeyFields.value query (source.address 0) slot) stored

def fields (state : State) (capacity : BitVec 32) (bucket index : Nat) (query : Key) (source : View) : List Cache.Field → Except Fault Bool
  | [] => .ok true
  | slot :: rest => do
    let equal ← field state capacity bucket index query source slot
    if equal then fields state capacity bucket index query source rest else .ok false

def run (state : State) (capacity : BitVec 32) (bucket index : Nat) (query : Key) (source : View) : Except Fault Bool :=
  fields state capacity bucket index query source Compiler.Extraction.Cache.equalityFields

theorem entry_byte_bound (state : State) (capacity : BitVec 32) (bucket index : Nat) (key : Key) (entry : OwnedKeys.Entry)
    (valid : state.valid = true) (view : Table.EntryView capacity bucket index state key entry) :
    key.arguments.length * 4 < addressLimit := by
  by_cases empty : key.arguments = []
  · simp [empty, addressLimit]
  · obtain ⟨cell, found, typed, writable, _⟩ := view.owned empty
    exact ArgumentScan.byte_length_bound state ⟨entry.address, 0, key.arguments.length⟩ valid
      ⟨key.arguments.length, cell, found, typed, writable, by simp⟩

theorem field_verified (state : State) (capacity : BitVec 32) (bucket index : Nat) (query stored : Key)
    (source : View) (entry : OwnedKeys.Entry) (slot : Cache.Field)
    (queryRead : Represents state source query.arguments) (view : Table.EntryView capacity bucket index state stored entry)
    (bounded : source.length * 4 < addressLimit ∧ stored.arguments.length * 4 < addressLimit) :
    field state capacity bucket index query source slot = .ok (slot.equal query stored) := by
  cases slot with
  | arguments =>
    have equal := ArgumentScan.run_verified state source (Memory.Arguments.view (OwnedKeys.slice stored entry))
      query.arguments stored.arguments queryRead view.contents bounded
    simpa only [field, view.stored.keys .arguments, KeyFields.value, bind, Except.bind, Nat.zero_mod,
      ne_self_iff_false, if_false, Nat.zero_div, Memory.Arguments.view, OwnedKeys.slice, Cache.Field.equal, Bool.beq_eq_decide_eq] using equal
  | kind | instruction | data | sequence =>
    simp [field, view.stored.keys, KeyFields.value, bind, Except.bind, scalar, Compiler.ZigAir.Scalar.Comparison.eval, Cache.Field.equal, Int.natCast_inj, BitVec.toNat_inj, Bool.beq_eq_decide_eq]

/-- Preserve the source's left-to-right short circuit. The source-bound field
inventory supplies the complete equality test; the list theorem is reused. -/
theorem fields_verified (state : State) (capacity : BitVec 32) (bucket index : Nat) (query stored : Key)
    (source : View) (entry : OwnedKeys.Entry) (slots : List Cache.Field)
    (queryRead : Represents state source query.arguments) (view : Table.EntryView capacity bucket index state stored entry)
    (bounded : source.length * 4 < addressLimit ∧ stored.arguments.length * 4 < addressLimit) :
    fields state capacity bucket index query source slots = .ok (Compiler.Extraction.Cache.equal slots query stored) := by
  induction slots with
  | nil => rfl
  | cons slot rest ih =>
    rw [fields, field_verified state capacity bucket index query stored source entry slot queryRead view bounded]
    simp only [bind, Except.bind, Compiler.Extraction.Cache.equal, List.all_cons]
    cases slot.equal query stored <;> simp_all [Compiler.Extraction.Cache.equal]

theorem run_verified (state : State) (capacity : BitVec 32) (bucket index : Nat) (query stored : Key)
    (source : View) (entry : OwnedKeys.Entry)
    (queryRead : Represents state source query.arguments) (view : Table.EntryView capacity bucket index state stored entry)
    (bounded : source.length * 4 < addressLimit ∧ stored.arguments.length * 4 < addressLimit) :
    run state capacity bucket index query source = .ok (decide (query = stored)) := by
  have equal : Compiler.Extraction.Cache.equal Compiler.Extraction.Cache.equalityFields query stored = decide (query = stored) := by
    apply Bool.eq_iff_iff.mpr
    simpa using Compiler.Extraction.Cache.equality_iff query stored
  exact (fields_verified state capacity bucket index query stored source entry _ queryRead view bounded).trans (congrArg Except.ok equal)

end Compiler.Extraction.ExpressionMap.KeyComparison
