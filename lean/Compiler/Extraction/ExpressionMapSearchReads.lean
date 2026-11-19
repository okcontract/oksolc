/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapProbeMemory

namespace Compiler.Extraction.ExpressionMap.Search
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray Initialization Buckets

/-- getIndex checks the actual count before hashing or touching metadata. -/
def readCount (place : Placement) (safety : Bool) (state : State) (receiver : Nat) : Except Fault (BitVec 32) := do
  let .scalar (.int false 32 count) ← Capacity.readField place safety state receiver .size | .error .unsupported
  .ok (BitVec.ofInt 32 count)

/-- The private bucket view admits precisely the captured metadata offset.
Null unwrap and malformed views remain explicit failures. -/
def readBucket (place : Placement) (safety : Bool) (state : State) (receiver : Nat) : Except Fault Nat := do
  let .optionalObject _ _ payload ← Capacity.readField place safety state receiver .metadata | .error .unsupported
  match payload with
  | none => .error (Capacity.rejected safety)
  | some (.leaf (.pointer target address)) =>
    if target ≠ metadataPointerType ∨ address.offset ≠ 24 then .error .unsupported
    else .ok address.allocation
  | _ => .error .unsupported

/-- Shared by the literal lookup and insertion loops; each native advance
reloads self.metadata before inspecting the next slot. -/
def inspect (place : Placement) (safety : Bool) (state : State) (receiver : Nat)
    (capacity : BitVec 32) (index remaining : Nat) (fp : BitVec 7) (key : Cache.Key) (source : View) :
    Except Fault (BitVec 8 × Candidate.Action) := do
  let bucket ← readBucket place safety state receiver
  Candidate.inspect state capacity bucket index remaining fp key source

/-- The source reads capacity in the else-if, before checking the tombstone.
A used matching fingerprint skips that read even when key equality was false. -/
def remember (place : Placement) (safety : Bool) (state : State) (receiver index first : Nat)
    (fp : BitVec 7) (bits : BitVec 8) : Except Fault Nat := do
  if Metadata.isUsed bits && bits.toNat % 128 == fp.toNat then return first
  let capacity ← Capacity.readCapacity place safety state receiver
  .ok (if first == capacity.toNat && bits == 1 then index else first)

theorem remember_eq (read : Capacity.readCapacity place safety state receiver = .ok capacity) :
    remember place safety state receiver index first fp bits = .ok (Probe.remember capacity index first fp bits) := by
  simp only [remember, Probe.remember]
  split <;> simp_all [bind, Except.bind, pure, Except.pure]

end Compiler.Extraction.ExpressionMap.Search

namespace Compiler.Extraction.ExpressionMap.Insertion
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray Initialization Buckets

theorem Layout.read_field (layout : Layout place safety receiver bucket capacity state)
    (slot : Slot) (ordinary : slot ≠ .lock) :
    Capacity.readField place safety state receiver slot = load state (Counter.field place safety receiver slot) := by
  obtain ⟨cell, found, typed, _⟩ := layout.receiverLive
  exact Counter.read_eq place safety state receiver slot cell layout.valid found typed ordinary

theorem Layout.read_bucket (layout : Layout place safety receiver bucket capacity state) :
    Search.readBucket place safety state receiver = .ok bucket := by
  simp [Search.readBucket, layout.read_field .metadata (by decide), layout.metadata, Receiver.value, bind, Except.bind]

theorem Layout.read_capacity (layout : Layout place safety receiver bucket capacity state) (positive : 0 < capacity.toNat) :
    Capacity.readCapacity place safety state receiver = .ok capacity := by
  obtain ⟨cell, found, typed, _⟩ := layout.bucketLive
  simp only [Capacity.readCapacity, layout.read_field .metadata (by decide), layout.metadata, Receiver.value,
    bind, Except.bind, ne_self_iff_false, ↓reduceIte,
    Metadata.read_capacity state bucket cell capacity positive layout.valid found typed (layout.headers .capacity),
    BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end Compiler.Extraction.ExpressionMap.Insertion

namespace Compiler.Extraction.ExpressionMap.Table
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray

theorem Binding.read_count (binding : Binding place safety receiver bucket capacity state table) :
    Search.readCount place safety state receiver = .ok (BitVec.ofNat 32 (count capacity bucket state)) := by
  simp only [Search.readCount, binding.layout.read_field .size (by decide), binding.size, number,
    bind, Except.bind, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem Binding.empty_of_count_zero (binding : Binding place safety receiver bucket capacity state table)
    (zero : count capacity bucket state = 0) (query : Cache.Key) : table query = none := by
  cases found : table query with
  | none => rfl
  | some entry =>
    obtain ⟨index, inside, used, _⟩ := binding.entries query entry found
    have missing := List.countP_eq_zero.mp zero index (List.mem_range.mpr inside)
    exact False.elim (missing ((occupied_iff state bucket index).mpr used))

end Compiler.Extraction.ExpressionMap.Table
