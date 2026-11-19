/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapMetadataFill
import Compiler.Extraction.ExpressionMapReceiver

namespace Compiler.Extraction.ExpressionMap.Buckets.Metadata
open Compiler.ZigAir.Memory

def isUsed (bits : BitVec 8) : Bool := bits.toNat / 128 == 1
def isFree (bits : BitVec 8) : Bool := bits == 0

theorem zero_free_unused : isFree 0 = true ∧ isUsed 0 = false := by decide

def observe (state : State) (id index : Nat) : Except Fault (Bool × Bool) := do
  let .scalar (.int false 8 bits) ← load state (pointer id index) | .error .unsupported
  .ok (isFree (BitVec.ofInt 8 bits), isUsed (BitVec.ofInt 8 bits))

theorem Filled.free_unused {id count : Nat} {capacity : BitVec 32} {before after : State}
    (post : Filled id 0 count capacity before after) (index : Nat) (inside : index < count) :
    observe after id index = .ok (true, false) := by
  simp only [observe, post.reads index (by omega) (by omega), zero, bind, Except.bind]
  exact show (Except.ok (isFree 0, isUsed 0) : Except Fault (Bool × Bool)) = .ok (true, false) from by
    rw [zero_free_unused.1, zero_free_unused.2]

/-- The nonnull branch of capacity(): checked Header view and actual u32 load.
The native pointer subtraction is admitted only at the known bucket offset. -/
def readCapacity (state : State) (address : Address) : Except Fault Value := do
  if address.offset ≠ 24 then .error .unsupported else do
  let field ← fieldPointer state (.pointer (.pointer true false headerType) ⟨address.allocation, address.offset - 24⟩) 16
  load state field

/-- This precise packed view retains its declared array extent. It grants no
byte access to unrelated records, pointer storage, keys or padding. -/
def byteArray (state : State) (capacity : Nat) (address : Address) : Except Fault Value := do
  let .pointer _ selected ← Header.arrayPointer state metadataType capacity address | .error .unsupported
  .ok (.pointer (.pointer true true byte) selected)

/-- Read the actual metadata pointer and header capacity before constructing the
memset slice. Null/malformed views are verification rejections, not defaults. -/
def prepare (safety : Bool) (receiver : Address) (state : State) : Except Fault (Nat × Nat) := do
  let value ← Receiver.read safety state receiver
  let .optionalObject _ _ (some (.leaf (.pointer target address))) := value | .error .unsupported
  if target ≠ metadataPointerType then .error .unsupported else do
  let .scalar (.int false 32 count) ← readCapacity state address | .error .unsupported
  let .pointer _ selected ← byteArray state count.toNat address | .error .unsupported
  .ok (selected.allocation, count.toNat)

def clear (safety : Bool) (receiver : Address) (before : State) : Except Fault Unit × State :=
  match prepare safety receiver before with
  | .error fault => (.error fault, before)
  | .ok (id, count) => fill id count 0 before

theorem read_capacity (state : State) (id : Nat) (cell : Allocation) (capacity : BitVec 32)
    (positive : 0 < capacity.toNat) (valid : state.valid = true)
    (found : state.heap.lookup id = some cell) (typed : cell.type = storageType capacity.toNat)
    (read : load state (Header.Slot.capacity.pointer capacity id) = .ok (Header.Slot.capacity.value capacity id)) :
    readCapacity state ⟨id, 24⟩ = .ok (.scalar (.int false 32 capacity.toNat)) := by
  have geometry := Buckets.geometry capacity.toNat capacity.isLt
  have root := root_access state id cell ⟨bytes capacity.toNat, 16⟩ false valid found
    (typed ▸ storage_layout capacity.toNat positive) geometry.2.2.2.2.2.2.1 (by simp)
  have accessed := access_subregion state ⟨id, 0⟩ ⟨bytes capacity.toNat, 16⟩ ⟨24, 8⟩ 0 false cell root
    (by decide) (by dsimp; omega) (by decide) (by change 16 % 8 = 0; decide)
  have view : acceptsView cell.type 0 headerType = true := by
    rw [typed]
    have checked := storage_valid capacity.toNat positive
    simp [storageType, acceptsView, checked, headerType]
    simp [storageFields, Field.contains, Field.layout, headerType, Ty.layout,
      checkFields, Field.layouts, Field.type]
  have selected := fieldPointer_of_access state ⟨id, 0⟩ cell headerType (.scalar (.int false 32)) ⟨24, 8⟩ 16 true false
    header_layout (by simpa using accessed) view (by decide)
  simp only [readCapacity, ne_self_iff_false, ↓reduceIte, Nat.sub_self, selected, bind, Except.bind]
  exact read

theorem byte_array (state : State) (id : Nat) (cell : Allocation) (capacity : BitVec 32)
    (positive : 0 < capacity.toNat) (valid : state.valid = true)
    (found : state.heap.lookup id = some cell) (typed : cell.type = storageType capacity.toNat)
    (writable : cell.writable = true) :
    byteArray state capacity.toNat ⟨id, 24⟩ = .ok (.pointer (.pointer true true byte) ⟨id, 24⟩) := by
  have geometry := Buckets.geometry capacity.toNat capacity.isLt
  have root := root_access state id cell ⟨bytes capacity.toNat, 16⟩ true valid found
    (typed ▸ storage_layout capacity.toNat positive) geometry.2.2.2.2.2.2.1 (fun _ => writable)
  have accessed := access_subregion state ⟨id, 0⟩ ⟨bytes capacity.toNat, 16⟩ ⟨capacity.toNat, 1⟩ 24 true cell root
    positive (by dsimp; omega) (by change 24 % 1 = 0; decide) (by change 16 % 1 = 0; decide)
  have layout : (Ty.array capacity.toNat metadataType).layout = some ⟨capacity.toNat, 1⟩ := by
    simp [Ty.layout, metadata_layout]
  simp only [Nat.zero_add] at accessed
  simp only [byteArray, Header.arrayPointer, layout, accessed, bind, Except.bind, typed,
    Receiver.metadata_view capacity.toNat positive, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

theorem prepare_verified (safety : Bool) (receiver : Address) (before : State) (id : Nat) (cell : Allocation)
    (capacity : BitVec 32) (positive : 0 < capacity.toNat) (valid : before.valid = true)
    (found : before.heap.lookup id = some cell) (typed : cell.type = storageType capacity.toNat)
    (writable : cell.writable = true)
    (metadata : Receiver.read safety before receiver = .ok (Receiver.value id))
    (header : load before (Header.Slot.capacity.pointer capacity id) = .ok (Header.Slot.capacity.value capacity id)) :
    prepare safety receiver before = .ok (id, capacity.toNat) := by
  simp only [prepare, metadata, Receiver.value, bind, Except.bind, ne_self_iff_false, ↓reduceIte,
    read_capacity before id cell capacity positive valid found typed header, Int.toNat_natCast,
    byte_array before id cell capacity positive valid found typed writable]

theorem clear_verified (safety : Bool) (receiver : Address) (before : State) (id : Nat) (cell : Allocation)
    (capacity : BitVec 32) (positive : 0 < capacity.toNat) (valid : before.valid = true)
    (found : before.heap.lookup id = some cell) (typed : cell.type = storageType capacity.toNat)
    (writable : cell.writable = true)
    (metadata : Receiver.read safety before receiver = .ok (Receiver.value id))
    (header : load before (Header.Slot.capacity.pointer capacity id) = .ok (Header.Slot.capacity.value capacity id)) :
    ∃ after, clear safety receiver before = (.ok (), after) ∧ Filled id 0 capacity.toNat capacity before after := by
  obtain ⟨after, ran, post⟩ := fill_verified id 0 capacity.toNat capacity before cell (by omega) valid found typed writable
  exact ⟨after, by simp only [clear, prepare_verified safety receiver before id cell capacity positive valid found typed writable metadata header]; exact ran, post⟩

end Compiler.Extraction.ExpressionMap.Buckets.Metadata
