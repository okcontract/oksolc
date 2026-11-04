/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryRecordWrites

namespace Compiler.ZigAir.Memory.ScalarBytes

/-- Locate an interior byte of a declared integer leaf. The existing checked
field geometry and array bounds exclude padding, pointer representations and
unrelated storage. This computes an address, not a second value representation. -/
private def atom (type : Ty) (offset : Nat) : Option (Nat × Bool × Nat) := do
  let .scalar (.int signed bits) := type | none
  let shape ← type.layout
  if 0 < bits ∧ bits % 8 = 0 ∧ shape.bytes = bits / 8 ∧ offset < shape.bytes then
    some (0, signed, bits)
  else none

mutual
def locate (type : Ty) (offset : Nat) : Option (Nat × Bool × Nat) :=
  match type with
  | .array length child => do
    let shape ← child.layout
    if 0 < shape.bytes ∧ offset / shape.bytes < length then do
      let (base, scalar) ← locate child (offset % shape.bytes)
      some (offset / shape.bytes * shape.bytes + base, scalar)
    else none
  | .aggregate _ shape fields =>
    if Ty.aggregateValid shape fields then locateFields fields offset else none
  | type => atom type offset
termination_by structural type

def locateField (field : Field) (offset : Nat) : Option (Nat × Bool × Nat) :=
  match field with
  | .object child => locate child offset
  | field => atom field.type offset
termination_by structural field

def locateFields (fields : List (Nat × Field)) (offset : Nat) : Option (Nat × Bool × Nat) :=
  match fields with
  | [] => none
  | (base, field) :: rest =>
    if field.contains base offset then do
      let (inner, scalar) ← locateField field (offset - base)
      some (base + inner, scalar)
    else locateFields rest offset
termination_by structural fields
end

/-- Reinterpret only an admitted integer subobject. Casting does not initialize
or read it, strengthen alignment, or upgrade a read-only pointer. -/
def arrayCast (state : State) (writable : Bool) (alignment count : Nat) (source : Value) : Except Fault Value := do
  let .pointer (.pointer mutable _ child@(.scalar (.int _ bits))) address := source | .error .unsupported
  if writable && !mutable then .error .readOnly else
  let some shape := child.layout | .error .unsupported
  if ¬(0 < bits ∧ bits % 8 = 0 ∧ count = bits / 8 ∧ shape.bytes = count ∧
      0 < alignment ∧ shape.alignment % alignment = 0) then .error .unsupported else
  let cell ← access state address shape false
  if !acceptsView cell.type address.offset child then .error .unsupported else
  .ok (.pointer (.pointer writable false (.array count (.scalar (.int false 8)))) address)

/-- AIR's array-to-slice conversion retains the pointer and its static extent;
it neither loads storage nor creates an allocation. -/
def arrayToSlice (source : Value) : Except Fault Value := do
  let .pointer (.pointer writable false (.array count child)) address := source | .error .malformed
  let value := Value.slice (.slice writable child) address count
  if value.valid then .ok value else .error .malformed

/-- Read one little-endian representation byte through the original typed heap.
The ordinary load still checks lifetime, geometry and initialization. -/
def readAt (state : State) (address : Address) : Except Fault (BitVec 8) := do
  let cell ← access state address ⟨1, 1⟩ false
  let some (base, signed, bits) := locate cell.type address.offset | .error .unsupported
  let .scalar (.int _ _ value) ← load state
    (.pointer (.pointer false false (.scalar (.int signed bits))) { address with offset := base }) | .error .malformed
  .ok (BitVec.ofNat 8 ((BitVec.ofInt bits value).toNat / 256 ^ (address.offset - base)))

def read (state : State) (source : Value) (index : Nat) : Except Fault (BitVec 8) := do
  let .slice (.slice _ (.scalar (.int false 8))) address length := source | .error .unsupported
  if index ≥ length then .error .sourceBounds else
  readAt state { address with offset := address.offset + index }

def bytes (state : State) (source : Value) : Except Fault (List (BitVec 8)) := do
  let .slice (.slice _ (.scalar (.int false 8))) _ length := source | .error .unsupported
  (List.range length).mapM (read state source)

theorem locate_integer (signed : Bool) (bits offset : Nat) (shape : Layout)
    (shaped : (Ty.scalar (.int signed bits)).layout = some shape)
    (positive : 0 < bits) (whole : bits % 8 = 0) (size : shape.bytes = bits / 8)
    (inside : offset < shape.bytes) :
    locate (.scalar (.int signed bits)) offset = some (0, signed, bits) := by
  have bound : offset < bits / 8 := by omega
  simp [locate, atom, shaped, positive, whole, size, bound]

theorem locateField_integer (signed : Bool) (bits offset : Nat) (shape : Layout)
    (shaped : (Ty.scalar (.int signed bits)).layout = some shape)
    (positive : 0 < bits) (whole : bits % 8 = 0) (size : shape.bytes = bits / 8)
    (inside : offset < shape.bytes) :
    locateField (.scalar (.int signed bits)) offset = some (0, signed, bits) := by
  exact locate_integer signed bits offset shape shaped positive whole size inside

theorem arrayCast_const (state : State) (address : Address) (cell : Allocation)
    (signed mutable many : Bool) (bits alignment count : Nat) (shape : Layout)
    (shaped : (Ty.scalar (.int signed bits)).layout = some shape)
    (positive : 0 < bits) (whole : bits % 8 = 0) (counted : count = bits / 8)
    (size : shape.bytes = count) (aligned : 0 < alignment ∧ shape.alignment % alignment = 0)
    (accessed : access state address shape false = .ok cell)
    (viewed : acceptsView cell.type address.offset (.scalar (.int signed bits)) = true) :
    arrayCast state false alignment count (.pointer (.pointer mutable many (.scalar (.int signed bits))) address) =
      .ok (.pointer (.pointer false false (.array count (.scalar (.int false 8)))) address) := by
  simp [arrayCast, shaped, positive, whole, counted, size, aligned, accessed, viewed, bind, Except.bind]

/-- The enclosing owner/array proof derives the selected leaf and its ordinary
load. This lemma derives the interior-byte access from that leaf's geometry. -/
theorem readAt_of_load (state : State) (address : Address) (cell : Allocation)
    (signed : Bool) (bits index : Nat) (value : Int) (shape : Layout)
    (accessed : access state address shape false = .ok cell) (inside : index < shape.bytes)
    (selected : locate cell.type (address.offset + index) = some (address.offset, signed, bits))
    (loaded : load state (.pointer (.pointer false false (.scalar (.int signed bits))) address) =
      .ok (.scalar (.int signed bits value))) :
    readAt state ⟨address.allocation, address.offset + index⟩ =
      .ok (BitVec.ofNat 8 ((BitVec.ofInt bits value).toNat / 256 ^ index)) := by
  have accessedByte := access_subregion state address shape ⟨1, 1⟩ index false cell accessed
    (by decide) (by change index + 1 ≤ shape.bytes; omega) (Nat.mod_one _) (Nat.mod_one _)
  cases address
  simp only [readAt, accessedByte, selected, bind, Except.bind, loaded, Nat.add_sub_cancel_left]

theorem readAt_same_allocation (before after : State) (address : Address)
    (same : before.heap.lookup address.allocation = after.heap.lookup address.allocation) :
    readAt before address = readAt after address := by
  simp only [readAt, access, load, same]

end Compiler.ZigAir.Memory.ScalarBytes
