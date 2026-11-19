/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Contract.Evm.Storage

/-! Declaration-order layout for the admitted uint256/bool storage fragment.
Locations are derived from source field types, never compiler layout metadata.
A Boolean occupies one low-order-aligned byte; a word starts a fresh slot when
the preceding slot is partially occupied. Inheritance, custom layout, arrays
and mappings are outside this layout. -/
namespace Compiler.Validation.SolidityStorage
open Contract.Evm
open Contract.Interaction (Word)

inductive StorageType where
  | word | boolean
  deriving DecidableEq, Repr

structure Variable where
  name : String
  type : StorageType := .word
  deriving DecidableEq, Repr

abbrev Layout := List Variable

structure Location where
  slot : Nat := 0
  byte : Fin 32 := 0
  deriving DecidableEq, Repr

def Location.allocate (cursor : Location) : StorageType → Location × Location
  | .word =>
    let slot := cursor.slot + if cursor.byte = 0 then 0 else 1
    (⟨slot, 0⟩, ⟨slot + 1, 0⟩)
  | .boolean =>
    (cursor, if next : cursor.byte.val + 1 < 32 then
      ⟨cursor.slot, ⟨cursor.byte.val + 1, next⟩⟩ else ⟨cursor.slot + 1, 0⟩)

def Layout.locateFrom (cursor : Location) : Layout → Nat → Option (Variable × Location)
  | [], _ => none
  | field :: rest, index =>
    let (here, next) := cursor.allocate field.type
    match index with
    | 0 => some (field, here)
    | index + 1 => locateFrom next rest index

def Layout.locate (variables : Layout) (index : Nat) : Option (Variable × Location) :=
  variables.locateFrom {} index

def Layout.names (variables : Layout) : List String := variables.map Variable.name

def Layout.words (names : List String) : Layout := names.map fun name => ⟨name, .word⟩

namespace PackedBool

def mask (byte : Fin 32) : Word := (255 : Word) <<< (8 * byte.val)
def encode (value : Bool) : Word := if value then 1 else 0
def read (word : Word) (byte : Fin 32) : Bool := decide (word &&& mask byte ≠ 0)
def insert (word : Word) (byte : Fin 32) (value : Bool) : Word :=
  (word &&& ~~~mask byte) ||| (encode value <<< (8 * byte.val))

/-- A packed write retains every bit outside its own storage byte, including
unused upper bytes and neighboring fields with arbitrary existing contents. -/
theorem insert_preserves_other_bits (word : Word) (byte : Fin 32) (value : Bool) :
    insert word byte value &&& ~~~mask byte = word &&& ~~~mask byte := by
  have fits : (encode value <<< (8 * byte.val)) &&& mask byte =
      encode value <<< (8 * byte.val) := by
    rw [mask, ← BitVec.shiftLeft_and_distrib]
    cases value <;> rfl
  unfold insert
  have disjoint : (encode value <<< (8 * byte.val)) &&& ~~~mask byte = 0#256 := by
    rw [← fits, BitVec.and_assoc, BitVec.and_not_self]
    exact BitVec.and_zero
  rw [BitVec.and_or_distrib_right, BitVec.and_assoc, BitVec.and_self, disjoint]
  exact BitVec.or_zero

end PackedBool

def Variable.read (field : Variable) (location : Location) (cells : Stateful.Slots) : Word :=
  match field.type with
  | .word => cells (BitVec.ofNat 256 location.slot)
  | .boolean => PackedBool.encode (PackedBool.read (cells (BitVec.ofNat 256 location.slot)) location.byte)

def Layout.read (variables : Layout) (name : String) (cells : Stateful.Slots) : Word :=
  match variables.names.idxOf? name with
  | none => 0
  | some index => match variables.locate index with
    | none => 0
    | some (field, location) => field.read location cells

/-- Indices name declarations, not physical slots. Invalid indices have an
explicit failure result; admitted source assignments always name a declaration. -/
def Layout.write (variables : Layout) (index : Nat) (value : Word)
    (cells : Stateful.Slots) : Option Stateful.Slots :=
  match variables.locate index with
  | none => none
  | some (field, location) =>
    let key := BitVec.ofNat 256 location.slot
    let word := match field.type with
      | .word => value
      | .boolean => PackedBool.insert (cells key) location.byte (decide (value ≠ 0))
    some (Stateful.write cells key word)

end Compiler.Validation.SolidityStorage
