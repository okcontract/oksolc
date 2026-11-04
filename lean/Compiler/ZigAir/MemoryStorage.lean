/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryTypes

/-! Sparse typed leaves are the sole storage representation. Missing leaves are
uninitialized; no default byte/value is manufactured. Array allocation requires
no traversal of its extent. Whole-array values, zero-stride element addressing
and representation-punning remain explicit unsupported cases. -/
namespace Compiler.ZigAir.Memory

/-- Resolve a typed subobject, retaining every array's declared extent. -/
def acceptsView (owner : Ty) (offset : Nat) (wanted : Ty) : Bool :=
  (Ty.project (fun type => decide (type = wanted)) owner offset).isSome

/-- A leaf is a scalar, atomic optional or pointer; a slice occupies two independently initialized
leaves. Recursion follows the declared type, not a fabricated pointer view. -/
def leafType (owner : Ty) (offset : Nat) : Option Ty :=
  Ty.project (fun type => match type with | .scalar _ | .optionalScalar _ | .optionalObject .. | .pointer .. => true | _ => false) owner offset

@[simp] theorem acceptsView_array (length : Nat) (child wanted : Ty) (offset : Nat) :
    acceptsView (.array length child) offset wanted =
      (decide (offset = 0 ∧ .array length child = wanted) || match child.layout with
        | none => false
        | some layout => decide (0 < layout.bytes ∧ offset / layout.bytes < length) &&
            acceptsView child (offset % layout.bytes) wanted) := by
  by_cases root : offset = 0 ∧ Ty.array length child = wanted
  · simp [acceptsView, Ty.project, root.1, root.2]
  · cases shaped : child.layout with
    | none => simp [acceptsView, Ty.project, root, shaped]
    | some layout =>
      by_cases inside : 0 < layout.bytes ∧ offset / layout.bytes < length <;>
        simp [acceptsView, Ty.project, root, shaped, inside]

@[simp] theorem leafType_array (length : Nat) (child : Ty) (offset : Nat) :
    leafType (.array length child) offset = (do
      let layout ← child.layout
      if 0 < layout.bytes ∧ offset / layout.bytes < length then
        leafType child (offset % layout.bytes) else none) := by
  simp [leafType, Ty.project]

@[simp] theorem acceptsView_self (owner : Ty) : acceptsView owner 0 owner = true := by
  cases owner <;> simp [acceptsView, Ty.project]

abbrev Cells := List (Nat × Value)

def Cells.lookup (cells : Cells) (offset : Nat) : Option Value :=
  (cells.find? (fun entry => entry.1 == offset)).map Prod.snd

def Cells.set (cells : Cells) (offset : Nat) (value : Value) : Cells :=
  (offset, value) :: cells.filter (fun entry => entry.1 != offset)

def leafFits (owner : Ty) (entry : Nat × Value) : Bool :=
  decide (leafType owner entry.1 = some entry.2.type) && entry.2.valid

def Cells.valid (cells : Cells) (owner : Ty) : Bool :=
  cells.all (leafFits owner) && decide (cells.Pairwise (fun a b => a.1 ≠ b.1))

/-- Decompose a value into the same leaves used by field and element accesses.
This only describes storage; callers must check the value and declared view. -/
def Value.leaves (value : Value) (offset : Nat := 0) : Cells :=
  match value with
  | .slice (.slice writable child) address length =>
    [(offset, .pointer (.pointer writable true child) address),
      (offset + 8, .scalar (.int false 64 length))]
  | _ => [(offset, value)]

def Cells.readLeaf (cells : Cells) (owner : Ty) (offset : Nat) (wanted : Ty) : Except Fault Value := do
  if leafType owner offset ≠ some wanted then .error .unsupported else
  let some value := cells.lookup offset | .error .uninitialized
  if value.hasType wanted then .ok value else .error .malformed

def Cells.read (cells : Cells) (owner : Ty) (offset : Nat) (wanted : Ty) : Except Fault Value := do
  if !acceptsView owner offset wanted then .error .unsupported else
  match wanted with
  | .array .. | .record .. | .aggregate .. => .error .unsupported
  | .slice writable child =>
    let .pointer _ address ← cells.readLeaf owner offset (.pointer writable true child) | .error .malformed
    let .scalar (.int false 64 length) ← cells.readLeaf owner (offset + 8) usize | .error .malformed
    .ok (.slice wanted address length.toNat)
  | _ => cells.readLeaf owner offset wanted

def Cells.write (cells : Cells) (owner : Ty) (offset : Nat) (value : Value) : Except Fault Cells := do
  if !value.valid then .error .malformed else
  if !acceptsView owner offset value.type then .error .unsupported else
  let leaves := value.leaves offset
  if !leaves.all (leafFits owner) then .error .unsupported else
  .ok (leaves.foldl (fun cells entry => cells.set entry.1 entry.2) cells)

end Compiler.ZigAir.Memory
