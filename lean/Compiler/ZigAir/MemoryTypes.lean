/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryValueDefinitions

namespace Compiler.ZigAir.Memory

def usize : Ty := .scalar (.int false 64)

def Field.type : Field → Ty
  | .scalar type => .scalar type
  | .pointer writable identity layout => .pointer writable false (.record identity layout)
  | .slice writable child => .slice writable (.scalar child)
  | .recordSlice writable identity layout => .slice writable (.record identity layout)
  | .object child => child

/-- This finite layout vocabulary is checked against the captured target/layout.
It is not a rule for computing ABI layouts on arbitrary targets. -/
@[simp] def Ty.leafLayout : Ty → Option Layout
  | .scalar .unit => some ⟨0, 1⟩
  | .scalar .bool => some ⟨1, 1⟩
  -- Captured exhaustive two-state SafetyLock tag, not an arbitrary enum ABI.
  | .scalar (.int false 1) => some ⟨1, 1⟩
  | .scalar (.int _ 8) => some ⟨1, 1⟩
  | .scalar (.int _ 16) => some ⟨2, 2⟩
  | .scalar (.int _ 32) => some ⟨4, 4⟩
  | .scalar (.int _ 64) => some ⟨8, 8⟩
  | .scalar (.int false 256) => some ⟨32, 16⟩
  -- Captured ?Instruction, ?usize, ?i64 and ?u256; no general optional ABI rule.
  | .optionalScalar (.int false 8) => some ⟨2, 1⟩
  | .optionalScalar (.int false 64) => some ⟨16, 8⟩
  | .optionalScalar (.int true 64) => some ⟨16, 8⟩
  | .optionalScalar (.int false 256) => some ⟨48, 16⟩
  | .scalar _ => none
  | .pointer .. => some ⟨8, 8⟩
  | .slice .. => some ⟨16, 8⟩
  | _ => none

/-- Check every captured subobject layout before accepting the owner. This local
layout table is derived once from immutable type metadata and retains all fields;
it neither stores values nor supplies missing initialization. -/
def checkFields (layout : Layout) (fields : List (Nat × Option Layout)) : Bool :=
  decide (0 < layout.bytes ∧ 0 < layout.alignment) &&
  fields.all (fun (offset, field) => match field with
    | none => false
    | some child => decide (0 < child.bytes ∧ offset + child.bytes ≤ layout.bytes ∧
        offset % child.alignment = 0 ∧ layout.alignment % child.alignment = 0)) &&
  decide (fields.Pairwise fun a b => a.1 + (a.2.getD ⟨0, 1⟩).bytes ≤ b.1)

/-- Validate captured optional geometry without assigning payload byte offsets.
The exporter must still bind both layouts to the native target. -/
def optionalLayout (child : Option Layout) (layout : Layout) : Option Layout := do
  let payload ← child
  if 0 < layout.bytes ∧ 0 < layout.alignment ∧ payload.bytes ≤ layout.bytes ∧
      layout.bytes % layout.alignment = 0 ∧ layout.alignment % payload.alignment = 0 then some layout else none

mutual
def Ty.layout : Ty → Option Layout
  | .array n child => do
    let layout ← child.layout
    some ⟨n * layout.bytes, layout.alignment⟩
  | .record _ layout => if 0 < layout.alignment then some layout else none
  | .aggregate _ layout fields => if checkFields layout (Field.layouts fields) then some layout else none
  | .optionalObject child layout => match child with
    | .slice .. | .aggregate .. => optionalLayout child.layout layout
    -- Captured nullable, non-allowzero pointer: null occupies the pointer word.
    -- No discriminator/payload byte projection is supplied by this atomic view.
    | .pointer .. => if layout = ⟨8, 8⟩ then some layout else none
    | _ => none
  | type => type.leafLayout
termination_by structural type => type

def Field.layout : Field → Option Layout
  | .object child => child.layout
  | field => field.type.leafLayout
termination_by structural field => field

def Field.layouts : List (Nat × Field) → List (Nat × Option Layout)
  | [] => []
  | (offset, field) :: tail => (offset, field.layout) :: Field.layouts tail
termination_by structural fields => fields
end

def Ty.aggregateValid (layout : Layout) (fields : List (Nat × Field)) : Bool :=
  checkFields layout (Field.layouts fields)

theorem Field.layouts_eq_map (fields : List (Nat × Field)) :
    Field.layouts fields = fields.map (fun entry => (entry.1, entry.2.layout)) := by
  induction fields with
  | nil => rfl
  | cons entry tail ih => cases entry; simp [Field.layouts, ih]


theorem Field.layout_eq_type (field : Field) : field.layout = field.type.layout := by
  cases field <;> rfl


/-- One byte-interval predicate for both field identity evidence and recursive
projection. Bounds are relative to the same complete declared parent. -/
def Field.contains (field : Field) (base offset : Nat) : Bool := match field.layout with
  | none => false
  | some layout => decide (base ≤ offset ∧ offset < base + layout.bytes)

def Ty.fieldAt (layout : Layout) (fields : List (Nat × Field)) (offset : Nat) : Option (Nat × Ty) :=
  if !Ty.aggregateValid layout fields then none else
  (fields.find? fun (base, field) => field.contains base offset).map (fun (base, field) => (base, field.type))

def Value.type : Value → Ty
  | .scalar value => .scalar value.type
  | .optionalScalar child _ => .optionalScalar child
  | .pointer ty _ | .slice ty _ _ => ty
  | .optionalObject child layout _ => .optionalObject child layout

mutual
def Value.valid : Value → Bool
  | .scalar value => value.valid
  | .optionalScalar child payload => match payload with
    | none => true
    | some value => decide (value.type = child) && value.valid
  | .pointer (.pointer ..) _ => true
  | .slice (.slice ..) _ length => decide (length < addressLimit)
  | .optionalObject child _ payload => match payload with
    | none => true
    | some value => value.hasType child
  | _ => false
termination_by structural value => value

def ObjectValue.hasType : ObjectValue → Ty → Bool
  | .leaf value, type => decide (value.type = type) && value.valid
  | .fields values, .aggregate _ layout fields =>
    Ty.aggregateValid layout fields && objectFieldsTyped values fields
  | _, _ => false
termination_by structural value => value

def objectFieldsTyped : List (Nat × ObjectValue) → List (Nat × Field) → Bool
  | [], [] => true
  | (offset, value) :: values, (base, field) :: fields =>
    decide (offset = base) && value.hasType field.type && objectFieldsTyped values fields
  | _, _ => false
termination_by structural values => values
end

def Value.hasType (value : Value) (ty : Ty) : Bool := decide (value.type = ty) && value.valid

inductive Fault where
  | malformed | unsupported | unallocated | uninitialized | memoryValidity
  | readOnly | outOfMemory | sourceBounds
  | scalar (fault : Scalar.Fault)
  deriving DecidableEq, Repr

@[simp] def sliceFieldType (type : Ty) (offset : Nat) : Option Ty :=
  match type with
  | .slice writable child =>
    if offset = 0 then some (.pointer writable true child)
    else if offset = 8 then some usize else none
  | _ => none

/-- Select only from declared subobjects. A query can ask for an exact complete
view, a storable leaf or the first field at an offset; the same checked walk
serves all three, preserving array bounds and rejecting malformed child layouts.
The walk follows the immutable type tree, never addresses or stored pointers. -/
@[simp] private def atomicProjection (type : Ty) (offset : Nat) (select : Ty → Bool) (self : Bool) : Option Ty :=
  if self && decide (offset = 0) && select type then some type else do
    let field ← sliceFieldType type offset
    if select field then some field else none

mutual
@[simp] def Ty.project (select : Ty → Bool) (type : Ty) (offset : Nat) (self : Bool := true) : Option Ty :=
  if self && decide (offset = 0) && select type then some type else
  match type with
  | .array length child => do
    let layout ← child.layout
    if 0 < layout.bytes ∧ offset / layout.bytes < length then
      Ty.project select child (offset % layout.bytes) true
    else none
  | .aggregate _ layout fields =>
    if Ty.aggregateValid layout fields then Field.projectFields select fields offset else none
  | _ => atomicProjection type offset select false
termination_by structural type

@[simp] def Field.project (select : Ty → Bool) (field : Field) (offset : Nat) : Option Ty :=
  match field with
  | .object child => Ty.project select child offset true
  | field => atomicProjection field.type offset select true
termination_by structural field

@[simp] def Field.projectFields (select : Ty → Bool) (fields : List (Nat × Field)) (offset : Nat) : Option Ty :=
  match fields with
  | [] => none
  | (base, field) :: tail => if field.contains base offset then
      Field.project select field (offset - base)
    else Field.projectFields select tail offset
termination_by structural fields
end

@[simp] theorem Ty.project_root (select : Ty → Bool) (type : Ty) (selected : select type = true) :
    Ty.project select type 0 true = some type := by
  cases type <;> simp [Ty.project, selected]

/-- Root fields are selected before initialization; this supplies no payload.
Scalar roots have no fields; slice roots retain their two captured components. -/
def fieldType (type : Ty) (offset : Nat) : Option Ty :=
  match type with
  | .aggregate .. => Ty.project (fun _ => true) type offset false
  | _ => sliceFieldType type offset

end Compiler.ZigAir.Memory
