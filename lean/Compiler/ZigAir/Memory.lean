/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryStorage

/-! Typed allocation/lifetime semantics for the initial 64-bit AIR memory client.
Unlike the expression-graph heap, these cells contain arbitrary admitted scalar,
pointer and slice values. Typed leaf storage tracks partial initialization and
aliases within slices and nested arrays. Whole-array values, byte punning,
packed/volatile/allowzero pointers,
foreign allocation and raw-address casts are not yet interpreted. Failed memory
obligations are verification failures, not claims about native behavior after UB.
Physical address injection and Zig backend preservation remain separate claims. -/
namespace Compiler.ZigAir.Memory

structure Allocation where
  base : Nat
  type : Ty
  cells : Cells := []
  writable : Bool := true
  stack : Bool := false
  deriving DecidableEq, Repr

abbrev Heap := List (Nat × Allocation)

structure State where
  heap : Heap := []
  nextId : Nat := 0
  nextAddress : Nat := 8
  deriving DecidableEq, Repr

def Heap.lookup (heap : Heap) (id : Nat) : Option Allocation :=
  (heap.find? (fun item => item.1 == id)).map Prod.snd

def Heap.replace (heap : Heap) (id : Nat) (value : Allocation) : Heap :=
  heap.map (fun item => if item.1 = id then (id, value) else item)

def separated (a b : Nat × Allocation) : Bool :=
  decide (a.1 ≠ b.1) && match a.2.type.layout, b.2.type.layout with
  | some x, some y => decide (a.2.base + x.bytes ≤ b.2.base ∨ b.2.base + y.bytes ≤ a.2.base)
  | _, _ => false

/-- The counters retain allocation history after stack cleanup. Initial states
must also separate physical regions and use unique lifetime identifiers. -/
def State.valid (state : State) : Bool :=
  decide (state.nextAddress ≤ addressLimit) &&
  state.heap.all (fun (id, allocation) =>
    decide (id < state.nextId ∧ 0 < allocation.base) &&
    match allocation.type.layout with
    | none => false
    | some layout => decide (allocation.base % layout.alignment = 0 ∧
        allocation.base + layout.bytes ≤ state.nextAddress) &&
      allocation.cells.valid allocation.type) &&
  decide (state.heap.Pairwise fun a b => separated a b = true)

def access (state : State) (address : Address) (layout : Layout) (write : Bool) : Except Fault Allocation := do
  let some allocation := state.heap.lookup address.allocation | .error .unallocated
  let some region := allocation.type.layout | .error .unsupported
  if write && !allocation.writable then .error .readOnly
  else if allocation.base = 0 ∨ allocation.base + region.bytes > addressLimit ∨
      allocation.base + address.offset ≥ addressLimit ∨
      address.offset + layout.bytes > region.bytes ∨
      (allocation.base + address.offset) % layout.alignment ≠ 0 then .error .memoryValidity
  else .ok allocation

def readCell (allocation : Allocation) (offset : Nat) (wanted : Ty) : Except Fault Value :=
  allocation.cells.read allocation.type offset wanted

def writeCell (allocation : Allocation) (offset : Nat) (value : Value) : Except Fault Allocation := do
  let cells ← allocation.cells.write allocation.type offset value
  .ok { allocation with cells := cells }

def load (state : State) (pointer : Value) : Except Fault Value := do
  let .pointer (.pointer _ _ child) address := pointer | .error .malformed
  let some layout := child.layout | .error .unsupported
  let allocation ← access state address layout false
  readCell allocation address.offset child

def store (state : State) (pointer value : Value) : Except Fault State := do
  let .pointer (.pointer writable _ child) address := pointer | .error .malformed
  if !writable then .error .readOnly else
  if !value.hasType child then .error .malformed else
  let some layout := child.layout | .error .unsupported
  let allocation ← access state address layout true
  let after ← writeCell allocation address.offset value
  .ok { state with heap := state.heap.replace address.allocation after }

def allocate (state : State) (child : Ty) : Except Fault (Value × State) := do
  if !state.valid then .error .malformed else
  let some layout := child.layout | .error .unsupported
  let base := state.nextAddress + (layout.alignment - state.nextAddress % layout.alignment) % layout.alignment
  -- Exhaustion is an explicit resource outcome, not a source-safety proof.
  if base = 0 ∨ base + layout.bytes ≥ addressLimit then .error .outOfMemory else
  let allocation : Allocation := ⟨base, child, [], true, true⟩
  let pointer := Value.pointer (.pointer true false child) ⟨state.nextId, 0⟩
  .ok (pointer, ⟨(state.nextId, allocation) :: state.heap, state.nextId + 1, base + layout.bytes⟩)

/-- Only this invocation's stack allocations are removed. Lifetime identifiers
and address counters are never rewound, including after an exceptional result. -/
def cleanup (mark : Nat) (state : State) : State :=
  { state with heap := state.heap.filter (fun (id, allocation) => !allocation.stack || id < mark) }

def pointerField (length : Bool) (pointer : Value) : Except Fault Value := do
  let .pointer (.pointer writable _ (.slice elements child)) address := pointer | .error .malformed
  let field := if length then usize else Ty.pointer elements true child
  .ok (.pointer (.pointer writable false field) { address with offset := address.offset + if length then 8 else 0 })

def pointerCompatible (source target : Ty) : Bool :=
  decide (source = target) || match source, target with
  | .array _ child, other | other, .array _ child => decide (child = other)
  | _, _ => false

def pointerCast (state : State) (target : Ty) (value : Value) : Except Fault Value := do
  let .pointer (.pointer writable _ child) address := value | .error .malformed
  let .pointer destWritable many destChild := target | .error .malformed
  if (destWritable && !writable) || !pointerCompatible child destChild then .error .unsupported
  else
    let some layout := destChild.layout | .error .unsupported
    -- Constant-length slicing can end in a pointer cast with no AIR `slice`.
    -- Require its whole array view to fit, even if the result is unused.
    let _ ← access state address ⟨if many then 0 else layout.bytes, layout.alignment⟩ false
    .ok (.pointer target address)

/-- Provenance failure is an unproved memory obligation. We do not give a native
meaning to Zig's undefined pointer result outside the allocation's provenance. -/
def offsetPointer (state : State) (subtract : Bool) (pointer : Value) (count : Nat) : Except Fault Value := do
  let .pointer ty@(.pointer _ true child) address := pointer | .error .malformed
  let some layout := child.layout | .error .unsupported
  if layout.bytes = 0 then .error .unsupported else
  let allocation ← access state address ⟨0, layout.alignment⟩ false
  let amount := count * layout.bytes
  let origin : Int := allocation.base + address.offset
  let raw := if subtract then origin - amount else origin + amount
  if raw < 0 ∨ raw ≥ addressLimit then .error (.scalar .illegalBehavior) else
  if raw < allocation.base then .error .memoryValidity else
  let offset := raw.toNat - allocation.base
  let next := { address with offset := offset }
  let _ ← access state next ⟨0, layout.alignment⟩ false
  .ok (.pointer ty next)

/-- Indexed many-pointer view. As with other single-pointer views, the model
requires the complete element to fit; array-pointer and zero-stride indexing
remain outside this operation's admitted domain. -/
def elementPointer (state : State) (pointer : Value) (index : Nat) : Except Fault Value := do
  let .pointer (.pointer writable true child) _ := pointer | .error .malformed
  let shifted ← offsetPointer state false pointer index
  pointerCast state (.pointer writable false child) shifted

/-- Slice indexing keeps the original source bound even when the allocation is
larger. In-bounds indexing still checks provenance, layout and element extent. -/
def sliceElementPointer (state : State) (view : Value) (index : Nat) : Except Fault Value := do
  let .slice (.slice writable child) address length := view | .error .malformed
  if length ≥ addressLimit then .error .malformed else
  if index < length then elementPointer state (.pointer (.pointer writable true child) address) index
  else .error .sourceBounds

def makeSlice (state : State) (target : Ty) (pointer : Value) (length : Nat) : Except Fault Value := do
  let .slice writable child := target | .error .malformed
  let .pointer (.pointer sourceWritable true sourceChild) address := pointer | .error .malformed
  if sourceChild ≠ child ∨ (writable && !sourceWritable) then .error .malformed else
  if length ≥ addressLimit then .error (.scalar .illegalBehavior) else
  let some layout := child.layout | .error .unsupported
  if layout.bytes = 0 then .error .unsupported else
  let _ ← access state address ⟨length * layout.bytes, layout.alignment⟩ false
  .ok (.slice target address length)

/-- This bound is the original source view, not the extent of its allocation. -/
def checkSliceBounds (start finish : Nat) (upper : Option Nat) : Except Fault Unit :=
  if start ≤ finish ∧ (upper.isNone ∨ upper.any (finish ≤ ·)) then .ok ()
  else .error .sourceBounds

end Compiler.ZigAir.Memory
