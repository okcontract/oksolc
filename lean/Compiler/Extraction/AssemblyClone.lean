/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.CacheIR

/-! The item clone copies every non-verbatim field, represented by the key item
and an arbitrary metadata value. Borrowed pointers in metadata are copied, not
deep-cloned. Only the optional verbatim byte slice is allocator-owned here.
Allocation identities denote lifetimes, not numerical machine pointers. -/
namespace Compiler.Extraction.AssemblyClone
open Compiler.Algebraic Compiler.Extraction.Cache

/-- Evaluated slice contents retain allocation lifetime and byte offset. A
readable interior view need not own the allocation consumed by destruction. -/
structure Bytes where
  address : Nat
  contents : List (BitVec 8)
  offset : Nat := 0
  deriving DecidableEq, Repr

structure Verbatim where
  arguments : Nat
  returns : Nat
  data : Bytes
  deriving DecidableEq, Repr

structure Value (Metadata : Type) where
  item : Item
  metadata : Metadata
  verbatim : Option Verbatim
  deriving DecidableEq, Repr

structure CloneCode where
  copyPayload : Bool
  arguments : Scalar Nat
  returns : Scalar Nat
  contents : Scalar (List (BitVec 8))
  returnCopy : Bool

def CloneCode.run (code : CloneCode) (duplicate : Bytes → σ → Except ε Bytes × σ)
    (input : Value Metadata) : σ → Except ε (Value Metadata) × σ := fun before =>
  match input.verbatim with
  | none => (.ok input, before)
  | some payload =>
    if code.copyPayload then
      let (result, after) := duplicate { payload.data with contents := code.contents.run payload.data.contents } before
      match result with
      | .error error => (.error error, after)
      | .ok data =>
        let copied := { input with verbatim := some {
          arguments := code.arguments.run payload.arguments,
          returns := code.returns.run payload.returns, data := data } }
        (.ok (if code.returnCopy then copied else input), after)
    else (.ok input, before)

structure DeinitCode where
  freePayload : Bool
  invalidate : Bool

/-- Free's preconditions, including the matching allocator and exclusive live
ownership, remain primitive obligations. A `none` result invalidates the item;
it does not manufacture a valid all-zero item from Zig's `undefined`. -/
def DeinitCode.run (code : DeinitCode) (free : Bytes → Heap → Heap)
    (input : Value Metadata) (before : Heap) : Option (Value Metadata) × Heap :=
  let after := match input.verbatim with
    | none => before
    | some payload => if code.freePayload then free payload.data before else before
  (if code.invalidate then none else some input, after)

/-- These are the allocator's remaining obligations, parametrized by the frame
and ownership relation needed by its caller. Empty slices may have no backing
allocation; ownership must not require distinct sentinel addresses for them. -/
def Duplicates (frame : Heap → Heap → Prop) (owns : Bytes → Bytes → Heap → Heap → Prop)
    (duplicate : Bytes → Effect Heap Error Bytes) : Prop :=
  ∀ source before result after, duplicate source before = (result, after) →
    match result with
    | .error _ => after = before
    | .ok copied => copied.contents = source.contents ∧ frame before after ∧ owns source copied before after

def SameValue (original copied : Value Metadata) : Prop :=
  copied.item = original.item ∧ copied.metadata = original.metadata ∧
    copied.verbatim.map (fun p => (p.arguments, p.returns, p.data.contents)) =
      original.verbatim.map (fun p => (p.arguments, p.returns, p.data.contents))

def Cloned (frame : Heap → Heap → Prop) (owns : Bytes → Bytes → Heap → Heap → Prop)
    (original copied : Value Metadata) (before after : Heap) : Prop :=
  SameValue original copied ∧
    match original.verbatim with
    | none => after = before
    | some payload => ∃ output, copied.verbatim = some output ∧
        frame before after ∧ owns payload.data output.data before after

end Compiler.Extraction.AssemblyClone
