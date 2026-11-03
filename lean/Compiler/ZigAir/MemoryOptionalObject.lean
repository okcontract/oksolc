/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemorySlots
import Compiler.ZigAir.MemoryReadTyping

namespace Compiler.ZigAir.Memory.OptionalObject

/-- Validate the whole evaluated payload before returning it. Null is an
initialized value; no fields, pointees or discriminator bytes are read here. -/
def payload (child : Ty) (layout : Layout) (value : Value) : Except Fault (Option ObjectValue) :=
  if !value.hasType (.optionalObject child layout) then .error .malformed else
  match value with
  | .optionalObject _ _ result => .ok result
  | _ => .error .malformed

def Typed (child : Ty) (value : Option ObjectValue) : Prop :=
  ∀ contents, value = some contents → contents.hasType child = true

theorem value_valid (child : Ty) (layout : Layout) (value : Option ObjectValue) (typed : Typed child value) :
    (Value.optionalObject child layout value).valid = true := by
  cases value with
  | none => rfl
  | some contents => exact typed contents rfl

theorem payload_value (child : Ty) (layout : Layout) (value : Option ObjectValue) (typed : Typed child value) :
    payload child layout (.optionalObject child layout value) = .ok value := by
  simp only [payload, Value.hasType, Value.type, decide_true, Bool.true_and,
    value_valid child layout value typed, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

theorem read_after_store (state after : State) (address : Address) (child : Ty) (layout : Layout)
    (value : Option ObjectValue) (typed : Typed child value)
    (stored : store state (.pointer (.pointer true false (.optionalObject child layout)) address)
      (.optionalObject child layout value) = .ok after) :
    (do let result ← load after (.pointer (.pointer false false (.optionalObject child layout)) address)
        payload child layout result) = .ok value := by
  rw [load_alias_after_store state true false (.optionalObject child layout) address
    (.optionalObject child layout value) after false false stored]
  exact payload_value child layout value typed

/-- Complete initial allocation geometry and a checked evaluated payload derive
the actual store, validity and exact readback. Embedded addresses are copied;
this establishes no ownership, contents or liveness of their pointees. -/
theorem store_root (state : State) (id : Nat) (cell : Allocation) (child : Ty) (layout : Layout)
    (value : Option ObjectValue) (typedValue : Typed child value)
    (valid : state.valid = true) (found : state.heap.lookup id = some cell)
    (typedCell : cell.type = .optionalObject child layout) (writable : cell.writable = true)
    (shaped : (Ty.optionalObject child layout).layout = some layout) (positive : 0 < layout.bytes) :
    ∃ after, store state (.pointer (.pointer true false (.optionalObject child layout)) ⟨id, 0⟩)
      (.optionalObject child layout value) = .ok after ∧ after.valid = true ∧
      (do let result ← load after (.pointer (.pointer false false (.optionalObject child layout)) ⟨id, 0⟩)
          payload child layout result) = .ok value := by
  obtain ⟨after, stored⟩ := root_store_total state id cell (.optionalObject child layout value) layout
    valid found typedCell writable (value_valid child layout value typedValue) shaped positive
  exact ⟨after, stored, store_preserves_valid state _ _ after valid stored,
    read_after_store state after ⟨id, 0⟩ child layout value typedValue stored⟩

end Compiler.ZigAir.Memory.OptionalObject
