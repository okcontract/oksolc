/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.ObservedStorage
import Compiler.Extraction.DispatchProgram

namespace Compiler.Extraction.Interner
open Compiler.Algebraic Compiler.Extraction.Cache

/-- An attached graph may grow, but no old descriptor may change or disappear.
Value-only heaps make no structural claim. Once attached, a view stays attached. -/
def Extends (before after : Heap) : Prop :=
  ∀ cells, before.representatives = some cells →
    ∃ suffix, after.representatives = some (cells ++ suffix)

theorem Extends.refl (heap : Heap) : Extends heap heap := by
  intro cells present
  exact ⟨[], by simpa using present⟩

theorem Extends.trans {before middle after : Heap} (first : Extends before middle)
    (second : Extends middle after) : Extends before after := by
  intro cells present
  obtain ⟨left, mid⟩ := first cells present
  obtain ⟨right, last⟩ := second (cells ++ left) mid
  exact ⟨left ++ right, by simpa [List.append_assoc] using last⟩

def Frames (action : Action α) : Prop := ∀ before, Extends before (action before).2

theorem Frames.pure (value : α) : Frames (pure value) := Extends.refl
theorem Frames.fail (error : Error) : Frames (fail (α := α) error) := Extends.refl
theorem Frames.lift (result : Except Error α) : Frames (lift result) := Extends.refl
theorem Frames.get : Frames get := Extends.refl

theorem Frames.local (action : Local α) : Frames (liftLocal action) := by
  intro before cells present
  exact ⟨[], by simpa only [liftLocal, List.append_nil] using present⟩

theorem Frames.ite (condition : Prop) [Decidable condition] (yes no : Action α)
    (yesFrames : Frames yes) (noFrames : Frames no) : Frames (if condition then yes else no) := by
  split <;> assumption

theorem Frames.option (value : Option α) (absent : Action β) (present : α → Action β)
    (absentFrames : Frames absent) (presentFrames : ∀ item, Frames (present item)) :
    Frames (match value with | none => absent | some item => present item) := by
  cases value with
  | none => exact absentFrames
  | some item => exact presentFrames item

theorem Frames.bind (first : Action α) (next : α → Action β)
    (firstFrames : Frames first) (nextFrames : ∀ value, Frames (next value)) : Frames (first >>= next) := by
  intro before
  have framed := firstFrames before
  change Extends before (Effect.bind first next before).2
  unfold Effect.bind
  cases step : first before with
  | mk result middle =>
    rw [step] at framed
    cases result with
    | error error => exact framed
    | ok value => exact framed.trans (nextFrames value middle)

theorem Frames.read (result : Except Storage.ReadError α) : Frames (Nested.readAction result) := by
  cases result with
  | ok value => exact Frames.pure value
  | error error => cases error <;> exact Frames.fail _

theorem Frames.arithmetic (result : Except Folding.Fault α) : Frames (Dispatch.arithmetic result) := by
  cases result with
  | ok value => exact Frames.pure value
  | error error => exact Frames.fail _

theorem Frames.publish (succeeds : Bool) (key : Key) (id : NodeId) : Frames (publish succeeds key id) := by
  intro before
  cases succeeds <;> intro cells present <;> exact ⟨[], by simpa [publish] using present⟩

theorem Frames.insert (cell : Storage.Cell) (key : Key) (deterministic : Bool)
    (succeeds : Storage.Allocation → Bool) : Frames (observedInsert cell key deterministic succeeds) := by
  intro before cells present
  simp only [observedInsert, present]
  rw [observed_insert_retains_cells]
  unfold insertionCells
  split
  · exact ⟨[cell], rfl⟩
  · exact ⟨[], by simp⟩

theorem Extends.cell (before after : Heap) (framed : Extends before after)
    (cells : List Storage.Cell) (present : before.representatives = some cells)
    (index : Nat) (bound : index < cells.length) :
    ∃ retained, after.representatives = some retained ∧ retained[index]? = cells[index]? := by
  obtain ⟨suffix, appended⟩ := framed cells present
  exact ⟨cells ++ suffix, appended, List.getElem?_append_left bound⟩

theorem Extends.constant (before after : Heap) (framed : Extends before after)
    (cells : List Storage.Cell) (present : before.representatives = some cells)
    (id : NodeId) (bound : id.toNat < cells.length) :
    (representativeReads after).constant id = (representativeReads before).constant id := by
  obtain ⟨retained, attached, same⟩ := framed.cell before after cells present id.toNat bound
  simp only [representativeReads, present, attached, Nested.storageReads, Storage.constant_correct, same]

theorem Extends.operation (before after : Heap) (framed : Extends before after)
    (cells : List Storage.Cell) (present : before.representatives = some cells)
    (id : NodeId) (bound : id.toNat < cells.length) (opcode : Opcode) :
    (representativeReads after).operation id opcode = (representativeReads before).operation id opcode := by
  obtain ⟨retained, attached, same⟩ := framed.cell before after cells present id.toNat bound
  simp only [representativeReads, present, attached, Nested.storageReads, Storage.operation_correct, same]

end Compiler.Extraction.Interner
