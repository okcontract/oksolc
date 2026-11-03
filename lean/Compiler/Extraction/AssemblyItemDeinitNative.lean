/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyCloneFields
import Compiler.ZigAir.MemoryInvalidation

namespace Compiler.Extraction.AssemblyItemDeinit.Native
open Compiler.Extraction.Memory.Arguments.Normalization
open Compiler.ZigAir.Memory (Address ObjectValue)

inductive Fault where
  | memory (reason : Compiler.ZigAir.Memory.Fault)
  | payload (reason : AssemblyItemDeinit.Fault)
  deriving DecidableEq, Repr

/-- Select the data descriptor from the already type-checked evaluated optional
payload. Preserve its allocation identity, offset and length; free reads no byte
contents and still establishes its own complete-extent ownership checks. -/
def payloadData (value : ObjectValue) : Except Compiler.ZigAir.Memory.Fault Bytes := do
  let .fields fields := value | .error .malformed
  let some (_, .leaf (.slice type data length)) := fields.find? (fun entry => entry.1 == AssemblyItem.verbatim_dataOffset)
    | .error .malformed
  if type ≠ .slice true byte then .error .malformed else
  .ok ⟨data.allocation, length, data.offset⟩

def readPayload (memory : Compiler.ZigAir.Memory.State) (object : Address) :
    Except Compiler.ZigAir.Memory.Fault (Option Bytes) := do
  let payload ← AssemblyItem.Fields.verbatim memory object
  match payload with
  | none => .ok none
  | some value => return some (← payloadData value)

/-- Complete the extracted undefined-store boundary in the same reached memory.
The old program's Boolean marker is a logical projection; expose invalidated
storage only after the typed native operation succeeds. A failed write retains
the earlier payload release and allocator effects. -/
def finish (object : Address) (reached : Session σ) : Except Fault Unit × AssemblyItemDeinit.State σ :=
  match Compiler.ZigAir.Memory.invalidate reached.memory true AssemblyItem.viewType object with
  | .error reason => (.error (.memory reason), ⟨reached, false⟩)
  | .ok memory => (.ok (), ⟨{ reached with memory }, true⟩)

/-- Read the actual native optional before the existing source-bound payload
destructor. Its reached session supplies the final typed invalidation. No item
allocation is destroyed here; that is the caller's following source operation. -/
def run (external : Release σ) (allocator : Nat) (object : Address) (before : Session σ) :
    Except Fault Unit × AssemblyItemDeinit.State σ :=
  match readPayload before.memory object with
  | .error reason => (.error (.memory reason), ⟨before, false⟩)
  | .ok payload =>
    let (result, reached) := AssemblyItemDeinit.run external allocator payload before
    match result with
    | .error reason => (.error (.payload reason), reached)
    | .ok () => finish object reached.memory

theorem payload_data (value : AssemblyClone.Verbatim) :
    payloadData (AssemblyClone.NativeFields.payloadValue value) =
      .ok ⟨value.data.address, value.data.contents.length, value.data.offset⟩ := by rfl

private theorem optional_payload (child : Compiler.ZigAir.Memory.Ty) (layout : Compiler.ZigAir.Memory.Layout)
    (value : Option ObjectValue)
    (typed : (Compiler.ZigAir.Memory.Value.optionalObject child layout value).hasType (.optionalObject child layout) = true) :
    Compiler.ZigAir.Memory.OptionalObject.payload child layout (.optionalObject child layout value) = .ok value := by
  simp only [Compiler.ZigAir.Memory.OptionalObject.payload, typed, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

/-- Exact payload projection follows the native clone-member relation. This
uses the same evaluated clone value and forwards the actual offset unchanged. -/
theorem read_represented (memory : Compiler.ZigAir.Memory.State) (object : Address)
    (input : AssemblyClone.NativeFields.ItemValue)
    (represented : AssemblyClone.NativeFields.Represents memory object input) :
    readPayload memory object = .ok (AssemblyClone.Physical.payload input) := by
  have typed := represented.typed .verbatim
  change (Compiler.ZigAir.Memory.Value.optionalObject AssemblyItem.verbatimType ⟨40, 8⟩
    (input.verbatim.map AssemblyClone.NativeFields.payloadValue)).hasType (.optionalObject AssemblyItem.verbatimType ⟨40, 8⟩) = true at typed
  unfold readPayload AssemblyItem.Fields.verbatim
  rw [represented .verbatim]
  simp only [bind, Except.bind, AssemblyClone.NativeFields.values, AssemblyClone.NativeFields.verbatimValue,
    optional_payload _ _ _ typed]
  cases selected : input.verbatim <;>
    simp only [Option.map_none, Option.map_some, payload_data, pure, Except.pure,
      AssemblyClone.Physical.payload, selected, AssemblyClone.Physical.descriptor]

theorem finish_retains (object : Address) (reached : Session σ) :
    (finish object reached).2.memory.heap = reached.heap ∧
    (finish object reached).2.memory.effects = reached.effects := by
  unfold finish
  split <;> exact ⟨rfl, rfl⟩

theorem finish_rejected (object : Address) (reached : Session σ) (reason : Compiler.ZigAir.Memory.Fault)
    (rejected : Compiler.ZigAir.Memory.invalidate reached.memory true AssemblyItem.viewType object = .error reason) :
    finish object reached = (.error (.memory reason), ⟨reached, false⟩) := by simp only [finish, rejected]

theorem finish_verified (allocator object : Nat) (before : Session σ)
    (initial : Valid before) (owned : AssemblyItem.Owned allocator object before) :
    ∃ after, finish ⟨object, 0⟩ before = (.ok (), after) ∧
      Compiler.ZigAir.Memory.invalidate before.memory true AssemblyItem.viewType ⟨object, 0⟩ = .ok after.memory.memory ∧
      Valid after.memory ∧ AssemblyItem.Owned allocator object after.memory ∧
      after.memory.heap = before.heap ∧ after.memory.effects = before.effects ∧ after.invalidated = true := by
  obtain ⟨cell, found, typed, writable, _⟩ := owned.2
  have executed := Compiler.ZigAir.Memory.invalidate_of_access before.memory AssemblyItem.viewType ⟨object, 0⟩
    AssemblyItem.Creation.layout cell AssemblyItem.Creation.view_layout_captured
    (Compiler.ZigAir.Memory.root_access before.memory object cell AssemblyItem.Creation.layout true initial.memory found
      (typed ▸ AssemblyItem.Creation.view_layout_captured) (by decide) (by intro _; exact writable))
    (typed ▸ Compiler.ZigAir.Memory.acceptsView_self AssemblyItem.viewType)
  have retained := AssemblyItem.session_frame allocator object before _
    (Compiler.ZigAir.Memory.invalidate_valid _ _ _ _ _ initial.memory executed)
    (Compiler.ZigAir.Memory.invalidate_retains_shape _ _ _ _ _ executed)
    (Compiler.ZigAir.Memory.invalidate_frame _ _ _ _ _ executed).2.2 initial owned
  exact ⟨⟨_, true⟩, by simp only [finish, executed], executed, retained.1, retained.2, rfl, rfl, rfl⟩

/-- Initial member correspondence and separated ownership derive both source
stages. The intermediate payload postcondition is retained explicitly: native
invalidation changes the item's own leaves, so its final frame must exclude
that allocation as well as any freed payload. -/
theorem run_verified (external : Release σ) (allocator object : Nat)
    (input : AssemblyClone.NativeFields.ItemValue) (before : Session σ)
    (initial : Valid before) (itemOwned : AssemblyItem.Owned allocator object before)
    (represented : AssemblyClone.NativeFields.Represents before.memory ⟨object, 0⟩ input)
    (payloadOwned : ∀ slice, AssemblyClone.Physical.payload input = some slice → Owned allocator slice before) :
    ∃ released after, run external allocator ⟨object, 0⟩ before = (.ok (), after) ∧
      AssemblyItemDeinit.run external allocator (AssemblyClone.Physical.payload input) before = (.ok (), released) ∧
      AssemblyItemDeinit.Post (AssemblyClone.Physical.payload input) before released ∧
      Compiler.ZigAir.Memory.invalidate released.memory.memory true AssemblyItem.viewType ⟨object, 0⟩ = .ok after.memory.memory ∧
      Valid after.memory ∧ AssemblyItem.Owned allocator object after.memory ∧
      after.memory.heap = released.memory.heap ∧ after.invalidated = true ∧
      after.memory.effects = released.memory.effects := by
  obtain ⟨released, payloadRun, payloadPost, _⟩ :=
    AssemblyItemDeinit.run_verified external allocator _ before initial payloadOwned
  have retained := AssemblyItem.after_payload allocator object _ before released itemOwned payloadOwned payloadPost
  obtain ⟨after, finished, invalidated, valid, owned, heap, sameEffects, marker⟩ :=
    finish_verified allocator object released.memory payloadPost.valid retained
  refine ⟨released, after, ?_, payloadRun, payloadPost, invalidated, valid, owned, heap, marker, sameEffects⟩
  simp only [run, read_represented _ _ _ represented, payloadRun, finished]

end Compiler.Extraction.AssemblyItemDeinit.Native
