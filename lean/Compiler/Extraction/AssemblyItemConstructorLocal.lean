/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyCloneFields
import Compiler.Extraction.InternerConstructorFrame

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem
open Compiler.Algebraic Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open AssemblyItem.Fields

/-- The evaluated constructor value includes every struct default and the
actual debug argument. It has no owned verbatim payload. -/
def input (item : Item) (debug : Values) : AssemblyClone.NativeFields.ItemValue :=
  ⟨item, AssemblyItem.Initializers.construct item debug, none⟩

theorem input_fields (item : Item) (debug : Values) :
    AssemblyClone.NativeFields.values (input item debug) = AssemblyItem.Initializers.construct item debug := by
  funext selected
  cases selected <;> rfl

def finish (before : World σ) (allocated : Compiler.ZigAir.Memory.State)
    (result : Except Compiler.ZigAir.Memory.Fault Compiler.ZigAir.Memory.State) :
    Except Fault Compiler.ZigAir.Memory.Address × World σ :=
  match result with
  | .error fault => (.error (.memory (.preparation (.memory fault))),
      { before with memory := { before.memory with memory := allocated } })
  | .ok memory => (.ok ⟨before.memory.memory.nextId, 0⟩, { before with memory := { before.memory with memory } })

def enter (item : Item) (debug : Values) (before : World σ)
    (result : Except Compiler.ZigAir.Memory.Fault (Compiler.ZigAir.Memory.Value × Compiler.ZigAir.Memory.State)) :
    Except Fault Compiler.ZigAir.Memory.Address × World σ :=
  match result with
  | .error fault => (.error (.memory (.preparation (.memory fault))), before)
  | .ok (_, allocated) => finish before allocated
      (assign (AssemblyItem.Initializers.construct item debug) before.memory.memory.nextId allocated)

/-- Materialize the constructor-local item before entering findDefault. Stack
allocation and complete field assignment use the existing native memory model;
assignment rejection retains the allocated, reached frame. -/
def prepare (item : Item) (debug : Values) : GraphAction σ Compiler.ZigAir.Memory.Address := fun before =>
  enter item debug before (Compiler.ZigAir.Memory.allocate before.memory.memory AssemblyItem.viewType)

theorem enter_ok (item : Item) (debug : Values) (before : World σ)
    (pointer : Compiler.ZigAir.Memory.Value) (allocated : Compiler.ZigAir.Memory.State) :
    enter item debug before (.ok (pointer, allocated)) =
      finish before allocated (assign (AssemblyItem.Initializers.construct item debug) before.memory.memory.nextId allocated) := rfl

theorem finish_ok (before : World σ) (allocated memory : Compiler.ZigAir.Memory.State) :
    finish before allocated (.ok memory) =
      (.ok ⟨before.memory.memory.nextId, 0⟩, { before with memory := { before.memory with memory } }) := rfl

theorem prepare_of_calls (item : Item) (debug : Values) (before : World σ)
    (pointer : Compiler.ZigAir.Memory.Value) (allocated memory : Compiler.ZigAir.Memory.State)
    (allocation : Compiler.ZigAir.Memory.allocate before.memory.memory AssemblyItem.viewType = .ok (pointer, allocated))
    (assigned : assign (AssemblyItem.Initializers.construct item debug) before.memory.memory.nextId allocated = .ok memory) :
    prepare item debug before = (.ok ⟨before.memory.memory.nextId, 0⟩, { before with memory := { before.memory with memory } }) := by
  exact (congrArg (enter item debug before) allocation).trans
    ((enter_ok item debug before pointer allocated).trans
      ((congrArg (finish before allocated) assigned).trans (finish_ok before allocated memory)))

theorem represented_of_reads (item : Item) (debug : Values) (memory : Compiler.ZigAir.Memory.State)
    (address : Compiler.ZigAir.Memory.Address)
    (reads : ∀ selected, member memory address selected = .ok (AssemblyItem.Initializers.construct item debug selected)) :
    AssemblyClone.NativeFields.Represents memory address (input item debug) := by
  intro selected
  rw [input_fields]
  exact reads selected

private theorem allocation_valid (before : Session σ) (type : Compiler.ZigAir.Memory.Ty)
    (pointer : Compiler.ZigAir.Memory.Value) (allocated : Compiler.ZigAir.Memory.State)
    (valid : Valid before) (allocation : Compiler.ZigAir.Memory.allocate before.memory type = .ok (pointer, allocated)) :
    ∃ cell, allocated.heap.lookup before.memory.nextId = some cell ∧ cell.type = type ∧
      cell.writable = true ∧ cell.stack = true ∧ Valid ({ before with memory := allocated } : Session σ) ∧
      (∀ id, id ≠ before.memory.nextId → allocated.heap.lookup id = before.memory.heap.lookup id) := by
  obtain ⟨layout, base, _, _, stateShape⟩ := Compiler.ZigAir.Memory.allocate_shape _ _ _ _ allocation
  have found : allocated.heap.lookup before.memory.nextId = some ⟨base, type, [], true, true⟩ := by
    rw [stateShape]; simp [Compiler.ZigAir.Memory.Heap.lookup_cons]
  have frame (id : Nat) (apart : id ≠ before.memory.nextId) : allocated.heap.lookup id = before.memory.heap.lookup id := by
    rw [stateShape]; simp [Compiler.ZigAir.Memory.Heap.lookup_cons, Ne.symm apart]
  exact ⟨_, found, rfl, rfl, rfl, Valid.private_memory_frame before allocated before.memory.nextId valid
    (valid.injected.fresh valid.memory) (Compiler.ZigAir.Memory.allocate_preserves_valid _ _ _ _ allocation)
    (Compiler.ZigAir.Memory.allocate_retains_shape _ _ _ _ valid.memory allocation) frame, frame⟩

structure Prepared (item : Item) (debug : Values) (before after : World σ) : Prop where
  valid : Valid after.memory
  represented : AssemblyClone.NativeFields.Represents after.memory.memory ⟨before.memory.memory.nextId, 0⟩ (input item debug)
  graph : after.graph = before.graph
  heap : after.memory.heap = before.memory.heap
  effects : after.memory.effects = before.memory.effects
  nextId : after.memory.memory.nextId = before.memory.memory.nextId + 1
  memory : ∀ id cell, before.memory.memory.heap.lookup id = some cell → after.memory.memory.heap.lookup id = some cell
  unregistered : after.memory.heap before.memory.memory.nextId = none
  stack : ∃ cell, after.memory.memory.heap.lookup before.memory.memory.nextId = some cell ∧ cell.stack = true
  allocation : ∃ pointer allocated,
    Compiler.ZigAir.Memory.allocate before.memory.memory AssemblyItem.viewType = .ok (pointer, allocated) ∧
    after.memory.memory.nextAddress = allocated.nextAddress

/-- The same stack allocation and stores derive native item correspondence,
registry validity, private ownership, and the frame of all existing storage.
No final member reads, argument contents or graph correspondence are assumed. -/
theorem prepare_verified (item : Item) (debug : Values) (before : World σ)
    (pointer : Compiler.ZigAir.Memory.Value) (allocated : Compiler.ZigAir.Memory.State)
    (valid : Valid before.memory) (domain : (item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (typed : AssemblyItem.Initializers.DebugTyped debug)
    (allocation : Compiler.ZigAir.Memory.allocate before.memory.memory AssemblyItem.viewType = .ok (pointer, allocated)) :
    ∃ after, prepare item debug before = (.ok ⟨before.memory.memory.nextId, 0⟩, after) ∧
      Prepared item debug before after := by
  have fresh := valid.injected.fresh valid.memory
  obtain ⟨native, found, nativeTyped, writable, stack, allocatedValid, frame⟩ := allocation_valid before.memory _ _ _ valid allocation
  obtain ⟨memory, assigned, written, reads⟩ := assign_total (AssemblyItem.Initializers.construct item debug)
    before.memory.memory.nextId allocated _ (AssemblyItem.Initializers.construct_typed item debug domain typed)
    allocatedValid.memory found nativeTyped writable
  have finalValid := Valid.private_memory_frame { before.memory with memory := allocated } memory
    before.memory.memory.nextId allocatedValid fresh written.valid written.shape written.frame
  obtain ⟨cell, located, cellShape⟩ := written.shape _ _ found
  refine ⟨{ before with memory := { before.memory with memory } }, ?_, finalValid, ?_, rfl, rfl, rfl,
    written.nextId.trans (Compiler.ZigAir.Memory.allocate_pointer _ _ _ _ allocation).2, ?_, fresh,
    ⟨cell, located, cellShape.2.2.2.trans stack⟩, ⟨pointer, allocated, allocation, written.nextAddress⟩⟩
  · exact prepare_of_calls item debug before pointer allocated memory allocation assigned
  · exact represented_of_reads item debug memory _ reads
  · intro id cell stored
    have older := (Compiler.ZigAir.Memory.valid_lookup _ _ _ valid.memory stored).1
    exact (written.frame id (by omega)).trans ((frame id (by omega)).trans stored)

/-- Successful execution supplies its own native allocation observation. This
interface needs neither an allocated-state witness nor final field premises. -/
theorem prepare_success (item : Item) (debug : Values) (before after : World σ)
    (address : Compiler.ZigAir.Memory.Address) (valid : Valid before.memory)
    (domain : (item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (typed : AssemblyItem.Initializers.DebugTyped debug)
    (ran : prepare item debug before = (.ok address, after)) :
    address = ⟨before.memory.memory.nextId, 0⟩ ∧ Prepared item debug before after := by
  cases allocation : Compiler.ZigAir.Memory.allocate before.memory.memory AssemblyItem.viewType with
  | error fault =>
    have rejected : prepare item debug before = (.error (.memory (.preparation (.memory fault))), before) :=
      congrArg (enter item debug before) allocation
    rw [ran] at rejected
    cases rejected
  | ok pair =>
    obtain ⟨pointer, allocated⟩ := pair
    obtain ⟨reached, executed, post⟩ := prepare_verified item debug before pointer allocated valid domain typed allocation
    have same := Prod.mk.inj (ran.symm.trans executed)
    cases same.2
    exact ⟨Except.ok.inj same.1, post⟩

/-- The original source view, including its offset, survives constructor-local
initialization. Empty views need no live sentinel; nonempty views derive their
old allocation identity from the original native reads. -/
theorem good_frame (before after : World σ) (source : View) (values : List NodeId)
    (good : Good source values before) (valid : Valid after.memory)
    (frame : ∀ id cell, before.memory.memory.heap.lookup id = some cell → after.memory.memory.heap.lookup id = some cell) :
    Good source values after := by
  refine ⟨valid, good.2.1, ?_⟩
  intro index inside
  have loaded := good.2.2 index inside
  cases accessed : Compiler.ZigAir.Memory.access before.memory.memory (source.address index) ⟨4, 4⟩ false with
  | error fault =>
    simp [Compiler.ZigAir.Memory.load, View.pointer, word, Compiler.ZigAir.Memory.Ty.layout,
      accessed, bind, Except.bind] at loaded
  | ok cell =>
    have found := (Compiler.ZigAir.Memory.access_success_region _ _ _ _ _ accessed).1
    exact (Compiler.ZigAir.Memory.load_eq_of_lookup _ _ true false word _
      ((frame source.allocation cell found).trans found.symm)).trans loaded

/-- Item allocation and field assignment failures are semantic rejections.
They retain their reached state and cannot masquerade as ordinary compiler OOM.
Both native preservation and complete protocol correspondence use this fact. -/
theorem prepare_error_nonordinary (item : Item) (debug : AssemblyItem.Fields.Values)
    (before reached : World σ) (fault : Fault)
    (failed : prepare item debug before = (.error fault, reached)) :
    ordinary (.error fault : Except Fault NodeId) = false := by
  cases allocated : Compiler.ZigAir.Memory.allocate before.memory.memory AssemblyItem.viewType with
  | error error =>
    have rejected : prepare item debug before = (.error (.memory (.preparation (.memory error))), before) :=
      congrArg (enter item debug before) allocated
    have same := Except.error.inj (congrArg Prod.fst (failed.symm.trans rejected))
    rw [same]
    rfl
  | ok pair =>
    obtain ⟨pointer, memory⟩ := pair
    cases assigned : AssemblyItem.Fields.assign (AssemblyItem.Initializers.construct item debug)
        before.memory.memory.nextId memory with
    | error error =>
      have rejected : prepare item debug before =
          (.error (.memory (.preparation (.memory error))), { before with memory := { before.memory with memory } }) :=
        (congrArg (enter item debug before) allocated).trans
          ((enter_ok item debug before pointer memory).trans (congrArg (finish before memory) assigned))
      have same := Except.error.inj (congrArg Prod.fst (failed.symm.trans rejected))
      rw [same]
      rfl
    | ok after =>
      have succeeded := prepare_of_calls item debug before pointer memory after allocated assigned
      have impossible := congrArg Prod.fst (failed.symm.trans succeeded)
      cases impossible


end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem
