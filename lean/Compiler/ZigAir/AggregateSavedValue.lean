/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.AggregateAirProofs
import Compiler.ZigAir.MemoryStackPrefix
import Compiler.ZigAir.MemoryStackFrame
import Compiler.ZigAir.MemoryReadTyping

namespace Compiler.ZigAir.AggregateAir.SavedValue
open Memory

/-- One native allocation followed by the ordinary typed store. This retains
the reached state on failure, including allocation history before a failed store. -/
def save (state : State) (value : Value) : Except Fault Unit × State :=
  match Memory.allocate state value.type with
  | .error fault => (.error fault, state)
  | .ok (pointer, allocated) =>
    match Memory.store allocated pointer value with
    | .error fault => (.error fault, allocated)
    | .ok after => (.ok (), after)

theorem verified (state : State) (value : Value) (layout : Layout)
    (initial : state.valid = true) (valid : value.valid = true)
    (shaped : value.type.layout = some layout) (positive : 0 < layout.bytes) :
    ∃ result after, save state value = (result, after) ∧ StackFrame state after ∧
      (result = .error .outOfMemory ∨ result = .ok () ∧
        Memory.load after (.pointer (.pointer true false value.type) ⟨state.nextId, 0⟩) = .ok value ∧
        (after.heap.lookup state.nextId).map Allocation.type = some value.type) := by
  cases allocated : Memory.allocate state value.type with
  | error fault =>
    have same := StackFrame.allocation_fault state value.type layout fault initial shaped allocated
    subst fault
    exact ⟨_, state, by simp only [save, allocated], StackFrame.refl state initial, Or.inl rfl⟩
  | ok pair =>
    obtain ⟨pointer, middle⟩ := pair
    obtain ⟨after, written⟩ := fresh_store_total state middle value pointer layout valid shaped positive allocated
    obtain ⟨pointerEq, nextId⟩ := allocate_pointer state value.type pointer middle allocated
    rw [pointerEq] at allocated written
    obtain ⟨cell, stack, prefixed⟩ := saved_slot_prefix state middle after value initial allocated written
    have counters := store_keeps_counters middle _ value after written
    have reached := store_preserves_valid middle _ value after
      (allocate_preserves_valid state value.type _ middle allocated) written
    obtain ⟨frame, owner, _, _⟩ := CellFrame.allocated state value.type layout _ middle shaped positive allocated
    obtain ⟨contents, initialized⟩ := Cells.write_root frame.cell.cells value valid
    have typed : value.hasType frame.cell.type = true := by simp [Value.hasType, owner, valid]
    have stored := frame.store_current value typed
    rw [owner, initialized] at stored
    have afterEq : after = frame.install contents := Except.ok.inj (written.symm.trans stored)
    have found : (after.heap.lookup state.nextId).map Allocation.type = some value.type := by
      rw [afterEq, frame.lookup]
      exact congrArg some owner
    refine ⟨.ok (), after, by simp only [save, allocated, written],
      ⟨initial, reached, by omega, [(state.nextId, cell)], ?_, ?_⟩,
      Or.inr ⟨rfl, load_after_store middle _ value after written, found⟩⟩
    · exact congrArg State.heap prefixed
    · intro entry member
      cases List.mem_singleton.mp member
      exact ⟨stack, Nat.le_refl _⟩

/-- Both saved locals in sliceAsBytes instantiate this same allocation/store
composition; no fixture address or successful allocation is assumed. -/
theorem bindings (value : Value) (reference : Ref) (allocationReg storeReg : Nat) (next : Code)
    (args : List Register) (env : Env) (state : State)
    (read : reference.eval (env.set allocationReg
      (.value (.pointer (.pointer true false value.type) ⟨state.nextId, 0⟩))) = .ok (.value value)) :
    (Control.Code.bind allocationReg (.pointer true false value.type) (.memory (.alloc value.type))
      (.bind storeReg (.scalar .unit) (.store (.local allocationReg) reference) next)).eval semantics args env state =
      match save state value with
      | (.error fault, after) => .fault fault after
      | (.ok (), after) => next.eval semantics args
          (Control.Env.set (env.set allocationReg (.value (.pointer (.pointer true false value.type) ⟨state.nextId, 0⟩)))
            storeReg (.value (.scalar .unit))) after := by
  cases allocation : Memory.allocate state value.type with
  | error fault =>
    simp only [save, allocation, Control.Code.eval, semantics, Prim.eval, Prim.transition,
      MemoryAir.Prim.transition, bind, Except.bind]
  | ok pair =>
    obtain ⟨pointer, allocated⟩ := pair
    have pointerEq := (allocate_pointer state value.type pointer allocated allocation).1
    rw [pointerEq] at allocation
    have allocates := eval_alloc value.type args env state allocated _ allocation
    rw [bind_ok _ _ _ _ _ _ _ _ _ allocates (pointer_typed _ _)]
    have selected := value_local (env.set allocationReg
      (.value (.pointer (.pointer true false value.type) ⟨state.nextId, 0⟩))) allocationReg
      (.pointer (.pointer true false value.type) ⟨state.nextId, 0⟩)
      (by simp [Control.Env.set]) rfl
    simp only [save, allocation, Control.Code.eval, semantics, Prim.eval, Prim.transition,
      selected, read, AggregateAir.store, bind, Except.bind]
    cases Memory.store allocated (.pointer (.pointer true false value.type) ⟨state.nextId, 0⟩) value <;> rfl

/-- Reading the saved descriptor's length is an actual load of its second
leaf. Whole-slice reconstruction supplies that initialized leaf; subregion
geometry derives the access check. -/
theorem slice_length (state : State) (id : Nat) (writable : Bool) (child : Ty)
    (address : Address) (length : Nat)
    (read : Memory.load state (.pointer (.pointer true false (.slice writable child)) ⟨id, 0⟩) =
      .ok (.slice (.slice writable child) address length))
    (owner : (state.heap.lookup id).map Allocation.type = some (.slice writable child)) :
    Memory.load state (.pointer (.pointer false false usize) ⟨id, 8⟩) =
      .ok (.scalar (.int false 64 length)) := by
  cases accessed : access state ⟨id, 0⟩ ⟨16, 8⟩ false with
  | error fault => simp [Memory.load, Ty.layout, Ty.leafLayout, accessed, bind, Except.bind] at read
  | ok cell =>
    have found := (access_success_region state ⟨id, 0⟩ ⟨16, 8⟩ false cell accessed).1
    rw [found] at owner
    have typed : cell.type = .slice writable child := Option.some.inj owner
    have contents : cell.cells.read cell.type 0 (.slice writable child) =
        .ok (.slice (.slice writable child) address length) := by
      simpa only [Memory.load, show (Ty.slice writable child).layout = some ⟨16, 8⟩ from rfl,
        accessed, bind, Except.bind, readCell] using read
    have parts := cell.cells.read_slice_parts cell.type 0 writable child address length contents
    have lengthAccess := access_subregion state ⟨id, 0⟩ ⟨16, 8⟩ ⟨8, 8⟩ 8 false cell
      accessed (by decide) (by decide) (by decide) (by decide)
    simpa only [Memory.load, show usize.layout = some ⟨8, 8⟩ from rfl, lengthAccess,
      bind, Except.bind, readCell, typed, Cells.read, show acceptsView (.slice writable child) 8 usize = true from rfl,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte] using typed ▸ parts.2.2

/-- Recover the owned initialized local from the actual allocation and store.
The mutable index uses this evidence; a successful read alone is not ownership. -/
theorem owned (state after : State) (value : Value) (layout : Layout)
    (valid : value.valid = true) (shaped : value.type.layout = some layout) (positive : 0 < layout.bytes)
    (ran : save state value = (.ok (), after)) :
    ∃ frame : CellFrame after state.nextId,
      frame.cell.type = value.type ∧ frame.cell.cells.valid value.type = true := by
  cases allocated : Memory.allocate state value.type with
  | error fault => simp only [save, allocated] at ran; cases ran
  | ok pair =>
    obtain ⟨pointer, middle⟩ := pair
    cases stored : Memory.store middle pointer value with
    | error fault => simp only [save, allocated, stored] at ran; cases ran
    | ok reached =>
      simp only [save, allocated, stored, Prod.mk.injEq, true_and] at ran
      subst after
      obtain ⟨frame, typed, empty, _⟩ := CellFrame.allocated state value.type layout pointer middle shaped positive allocated
      have pointerEq := (allocate_pointer state value.type pointer middle allocated).1
      obtain ⟨cells, written⟩ := Cells.write_root frame.cell.cells value valid
      have writes := frame.store_current value (by simp [Value.hasType, typed, valid])
      rw [typed, written] at writes
      rw [pointerEq] at stored
      have same : reached = frame.install cells := Except.ok.inj (stored.symm.trans writes)
      subst reached
      exact ⟨frame.replaced cells, typed,
        Cells.write_preserves_valid _ _ _ _ _ (by simp [empty, Cells.valid]) written⟩


end Compiler.ZigAir.AggregateAir.SavedValue
