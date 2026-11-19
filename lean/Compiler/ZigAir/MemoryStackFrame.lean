/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryCellFrame

namespace Compiler.ZigAir.Memory

/-- Invocation-owned stack storage precedes the unchanged caller heap. Contents
may evolve; cleanup retires exactly this prefix and retains allocation history. -/
structure StackFrame (before after : State) : Prop where
  initial : before.valid = true
  valid : after.valid = true
  nextId : before.nextId ≤ after.nextId
  extended : ∃ locals, after.heap = locals ++ before.heap ∧
    ∀ entry ∈ locals, entry.2.stack = true ∧ before.nextId ≤ entry.1

namespace StackFrame
variable {before after : State}

theorem older (state : State) (valid : state.valid = true) (entry : Nat × Allocation) (member : entry ∈ state.heap) :
    entry.1 < state.nextId :=
  (valid_lookup state entry.1 entry.2 valid (lookup_of_mem_valid state entry.1 entry.2 valid member)).1

theorem refl (state : State) (valid : state.valid = true) : StackFrame state state :=
  ⟨valid, valid, Nat.le_refl _, [], rfl, by simp⟩

theorem allocate (frame : StackFrame before after) (type : Ty) (value : Value) (reached : State)
    (ran : Memory.allocate after type = .ok (value, reached)) : StackFrame before reached := by
  obtain ⟨layout, base, _, _, reachedEq⟩ := allocate_shape after type value reached ran
  obtain ⟨locals, heapEq, owned⟩ := frame.extended
  refine ⟨frame.initial, allocate_preserves_valid after type value reached ran,
    by rw [reachedEq]; exact Nat.le_trans frame.nextId (Nat.le_succ _),
    (after.nextId, ⟨base, type, [], true, true⟩) :: locals, ?_, ?_⟩
  · simp only [reachedEq, heapEq, List.cons_append]
  · intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨rfl, frame.nextId⟩
    · exact owned entry member

theorem native_cell (frame : StackFrame before after) (id : Nat) (cell : Allocation)
    (fresh : before.nextId ≤ id) (found : after.heap.lookup id = some cell) : cell.stack = true := by
  obtain ⟨locals, heapEq, owned⟩ := frame.extended
  have member := Heap.lookup_mem after.heap id cell found
  rw [heapEq, List.mem_append] at member
  rcases member with freshEntry | caller
  · exact (owned _ freshEntry).1
  · have old := older before frame.initial _ caller
    omega

/-- Cell replacement is confined to a newly allocated local. The reusable cell
frame separately equates each typed read/write to the original heap primitive. -/
theorem install (stack : StackFrame before after) (id : Nat) (frame : CellFrame after id) (cells : Cells)
    (fresh : before.nextId ≤ id) (typed : cells.valid frame.cell.type = true) :
    StackFrame before (frame.install cells) := by
  obtain ⟨locals, heapEq, owned⟩ := stack.extended
  have caller : before.heap.replace id { frame.cell with cells } = before.heap := by
    unfold Heap.replace
    refine (List.map_congr_left ?_).trans (List.map_id' _)
    intro entry member
    have old := older before stack.initial entry member
    exact if_neg (by omega : entry.1 ≠ id)
  refine ⟨stack.initial, frame.valid cells stack.valid typed, stack.nextId,
    locals.replace id { frame.cell with cells }, ?_, ?_⟩
  · simp only [CellFrame.install, heapEq, Heap.replace, List.map_append] at caller ⊢
    rw [caller]
  · intro entry member
    obtain ⟨old, inside, replaced⟩ := List.mem_map.mp member
    by_cases same : old.1 = id
    · simp only [if_pos same] at replaced
      rw [← replaced]
      exact ⟨stack.native_cell id frame.cell fresh frame.found, fresh⟩
    · simp only [if_neg same] at replaced
      rw [← replaced]
      exact owned old inside

/-- Cleanup restores the complete original heap, including partially
initialized caller objects. Both monotonically allocated counters are retained. -/
theorem cleanup_heap (frame : StackFrame before after) :
    (Memory.cleanup before.nextId after).heap = before.heap := by
  obtain ⟨locals, heapEq, owned⟩ := frame.extended
  have localGone : locals.filter (fun entry => !entry.2.stack || entry.1 < before.nextId) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro entry member
    obtain ⟨stack, recent⟩ := owned entry member
    simp only [stack, Bool.not_true, Bool.false_or, Nat.not_lt.mpr recent, decide_false, Bool.false_eq_true, not_false_eq_true]
  have callerKept : before.heap.filter (fun entry => !entry.2.stack || entry.1 < before.nextId) = before.heap := by
    apply List.filter_eq_self.mpr
    intro entry member
    simp only [older before frame.initial entry member, decide_true, Bool.or_true]
  simp only [Memory.cleanup, heapEq, List.filter_append, localGone, callerKept, List.nil_append]

theorem cleanup_valid (frame : StackFrame before after) : (Memory.cleanup before.nextId after).valid = true :=
  cleanup_preserves_valid before.nextId after frame.valid

/-- A completed nested invocation remains a frame: its locals have retired,
while the reached lifetime and address cursors remain in the returned state. -/
theorem cleaned (frame : StackFrame before after) : StackFrame before (Memory.cleanup before.nextId after) :=
  ⟨frame.initial, frame.cleanup_valid, frame.nextId, [], frame.cleanup_heap, by simp⟩

/-- A declared type on a valid heap can fail allocation only by explicit stack
resource exhaustion. This does not turn that rejection into successful hashing. -/
theorem allocation_fault (state : State) (type : Ty) (layout : Layout) (fault : Fault)
    (valid : state.valid = true) (shaped : type.layout = some layout)
    (failed : Memory.allocate state type = .error fault) : fault = .outOfMemory := by
  simp only [Memory.allocate, valid, Bool.not_true, Bool.false_eq_true, ↓reduceIte, shaped] at failed
  split at failed
  · exact (Except.error.inj failed).symm
  · contradiction

theorem trans (first : StackFrame before middle) (second : StackFrame middle after) : StackFrame before after := by
  obtain ⟨a, ah, av⟩ := first.extended
  obtain ⟨b, bh, bv⟩ := second.extended
  refine ⟨first.initial, second.valid, Nat.le_trans first.nextId second.nextId, b ++ a, ?_, ?_⟩
  · rw [bh, ah, List.append_assoc]
  · intro entry member
    rcases List.mem_append.mp member with inside | inside
    · exact ⟨(bv entry inside).1, Nat.le_trans first.nextId (bv entry inside).2⟩
    · exact av entry inside

theorem old_lookup (frame : StackFrame before after) (id : Nat) (cell : Allocation)
    (found : before.heap.lookup id = some cell) : after.heap.lookup id = some cell := by
  have older := (valid_lookup before id cell frame.initial found).1
  rw [← cleanup_lookup_older after before.nextId id older, frame.cleanup_heap]
  exact found

/-- A successful caller load survives allocation and mutation of fresh locals.
The lifetime is recovered from the load itself, including an empty view's lack
of reads; no caller-allocation or successful post-load premise is added. -/
theorem old_load (frame : StackFrame before after) (writable many : Bool) (child : Ty)
    (address : Address) (value : Value)
    (loaded : Memory.load before (.pointer (.pointer writable many child) address) = .ok value) :
    Memory.load after (.pointer (.pointer writable many child) address) = .ok value := by
  cases shaped : child.layout with
  | none => simp only [Memory.load, shaped] at loaded; cases loaded
  | some shape =>
    cases found : before.heap.lookup address.allocation with
    | none => simp only [Memory.load, shaped, Memory.access, found, bind, Except.bind] at loaded; cases loaded
    | some cell =>
      simp only [Memory.load, shaped, Memory.access, found] at loaded
      simpa only [Memory.load, shaped, Memory.access, frame.old_lookup _ _ found] using loaded

/-- The body is proved once at the cell layer; allocation and writable-root
admission are derived here. Exhaustion is explicit, and every reached local is
owned by the invocation even when a later allocation fails. -/
theorem create (state : State) (owner : Ty) (layout : Layout)
    (body : Cells → Except Fault (α × Cells)) (value : α) (cells : Cells)
    (valid : state.valid = true) (shaped : owner.layout = some layout) (positive : 0 < layout.bytes)
    (ran : body [] = .ok (value, cells)) (typed : cells.valid owner = true) :
    ∃ result after, CellFrame.create state owner body = (result, after) ∧ StackFrame state after ∧
      (result = .error .outOfMemory ∨
        (result = .ok (value, state.nextId) ∧ ∃ cell, after.heap.lookup state.nextId = some cell ∧
          cell.type = owner ∧ cell.cells = cells ∧ cell.writable = true)) := by
  cases allocated : Memory.allocate state owner with
  | error fault =>
    have same := allocation_fault state owner layout fault valid shaped allocated
    subst fault
    exact ⟨_, state, by simp only [CellFrame.create, allocated], refl state valid, Or.inl rfl⟩
  | ok pair =>
    obtain ⟨pointer, reached⟩ := pair
    obtain ⟨frame, type, _, created⟩ := CellFrame.create_allocated state owner layout pointer reached body value cells
      shaped positive allocated ran typed
    have stack := (refl state valid).allocate owner pointer reached allocated
    have fresh : state.nextId ≤ state.nextId := Nat.le_refl _
    have writable : frame.cell.writable = true := by
      cases permission : frame.cell.writable
      · have access := frame.admitted
        simp [Memory.access, frame.found, frame.shaped, permission] at access
      · rfl
    exact ⟨_, _, created, stack.install _ frame cells fresh (type ▸ typed),
      Or.inr ⟨rfl, { frame.cell with cells }, frame.lookup cells, type, rfl, writable⟩⟩

end StackFrame
end Compiler.ZigAir.Memory
