/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryRecordWrites
import Compiler.ZigAir.MemoryAllocationShape
import Compiler.ZigAir.MemoryScalarTransfer

namespace Compiler.ZigAir.Memory

/-- A checked writable allocation. Evolving its sparse cells retains the same
native lifetime, region, type and permissions. Undefined leaves stay undefined. -/
structure CellFrame (before : State) (id : Nat) where
  cell : Allocation
  layout : Layout
  found : before.heap.lookup id = some cell
  shaped : cell.type.layout = some layout
  admitted : access before ⟨id, 0⟩ layout true = .ok cell

namespace CellFrame
variable {before : State} {id : Nat}

def install (frame : CellFrame before id) (cells : Cells) : State :=
  { before with heap := before.heap.replace id { frame.cell with cells } }

/-- Scoped evaluation over an actual writable typed region. The caller supplies
an executable cell operation, not its result. Root admission, type agreement and
the returned cell validity are checked; the scalar reflection laws below connect
its typed operations to the heap primitives. This is not an AIR trace theorem. -/
def borrow (state : State) (id : Nat) (owner : Ty) (body : Cells → Except Fault (α × Cells)) :
    Except Fault (α × State) := do
  let some layout := owner.layout | .error .unsupported
  let cell ← access state ⟨id, 0⟩ layout true
  if cell.type ≠ owner then .error .unsupported else
  let (value, cells) ← body cell.cells
  if !cells.valid owner then .error .malformed else
  .ok (value, { state with heap := state.heap.replace id { cell with cells } })

theorem borrow_eq (frame : CellFrame before id) (body : Cells → Except Fault (α × Cells))
    (value : α) (cells : Cells) (ran : body frame.cell.cells = .ok (value, cells))
    (typed : cells.valid frame.cell.type = true) :
    borrow before id frame.cell.type body = .ok (value, frame.install cells) := by
  simp only [borrow, frame.shaped, frame.admitted, bind, Except.bind, ne_self_iff_false, ↓reduceIte,
    ran, typed, Bool.not_true, Bool.false_eq_true, install]

def of_valid (before : State) (id : Nat) (cell : Allocation) (layout : Layout)
    (valid : before.valid = true) (found : before.heap.lookup id = some cell)
    (shaped : cell.type.layout = some layout) (positive : 0 < layout.bytes)
    (writable : cell.writable = true) : CellFrame before id :=
  ⟨cell, layout, found, shaped, root_access before id cell layout true valid found shaped positive (fun _ => writable)⟩

theorem lookup (frame : CellFrame before id) (cells : Cells) :
    (frame.install cells).heap.lookup id = some { frame.cell with cells } :=
  Heap.lookup_replace _ _ _ _ frame.found

theorem outside (frame : CellFrame before id) (cells : Cells) (other : Nat) (apart : other ≠ id) :
    (frame.install cells).heap.lookup other = before.heap.lookup other := replace_other _ _ _ _ apart

theorem valid (frame : CellFrame before id) (cells : Cells) (initial : before.valid = true)
    (typed : cells.valid frame.cell.type = true) : (frame.install cells).valid = true :=
  replace_typed_preserves_valid _ _ _ _ initial frame.found typed

theorem counters (frame : CellFrame before id) (cells : Cells) :
    (frame.install cells).nextId = before.nextId ∧ (frame.install cells).nextAddress = before.nextAddress := ⟨rfl, rfl⟩

/-- Read the current root without first replacing its cells. Initialization is
still decided by the existing typed reader, including its failure outcomes. -/
theorem load_current (frame : CellFrame before id) (writable many : Bool) :
    load before (.pointer (.pointer writable many frame.cell.type) ⟨id, 0⟩) =
      frame.cell.cells.read frame.cell.type 0 frame.cell.type := by
  have readable := access_write_read before ⟨id, 0⟩ frame.layout frame.cell frame.admitted
  simp only [load, frame.shaped, readable, bind, Except.bind, readCell]

/-- The current root's ordinary store, with admission derived from the frame.
The result keeps the original allocator cursors and all unrelated allocations. -/
theorem store_current (frame : CellFrame before id) (value : Value)
    (typed : value.hasType frame.cell.type = true) :
    store before (.pointer (.pointer true false frame.cell.type) ⟨id, 0⟩) value =
      (frame.cell.cells.write frame.cell.type 0 value).map frame.install := by
  simp only [store, Bool.not_true, Bool.false_eq_true, ↓reduceIte, typed,
    frame.shaped, frame.admitted, bind, Except.bind, writeCell]
  cases frame.cell.cells.write frame.cell.type 0 value <;> rfl

/-- Updating another allocation preserves this region's complete admission.
No assumed successful read or store is introduced at the second root. -/
def after_other (frame : CellFrame before id) (other : CellFrame before otherId)
    (cells : Cells) (apart : otherId ≠ id) : CellFrame (frame.install cells) otherId where
  cell := other.cell
  layout := other.layout
  found := (frame.outside cells otherId apart).trans other.found
  shaped := other.shaped
  admitted := by simpa only [access, frame.outside cells otherId apart] using other.admitted

/-- Restoring the current contents is identity on a valid heap; validity excludes
shadowed duplicate lifetime identifiers. -/
theorem install_current (frame : CellFrame before id) (valid : before.valid = true) :
    frame.install frame.cell.cells = before := by
  have same : before.heap.replace id frame.cell = before.heap := by
    unfold Heap.replace
    refine (List.map_congr_left ?_).trans (List.map_id' _)
    rintro ⟨key, cell⟩ member
    by_cases selected : key = id
    · subst key
      have equal : cell = frame.cell := Option.some.inj
        ((lookup_of_mem_valid before id cell valid member).symm.trans frame.found)
      simp only [↓reduceIte, equal]
    · exact if_neg selected
  change { before with heap := before.heap.replace id frame.cell } = before
  rw [same]

theorem replace_twice (heap : Heap) (id : Nat) (first second : Allocation) :
    (heap.replace id first).replace id second = heap.replace id second := by
  induction heap with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨key, cell⟩
    by_cases same : key = id <;> simp [Heap.replace_cons, same, ih]

/-- Access checks depend on the allocation geometry, not its initialized cells.
Both successful accesses and rejection remain identical after installing cells. -/
theorem access_eq (frame : CellFrame before id) (cells : Cells) (offset : Nat) (layout : Layout) (write : Bool) :
    access (frame.install cells) ⟨id, offset⟩ layout write =
      (access before ⟨id, offset⟩ layout write).map (fun cell => { cell with cells }) := by
  simp only [access, frame.lookup, frame.found, frame.shaped]
  split
  · rfl
  · split <;> rfl

/-- Reuse the same admitted region after a cell update. Geometry and ownership
are unchanged; validity of the new cells is checked by the enclosing caller. -/
def replaced (frame : CellFrame before id) (cells : Cells) : CellFrame (frame.install cells) id where
  cell := { frame.cell with cells }
  layout := frame.layout
  found := frame.lookup cells
  shaped := frame.shaped
  admitted := by rw [frame.access_eq, frame.admitted]; rfl

theorem replaced_install (frame : CellFrame before id) (first second : Cells) :
    (frame.replaced first).install second = frame.install second := by
  simp only [replaced, install, replace_twice]

theorem load_outside (frame : CellFrame before id) (cells : Cells) (address : Address)
    (apart : address.allocation ≠ id) (mutable many : Bool) (type : Ty) :
    load (frame.install cells) (.pointer (.pointer mutable many type) address) =
      load before (.pointer (.pointer mutable many type) address) := by
  simp only [load, access, frame.outside cells address.allocation apart]

theorem field_access (frame : CellFrame before id) (cells : Cells) (offset : Nat) (child : Layout)
    (positive : 0 < child.bytes) (inside : offset + child.bytes ≤ frame.layout.bytes)
    (aligned : offset % child.alignment = 0) (divided : frame.layout.alignment % child.alignment = 0) :
    access (frame.install cells) ⟨id, offset⟩ child true = .ok { frame.cell with cells } := by
  rw [frame.access_eq]
  have selected := access_subregion before ⟨id, 0⟩ frame.layout child offset true frame.cell
    frame.admitted positive inside aligned divided
  simp only [Nat.zero_add] at selected
  rw [selected]
  rfl

theorem field_read_access (frame : CellFrame before id) (cells : Cells) (offset : Nat) (child : Layout)
    (positive : 0 < child.bytes) (inside : offset + child.bytes ≤ frame.layout.bytes)
    (aligned : offset % child.alignment = 0) (divided : frame.layout.alignment % child.alignment = 0) :
    access (frame.install cells) ⟨id, offset⟩ child false = .ok { frame.cell with cells } := by
  have written := frame.field_access cells offset child positive inside aligned divided
  unfold access at written ⊢
  simp only [frame.lookup, frame.shaped, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at written ⊢
  split at written
  · contradiction
  · exact written

/-- The original native load, with the complete access checks derived once.
There is no successful-read or initialized-value premise, so faults also agree. -/
theorem load_eq (frame : CellFrame before id) (cells : Cells) (offset : Nat) (wanted : Ty) (child : Layout)
    (shaped : wanted.layout = some child) (positive : 0 < child.bytes)
    (inside : offset + child.bytes ≤ frame.layout.bytes) (aligned : offset % child.alignment = 0)
    (divided : frame.layout.alignment % child.alignment = 0) :
    load (frame.install cells) (.pointer (.pointer true false wanted) ⟨id, offset⟩) =
      cells.read frame.cell.type offset wanted := by
  simp only [load, shaped, frame.field_read_access cells offset child positive inside aligned divided,
    bind, Except.bind, readCell]

/-- The original native store equals the same typed cell writer embedded in
this allocation. This covers every writer result, not only a supplied success. -/
theorem store_eq (frame : CellFrame before id) (cells : Cells) (offset : Nat) (value : Value) (child : Layout)
    (typed : value.hasType value.type = true) (shaped : value.type.layout = some child)
    (positive : 0 < child.bytes) (inside : offset + child.bytes ≤ frame.layout.bytes)
    (aligned : offset % child.alignment = 0) (divided : frame.layout.alignment % child.alignment = 0) :
    store (frame.install cells) (.pointer (.pointer true false value.type) ⟨id, offset⟩) value =
      (cells.write frame.cell.type offset value).map frame.install := by
  simp only [store, Bool.not_true, Bool.false_eq_true, ↓reduceIte, typed, shaped,
    frame.field_access cells offset child positive inside aligned divided, bind, Except.bind, writeCell]
  cases cells.write frame.cell.type offset value <;>
    simp only [Except.map, install, replace_twice]

/-- A successful ordinary allocation supplies the whole writable region. No
caller-selected allocation, permission or initialized cell is assumed. -/
theorem allocated (state : State) (owner : Ty) (layout : Layout) (value : Value) (after : State)
    (shaped : owner.layout = some layout) (positive : 0 < layout.bytes)
    (ran : allocate state owner = .ok (value, after)) :
    ∃ frame : CellFrame after state.nextId,
      frame.cell.type = owner ∧ frame.cell.cells = [] ∧ frame.layout = layout := by
  obtain ⟨actual, base, shape, _, eq⟩ := allocate_shape state owner value after ran
  have same : actual = layout := Option.some.inj (shape.symm.trans shaped)
  subst actual
  have valid := allocate_preserves_valid state owner value after ran
  have found : after.heap.lookup state.nextId = some ⟨base, owner, [], true, true⟩ := by
    rw [eq]; simp only [Heap.lookup_cons, ↓reduceIte]
  exact ⟨of_valid after state.nextId _ layout valid found shaped positive rfl, rfl, rfl, rfl⟩

/-- Reserve a local and evaluate its typed-cell body in the checked region.
Failure keeps the reached allocation history for the enclosing cleanup. -/
def create (state : State) (owner : Ty) (body : Cells → Except Fault (α × Cells)) :
    Except Fault (α × Nat) × State :=
  match allocate state owner with
  | .error fault => (.error fault, state)
  | .ok (_, allocated) =>
    match borrow allocated state.nextId owner body with
    | .error fault => (.error fault, allocated)
    | .ok (value, after) => (.ok (value, state.nextId), after)

theorem create_allocated (state : State) (owner : Ty) (layout : Layout) (pointer : Value) (after : State)
    (body : Cells → Except Fault (α × Cells)) (value : α) (cells : Cells)
    (shaped : owner.layout = some layout) (positive : 0 < layout.bytes)
    (allocated : allocate state owner = .ok (pointer, after))
    (ran : body [] = .ok (value, cells)) (typed : cells.valid owner = true) :
    ∃ frame : CellFrame after state.nextId,
      frame.cell.type = owner ∧ frame.layout = layout ∧
      create state owner body = (.ok (value, state.nextId), frame.install cells) := by
  obtain ⟨frame, type, empty, shape⟩ := CellFrame.allocated state owner layout pointer after shaped positive allocated
  have borrowed := frame.borrow_eq body value cells (empty ▸ ran) (type ▸ typed)
  rw [type] at borrowed
  exact ⟨frame, type, shape, by simp only [create, allocated, borrowed]⟩

end CellFrame
end Compiler.ZigAir.Memory
