/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryProofs

/-! Compositional laws for the executable heap operations. Successful stores
establish actual readback and preserve observations outside their write set.
These are model laws, not a native pointer/allocator refinement. -/
namespace Compiler.ZigAir.Memory

/-- The interpreted read's leaf footprint; unsupported arrays/records read no
leaves. This is a modeled-cell footprint, not a native byte-punning rule. -/
def Ty.readOffsets (wanted : Ty) (offset : Nat) : List Nat :=
  match wanted with
  | .slice .. => [offset, offset + 8]
  | .array .. | .record .. | .aggregate .. => []
  | _ => [offset]

/-- A valid stored value has exactly the leaf offsets read by its type. -/
theorem Value.leaf_offsets (value : Value) (offset : Nat) (valid : value.valid = true) :
    (value.leaves offset).map Prod.fst = value.type.readOffsets offset := by
  cases value with
  | scalar value | optionalScalar _ value | optionalObject _ _ value => rfl
  | pointer type address => cases type <;> simp_all [Value.valid, Value.leaves, Value.type, Ty.readOffsets]
  | slice type address length => cases type <;> simp_all [Value.valid, Value.leaves, Value.type, Ty.readOffsets]

theorem Cells.read_eq_of_lookup (before after : Cells) (owner : Ty) (offset : Nat) (wanted : Ty)
    (same : ∀ position ∈ wanted.readOffsets offset, after.lookup position = before.lookup position) :
    after.read owner offset wanted = before.read owner offset wanted := by
  cases wanted with
  | scalar type | optionalScalar type | optionalObject type _ =>
    have here := same offset (by simp [Ty.readOffsets])
    simp only [Cells.read, Cells.readLeaf, here]
  | pointer writable many child =>
    have here := same offset (by simp [Ty.readOffsets])
    simp only [Cells.read, Cells.readLeaf, here]
  | slice writable child =>
    have pointer := same offset (by simp [Ty.readOffsets])
    have length := same (offset + 8) (by simp [Ty.readOffsets])
    simp only [Cells.read, Cells.readLeaf, pointer, length]
  | array | record | aggregate => rfl

theorem Cells.fold_lookup_other (updates cells : Cells) (offset : Nat)
    (apart : ∀ entry ∈ updates, offset ≠ entry.1) :
    (updates.foldl (fun cells entry => cells.set entry.1 entry.2) cells).lookup offset = cells.lookup offset := by
  induction updates generalizing cells with
  | nil => rfl
  | cons entry tail ih =>
    change (tail.foldl _ (cells.set entry.1 entry.2)).lookup offset = cells.lookup offset
    rw [ih _ (fun item present => apart item (List.mem_cons_of_mem _ present))]
    exact cells.lookup_set_other entry.1 offset entry.2 (apart entry (by simp))

theorem Cells.read_frame (cells : Cells) (owner : Ty) (offset : Nat) (value : Value) (after : Cells)
    (readOffset : Nat) (readType : Ty) (success : cells.write owner offset value = .ok after)
    (apart : ∀ position ∈ readType.readOffsets readOffset, ∀ entry ∈ value.leaves offset, position ≠ entry.1) :
    after.read owner readOffset readType = cells.read owner readOffset readType := by
  rcases cells.write_success owner offset value after success with ⟨_, _, _, rfl⟩
  apply Cells.read_eq_of_lookup
  intro position present
  exact Cells.fold_lookup_other _ cells position (apart position present)

theorem Heap.lookup_replace (heap : Heap) (id : Nat) (before after : Allocation)
    (found : heap.lookup id = some before) : (heap.replace id after).lookup id = some after := by
  induction heap with
  | nil => simp [Heap.lookup] at found
  | cons entry tail ih =>
    rcases entry with ⟨key, cell⟩
    by_cases selected : key = id
    · subst key
      simp only [Heap.replace_cons, ite_true, Heap.lookup_cons]
    · simp only [Heap.lookup_cons, if_neg selected] at found
      simpa only [Heap.replace_cons, if_neg selected, Heap.lookup_cons, if_neg selected] using ih found

theorem writeCell_success (cell : Allocation) (offset : Nat) (value : Value) (after : Allocation)
    (success : writeCell cell offset value = .ok after) :
    ∃ contents, cell.cells.write cell.type offset value = .ok contents ∧ after = { cell with cells := contents } := by
  cases written : cell.cells.write cell.type offset value with
  | error fault => simp [writeCell, written, bind, Except.bind] at success
  | ok contents =>
    simp only [writeCell, written, bind, Except.bind, Except.ok.injEq] at success
    exact ⟨contents, rfl, success.symm⟩

theorem readCell_after_writeCell (cell : Allocation) (offset : Nat) (value : Value) (after : Allocation)
    (success : writeCell cell offset value = .ok after) : readCell after offset value.type = .ok value := by
  rcases writeCell_success cell offset value after success with ⟨contents, written, rfl⟩
  exact Cells.read_after_write cell.cells cell.type offset value contents written

/-- Successful store exposes the checked access and the exact heap update. No
assumption that the whole initial heap is well formed is needed for this law. -/
theorem store_success (state : State) (pointer value : Value) (after : State)
    (success : store state pointer value = .ok after) :
    ∃ many child address layout cell contents,
      pointer = .pointer (.pointer true many child) address ∧ value.hasType child = true ∧
      child.layout = some layout ∧ access state address layout true = .ok cell ∧
      cell.cells.write cell.type address.offset value = .ok contents ∧
      after = { state with heap := state.heap.replace address.allocation { cell with cells := contents } } := by
  unfold store at success
  split at success
  · rename_i actual writable many child address
    cases writable
    · simp at success
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at success
      split at success
      · contradiction
      · rename_i typed
        cases shaped : child.layout with
        | none => simp [shaped] at success
        | some layout =>
          simp only [shaped] at success
          cases accessed : access state address layout true with
          | error fault => simp [accessed, bind, Except.bind] at success
          | ok cell =>
            simp only [accessed, bind, Except.bind] at success
            cases written : writeCell cell address.offset value with
            | error fault => simp [written] at success
            | ok updated =>
              simp only [written, Except.ok.injEq] at success
              rcases writeCell_success cell address.offset value updated written with ⟨contents, contentsWritten, rfl⟩
              refine ⟨many, child, address, layout, cell, contents, rfl, by simpa using typed,
                shaped, accessed, contentsWritten, ?_⟩
              exact success.symm
  · contradiction

theorem access_write_read (state : State) (address : Address) (layout : Layout) (cell : Allocation)
    (success : access state address layout true = .ok cell) : access state address layout false = .ok cell := by
  rcases access_success_region state address layout true cell success with
    ⟨found, region, shaped, positive, regionBound, pointerBound, viewBound, aligned, _⟩
  have valid : ¬(cell.base = 0 ∨ cell.base + region.bytes > addressLimit ∨
      cell.base + address.offset ≥ addressLimit ∨ address.offset + layout.bytes > region.bytes ∨
      (cell.base + address.offset) % layout.alignment ≠ 0) := by omega
  simp [access, found, shaped, valid]

theorem access_read_write (state : State) (address : Address) (layout : Layout) (cell : Allocation)
    (readable : access state address layout false = .ok cell) (writable : cell.writable = true) :
    access state address layout true = .ok cell := by
  have found := (access_success_region state address layout false cell readable).1
  simpa only [access, found, writable, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte] using readable

theorem access_replace_cells (state : State) (address : Address) (layout : Layout) (write : Bool)
    (cell : Allocation) (contents : Cells) (found : state.heap.lookup address.allocation = some cell) :
    access { state with heap := state.heap.replace address.allocation { cell with cells := contents } }
      address layout write =
      match access state address layout write with
      | .ok old => .ok { old with cells := contents }
      | .error fault => .error fault := by
  have updated := Heap.lookup_replace state.heap address.allocation cell { cell with cells := contents } found
  simp only [access, found, updated]
  cases cell.type.layout with
  | none => rfl
  | some region =>
    dsimp only
    split <;> simp_all
    split <;> rfl

theorem load_after_store (state : State) (pointer value : Value) (after : State)
    (success : store state pointer value = .ok after) : load after pointer = .ok value := by
  rcases store_success state pointer value after success with
    ⟨many, child, address, layout, cell, contents, rfl, typed, shaped, accessed, written, rfl⟩
  have found := (access_success_region state address layout true cell accessed).1
  have readable := access_write_read state address layout cell accessed
  have updated := access_replace_cells state address layout false cell contents found
  rw [readable] at updated
  have typeEq : value.type = child := by
    simp only [Value.hasType, Bool.and_eq_true, decide_eq_true_eq] at typed
    exact typed.1
  have readback := Cells.read_after_write cell.cells cell.type address.offset value contents written
  simpa [load, shaped, updated, readCell, typeEq, bind, Except.bind] using readback

theorem load_alias_after_store (state : State) (writable many : Bool) (child : Ty) (address : Address)
    (value : Value) (after : State) (readWritable readMany : Bool)
    (success : store state (.pointer (.pointer writable many child) address) value = .ok after) :
    load after (.pointer (.pointer readWritable readMany child) address) = .ok value := by
  exact load_after_store state (.pointer (.pointer writable many child) address) value after success

theorem load_eq_of_lookup (before after : State) (writable many : Bool) (child : Ty) (address : Address)
    (same : after.heap.lookup address.allocation = before.heap.lookup address.allocation) :
    load after (.pointer (.pointer writable many child) address) =
      load before (.pointer (.pointer writable many child) address) := by
  simp only [load, access, same]

/-- Different declared allocation types establish separation in the same heap;
no independent-address assumption is needed. -/
theorem Heap.lookup_ne_of_type_ne (heap : Heap) (left right : Nat) (first second : Allocation)
    (leftFound : heap.lookup left = some first) (rightFound : heap.lookup right = some second)
    (different : first.type ≠ second.type) : left ≠ right := by
  intro same
  have cells : first = second := Option.some.inj (leftFound.symm.trans (same.symm ▸ rightFound))
  exact different (congrArg Allocation.type cells)

/-- Successful typed stores retain every unrelated allocation exactly. -/
theorem heap_after_store_other (state : State) (writable many : Bool) (child : Ty) (address : Address)
    (value : Value) (after : State)
    (success : store state (.pointer (.pointer writable many child) address) value = .ok after) :
    ∀ other, other ≠ address.allocation → after.heap.lookup other = state.heap.lookup other := by
  rcases store_success state _ value after success with
    ⟨_, _, _, _, _, contents, same, _, _, _, _, rfl⟩
  cases same
  intro other apart
  exact replace_other _ _ _ _ apart

/-- A store leaves every load in another allocation unchanged, including an
uninitialized, unsupported or invalid read's exact failure. -/
theorem load_other_after_store (state : State) (writable many : Bool) (child : Ty) (address : Address)
    (value : Value) (after : State) (readWritable readMany : Bool) (readType : Ty) (readAddress : Address)
    (success : store state (.pointer (.pointer writable many child) address) value = .ok after)
    (apart : readAddress.allocation ≠ address.allocation) :
    load after (.pointer (.pointer readWritable readMany readType) readAddress) =
      load state (.pointer (.pointer readWritable readMany readType) readAddress) :=
  load_eq_of_lookup state after readWritable readMany readType readAddress
    (heap_after_store_other state writable many child address value after success readAddress.allocation apart)

/-- The corresponding frame rule within an allocation compares all leaves of
both views, so distinct starting offsets alone do not establish independence. -/
theorem load_disjoint_after_store (state : State) (writable many : Bool) (child : Ty) (address : Address)
    (value : Value) (after : State) (readWritable readMany : Bool) (readType : Ty) (readOffset : Nat)
    (success : store state (.pointer (.pointer writable many child) address) value = .ok after)
    (apart : ∀ position ∈ readType.readOffsets readOffset, ∀ entry ∈ value.leaves address.offset, position ≠ entry.1) :
    load after (.pointer (.pointer readWritable readMany readType) ⟨address.allocation, readOffset⟩) =
      load state (.pointer (.pointer readWritable readMany readType) ⟨address.allocation, readOffset⟩) := by
  rcases store_success state _ value after success with
    ⟨_, _, _, layout, cell, contents, same, _, _, accessed, written, rfl⟩
  cases same
  have found := (access_success_region state address layout true cell accessed).1
  have framed := Cells.read_frame cell.cells cell.type address.offset value contents readOffset readType written apart
  cases shaped : readType.layout with
  | none => simp [load, shaped]
  | some readLayout =>
    have updated := access_replace_cells state ⟨address.allocation, readOffset⟩ readLayout false cell contents found
    simp only [load, shaped, updated, bind, Except.bind]
    cases checked : access state ⟨address.allocation, readOffset⟩ readLayout false with
    | error fault => rfl
    | ok readCell =>
      have sameCell : readCell = cell := Option.some.inj
        (((access_success_region state _ _ false readCell checked).1).symm.trans found)
      subst readCell
      exact framed

/-- Two scalar writes in one allocation observe either the overwritten value or
the framed first value. Both writes are checked; no non-aliasing assumption is
smuggled into the statement. -/
theorem load_after_two_scalar_stores (state middle after : State) (type : Scalar.Ty)
    (allocation left right : Nat) (first second : Scalar.Value)
    (firstWritten : store state (.pointer (.pointer true false (.scalar type)) ⟨allocation, left⟩)
      (.scalar first) = .ok middle)
    (secondWritten : store middle (.pointer (.pointer true false (.scalar type)) ⟨allocation, right⟩)
      (.scalar second) = .ok after) :
    load after (.pointer (.pointer true false (.scalar type)) ⟨allocation, left⟩) =
      .ok (.scalar (if left = right then second else first)) := by
  by_cases same : left = right
  · subst right
    simpa using load_after_store middle _ (.scalar second) after secondWritten
  · have framed := load_disjoint_after_store middle true false (.scalar type) ⟨allocation, right⟩
      (.scalar second) after true false (.scalar type) left secondWritten
      (by simpa [Ty.readOffsets, Value.leaves] using same)
    rw [framed, load_after_store state _ (.scalar first) middle firstWritten]
    simp [same]

end Compiler.ZigAir.Memory
