/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeDescriptorRelation
import Compiler.Extraction.RepresentativeFallbackProofs

namespace Compiler.Extraction.RepresentativeArray.DescriptorRelation
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

private theorem writeFields_read_frame (fields : List (Nat × Value)) (before : State) (lifetime index other offset : Nat)
    (type : Ty) (readSlot : (offset, type) ∈ expressionSlots)
    (declared : ∀ slot ∈ fields, (slot.1, slot.2.type) ∈ expressionSlots) (apart : other ≠ index) :
    Expression.readField (writeFields before lifetime index fields).2 false ⟨lifetime, other * 32⟩ offset =
      Expression.readField before false ⟨lifetime, other * 32⟩ offset := by
  induction fields generalizing before with
  | nil => rfl
  | cons slot tail ih =>
    rcases slot with ⟨fieldOffset, value⟩
    simp only [writeFields]
    cases stored : store before (.pointer (.pointer true false value.type) ⟨lifetime, index * 32 + fieldOffset⟩) value with
    | error fault => rfl
    | ok middle =>
      exact (ih middle (fun slot member => declared slot (List.mem_cons_of_mem _ member))).trans
        (Copy.readField_after_slot_store before middle lifetime lifetime index other fieldOffset offset type value.type value
          readSlot (declared (fieldOffset, value) (by simp)) stored (Or.inr (Or.inl apart)))

/-- Every reached initialization prefix preserves older descriptor rows, even
on rejection. The proof reuses the copy module's captured-slot separation. -/
theorem initialization_frame (before : State) (lifetime index other : Nat) (item arguments : Address)
    (length : Nat) (id sequence : Int) (apart : other ≠ index) :
    Expression.readFields (initializeFieldsReached before lifetime index item arguments length id sequence).2 false ⟨lifetime, other * 32⟩ =
      Expression.readFields before false ⟨lifetime, other * 32⟩ := by
  apply Copy.readFields_eq_of_slots
  intro slot member
  apply writeFields_read_frame _ before lifetime index other slot.1 slot.2 member _ apart
  intro field present
  simp only [descriptorFields, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl
  all_goals dsimp only [Value.type, Compiler.ZigAir.Scalar.Value.type]; decide

/-- Writing the next descriptor extends the relation to the existing logical
cell list. Old rows are framed, the source-generated ID is the old length, and
all new fields follow from the actual initialization. Header publication and
pointee/registry correspondence are separate obligations. -/
theorem initialize_prefix (before : State) (lifetime capacity : Nat) (backing : Allocation)
    (cells : List Storage.Cell) (cell : Storage.Cell) (valid : before.valid = true)
    (found : before.heap.lookup lifetime = some backing) (typed : backing.type = .array capacity Expression.allocationType)
    (writable : backing.writable = true) (represented : Prefix before lifetime cells)
    (spare : cells.length < capacity) (room : cells.length < 2 ^ 32 - 1) (argumentsValid : cell.arguments.length < addressLimit) :
    ∃ after, initializeFields before lifetime cells.length ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩
        cell.arguments.length (Storage.idFor cells).toNat cell.sequence.toNat = .ok after ∧
      after.valid = true ∧ before.heap.RetainsShape after.heap ∧ Prefix after lifetime (cells ++ [cell]) := by
  obtain ⟨after, initialized, finalValid, shape, row⟩ := initializeFields_verified before lifetime capacity cells.length backing
    ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩ cell.arguments.length (Storage.idFor cells).toNat cell.sequence.toNat
    valid found typed writable spare argumentsValid (WordArray.number_valid (Storage.idFor cells)) (WordArray.number_valid cell.sequence)
  have reached := (initializeFields_reached_iff before after lifetime cells.length ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩
    cell.arguments.length (Storage.idFor cells).toNat cell.sequence.toNat).mp initialized
  have newRow : Row after lifetime cells.length cell := by
    simpa only [Row, values, descriptorFields, List.map_cons, List.map_nil, Storage.idFor_toNat cells room] using row
  refine ⟨after, initialized, finalValid, shape, extend after lifetime cells cell ?_ newRow⟩
  intro index record entry
  have inside : index < cells.length := by
    by_cases inside : index < cells.length
    · exact inside
    · rw [List.getElem?_eq_none (by omega)] at entry
      contradiction
  have retained := initialization_frame before lifetime cells.length index ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩
    cell.arguments.length (Storage.idFor cells).toNat cell.sequence.toNat (by omega)
  rw [reached] at retained
  exact retained.trans (represented index record entry)

/-- Registered copying derives its initialized-read premises from the logical
descriptor relation, and preserves that same relation at the new lifetime.
The destination registry entry remains provisional. -/
theorem copy_verified (source target allocator capacity : Nat) (before : Session σ) (cells : List Storage.Cell)
    (valid : Valid before) (destination : Backing.Release.Owned allocator ⟨target, 0⟩ capacity before)
    (extent : cells.length ≤ capacity) (separate : cells.length = 0 ∨ source ≠ target)
    (represented : Prefix before.memory source cells) :
    ∃ after, Backing.RegisteredCopy.run source target cells.length before = (.ok (), after) ∧
      Valid after ∧ Backing.Release.Owned allocator ⟨target, 0⟩ capacity after ∧
      after.heap = before.heap ∧ after.effects = before.effects ∧ Prefix after.memory target cells := by
  obtain ⟨after, executed, finalValid, owned, heap, effects, _, _, _, fields⟩ :=
    Backing.RegisteredCopy.verified source target cells.length allocator capacity before valid destination extent separate
      (source_ready _ _ _ represented)
  exact ⟨after, executed, finalValid, owned, heap, effects, copied _ _ _ _ _ represented fields⟩

/-- Actual allocation through publication preserves the complete descriptor
relation and derives the new header. The saved old view remains evaluated;
this does not supply remap preservation or initialize logical registry cells. -/
theorem fallback_verified (runtimeSafety : Bool) (allocate : Backing.Registry.Allocate σ) (release : Backing.Release.External σ)
    (allocator owner source oldCapacity capacity base : Nat) (before : Session σ) (effects : σ) (ownerCell : Allocation)
    (cells : List Storage.Cell) (valid : Valid before) (ownerFound : before.memory.heap.lookup owner = some ownerCell)
    (ownerType : ownerCell.type = Owner.viewType runtimeSafety) (ownerWritable : ownerCell.writable = true)
    (sourceOwned : Backing.Release.Owned allocator ⟨source, 0⟩ oldCapacity before)
    (oldNonempty : oldCapacity ≠ 0) (nonempty : capacity ≠ 0) (size : capacity * 32 < addressLimit)
    (extent : cells.length ≤ capacity)
    (response : allocate allocator (capacity * 32) 8 before.effects = (some base, effects))
    (fits : RegionAllocation.Fits before.memory ⟨capacity * 32, 8⟩ base)
    (loaded : readItems before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType ⟨source, 0⟩ cells.length))
    (represented : Prefix before.memory source cells) :
    ∃ after, Backing.Fallback.run allocate release allocator (Owner.headerAddress ⟨owner, 0⟩) ⟨source, 0⟩ oldCapacity capacity before =
        (.ok (some ()), after) ∧ Valid after ∧ Backing.Release.Owned allocator ⟨before.memory.nextId, 0⟩ capacity after ∧
      after.memory.heap.lookup source = none ∧
      readHeader after.memory (Owner.headerAddress ⟨owner, 0⟩) =
        .ok (.slice itemsType ⟨before.memory.nextId, 0⟩ cells.length, .scalar (.int false 64 capacity)) ∧
      Prefix after.memory before.memory.nextId cells ∧
      ∀ id, representativeFields after.memory (Owner.headerAddress ⟨owner, 0⟩) id =
        .ok ((Storage.representativeProgram.run cells id).map (values id.toNat)) := by
  obtain ⟨_, after, _, executed, finalValid, owned, _, _, _, _, dead, header, fields, _⟩ :=
    Backing.Fallback.verified runtimeSafety allocate release allocator owner source oldCapacity capacity cells.length base before effects ownerCell
      valid ownerFound ownerType ownerWritable sourceOwned oldNonempty nonempty size extent response fits loaded
      (source_ready _ _ _ represented)
  have preserved := copied _ _ _ _ _ represented fields
  have ownedAgain := owned
  obtain ⟨_, _, backing, found, typed, writable, _⟩ := ownedAgain
  exact ⟨after, executed, finalValid, owned, dead, header, preserved, fun id =>
    query after.memory _ before.memory.nextId capacity backing cells id finalValid.memory
      (readHeader_items _ _ _ _ header) found typed writable extent preserved⟩

end Compiler.Extraction.RepresentativeArray.DescriptorRelation
