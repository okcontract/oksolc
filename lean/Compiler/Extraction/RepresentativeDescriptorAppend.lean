/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeDescriptorAppendFrame

namespace Compiler.Extraction.RepresentativeArray.DescriptorRelation
open Compiler.ZigAir.Memory
open Compiler.Algebraic

/-- The complete captured-owner spare append derives the extended descriptor
relation and every subsequent lookup. Initial header/backing geometry and the
old relation are compiler preconditions; final initialization is a conclusion. -/
theorem spare_append (runtimeSafety : Bool) (state : State) (owner lifetime capacity : Nat) (ownerCell backing : Allocation)
    (cells : List Storage.Cell) (cell : Storage.Cell) (allocate : RegionAllocation.Allocator σ) (effects : σ)
    (initial : state.valid = true) (ownerFound : state.heap.lookup owner = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety) (ownerWritable : ownerCell.writable = true)
    (backingFound : state.heap.lookup lifetime = some backing) (backingTyped : backing.type = .array capacity Expression.allocationType)
    (backingWritable : backing.writable = true)
    (itemsRead : readItems state (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType ⟨lifetime, 0⟩ cells.length))
    (capacityRead : readField state (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 capacity)))
    (represented : Prefix state lifetime cells) (spare : cells.length < capacity) (room : cells.length < 2 ^ 32 - 1)
    (argumentsValid : cell.arguments.length < addressLimit) :
    ∃ after, Append.Execution.ownerRun runtimeSafety state ⟨owner, 0⟩ ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩
        cell.arguments.length (Storage.idFor cells).toNat cell.sequence.toNat allocate effects = ((.ok (some ()), after), effects) ∧
      after.valid = true ∧ state.heap.RetainsShape after.heap ∧
      readHeader after (Owner.headerAddress ⟨owner, 0⟩) =
        .ok (.slice itemsType ⟨lifetime, 0⟩ (cells ++ [cell]).length, .scalar (.int false 64 capacity)) ∧
      Prefix after lifetime (cells ++ [cell]) ∧ after.nextId = state.nextId ∧ after.nextAddress = state.nextAddress ∧
      ∀ id, representativeFields after (Owner.headerAddress ⟨owner, 0⟩) id =
        .ok ((Storage.representativeProgram.run (cells ++ [cell]) id).map (values id.toNat)) := by
  obtain ⟨after, executed, valid, shape, header, fields, nextId, nextAddress, _⟩ :=
    Append.Execution.spare_verified runtimeSafety state owner lifetime capacity cells.length ownerCell backing
      ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩ cell.arguments.length (Storage.idFor cells).toNat cell.sequence.toNat allocate effects
      initial ownerFound ownerTyped ownerWritable backingFound backingTyped backingWritable itemsRead capacityRead spare argumentsValid
      (WordArray.number_valid (Storage.idFor cells)) (WordArray.number_valid cell.sequence)
  have apart := state.heap.lookup_ne_of_type_ne lifetime owner backing ownerCell backingFound ownerFound
    (by simp [backingTyped, ownerTyped, Owner.viewType])
  have old := owner_spare_frame runtimeSafety state owner lifetime capacity ownerCell cells ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩
    cell.arguments.length (Storage.idFor cells).toNat cell.sequence.toNat allocate effects initial ownerFound ownerTyped itemsRead capacityRead spare
    (Append.nextLength_bounded state lifetime capacity cells.length backing initial backingFound backingTyped spare) apart represented
  rw [executed] at old
  have newRow : Row after lifetime cells.length cell := by
    simpa only [Row, values, descriptorFields, List.map_cons, List.map_nil, Storage.idFor_toNat cells room] using fields
  have extended := extend after lifetime cells cell old newRow
  have finalHeader : readHeader after (Owner.headerAddress ⟨owner, 0⟩) =
      .ok (.slice itemsType ⟨lifetime, 0⟩ (cells ++ [cell]).length, .scalar (.int false 64 capacity)) := by
    simpa only [Append.nextLength, List.length_append, List.length_cons, List.length_nil, Nat.add_zero] using header
  obtain ⟨finalBacking, finalFound, finalShape⟩ := shape lifetime backing backingFound
  refine ⟨after, executed, valid, shape, finalHeader, extended, nextId, nextAddress, ?_⟩
  intro id
  exact query after _ lifetime capacity finalBacking (cells ++ [cell]) id valid (readHeader_items _ _ _ _ finalHeader)
    finalFound (finalShape.2.1.trans backingTyped) (finalShape.2.2.1.trans backingWritable)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) extended

/-- First append establishes the singleton relation from the actual allocated
backing and reached assignment. It requires no live empty sentinel or initial
descriptor contents, and retains the allocator's reached private effects. -/
theorem first_append (runtimeSafety : Bool) (state : State) (owner : Nat) (ownerCell : Allocation) (sentinel : Address)
    (cell : Storage.Cell) (base : Nat) (allocate : RegionAllocation.Allocator σ) (effects reached : σ)
    (initial : state.valid = true) (found : state.heap.lookup owner = some ownerCell)
    (typed : ownerCell.type = Owner.viewType runtimeSafety) (writable : ownerCell.writable = true)
    (items : readItems state (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType sentinel 0))
    (capacity : readField state (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 0)))
    (argumentsValid : cell.arguments.length < addressLimit)
    (response : allocate 160 8 effects = (some base, reached)) (fits : RegionAllocation.Fits state ⟨160, 8⟩ base)
    (unlocked : Owner.NativeLock.checkHeader state (Owner.headerAddress ⟨owner, 0⟩) = .ok ()) :
    ∃ after, Append.Execution.ownerRun runtimeSafety state ⟨owner, 0⟩ ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩
        cell.arguments.length 0 cell.sequence.toNat allocate effects = ((.ok (some ()), after), reached) ∧
      after.valid = true ∧ state.heap.RetainsShape after.heap ∧
      readHeader after (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType ⟨state.nextId, 0⟩ 1, .scalar (.int false 64 5)) ∧
      Prefix after state.nextId [cell] ∧ after.nextId = state.nextId + 1 ∧ after.nextAddress = max state.nextAddress (base + 160) ∧
      ∀ id, representativeFields after (Owner.headerAddress ⟨owner, 0⟩) id =
        .ok ((Storage.representativeProgram.run [cell] id).map (values id.toNat)) := by
  obtain ⟨after, executed, valid, shape, header, fields, nextId, nextAddress, _⟩ :=
    Append.Execution.first_verified runtimeSafety state owner ownerCell sentinel ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩
      cell.arguments.length 0 cell.sequence.toNat base allocate effects reached initial found typed writable items capacity argumentsValid
      (by decide) (WordArray.number_valid cell.sequence) response fits unlocked
  have newRow : Row after state.nextId 0 cell := by
    simpa only [Row, values, descriptorFields, List.map_cons, List.map_nil, Nat.zero_mul] using fields
  have represented : Prefix after state.nextId [cell] := extend after state.nextId [] cell (empty _ _) newRow
  have retained := first_continuation_backing runtimeSafety state owner ownerCell sentinel ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩
    cell.arguments.length 0 cell.sequence.toNat base allocate effects reached initial found typed writable items capacity response fits unlocked
  rw [executed] at retained
  obtain ⟨finalBacking, finalFound, finalShape⟩ := retained.2
  refine ⟨after, executed, valid, shape, header, represented, nextId, nextAddress, ?_⟩
  intro id
  exact query after _ state.nextId 5 finalBacking [cell] id valid (readHeader_items _ _ _ _ header)
    finalFound finalShape.2.1 finalShape.2.2.1 (by simp) represented

end Compiler.Extraction.RepresentativeArray.DescriptorRelation
