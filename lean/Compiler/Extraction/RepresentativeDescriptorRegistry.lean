/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeDescriptorAppend

namespace Compiler.Extraction.RepresentativeArray.DescriptorRelation
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

/-- Common session frame for the actual owner executor. Callers derive shape
preservation from their reached capacity branch; the registered argument frame
comes from the existing native parent-borrow theorem, not from shape alone. -/
theorem owner_session_of_shape (runtimeSafety : Bool) (before : Session σ) (owner : Nat) (ownerCell : Allocation)
    (item arguments : Address) (length : Nat) (id sequence : Int) (allocate : RegionAllocation.Allocator σ)
    (valid : Valid before) (ownerFound : before.memory.heap.lookup owner = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety)
    (shape : before.memory.heap.RetainsShape
      (Append.Execution.ownerRun runtimeSafety before.memory ⟨owner, 0⟩ item arguments length id sequence allocate before.effects).1.2.heap) :
    let outcome := Append.Execution.ownerRun runtimeSafety before.memory ⟨owner, 0⟩ item arguments length id sequence allocate before.effects
    Valid ({before with memory := outcome.1.2, effects := outcome.2} : Session σ) := by
  have selected := Owner.root_header_pointer runtimeSafety before.memory owner ownerCell true valid.memory ownerFound ownerTyped
  refine ⟨?_, ?_, valid.injected.retained shape⟩
  · simpa only [Append.Execution.ownerRun, Append.Execution.ownerWithCapacity, selected, Append.Execution.run] using Append.Execution.run_valid before.memory
      (Owner.headerAddress ⟨owner, 0⟩) item arguments length id sequence allocate before.effects valid.memory
  · intro allocator query values nonempty registered
    obtain ⟨⟨parent, found, typed, writable, persistent⟩, represented⟩ := valid.related allocator query values nonempty registered
    have kept := Append.Execution.owner_parent_borrow runtimeSafety before.memory owner ownerCell item arguments length id sequence
      allocate before.effects ⟨query, 0, values.length⟩ values values.length parent valid.memory ownerFound ownerTyped found typed represented
    exact ⟨⟨parent, kept.2.1, typed, writable, persistent⟩, kept.2.2.1⟩

/-- Lift the reached spare append into the existing session without changing
the logical registry. All outcomes retain registered argument contents and
persistent lifetime injection, even when the new descriptor is only partial. -/
theorem spare_session (runtimeSafety : Bool) (before : Session σ) (owner lifetime capacity : Nat)
    (ownerCell : Allocation) (cells : List Storage.Cell) (item arguments : Address) (length : Nat) (id sequence : Int)
    (allocate : RegionAllocation.Allocator σ) (valid : Valid before)
    (ownerFound : before.memory.heap.lookup owner = some ownerCell) (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety)
    (itemsRead : readItems before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType ⟨lifetime, 0⟩ cells.length))
    (capacityRead : readField before.memory (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 capacity)))
    (spare : cells.length < capacity) (bounded : Append.nextLength cells.length < addressLimit) :
    let outcome := Append.Execution.ownerRun runtimeSafety before.memory ⟨owner, 0⟩ item arguments length id sequence allocate before.effects
    Valid ({before with memory := outcome.1.2, effects := outcome.2} : Session σ) := by
  have selected := Owner.root_header_pointer runtimeSafety before.memory owner ownerCell true valid.memory ownerFound ownerTyped
  have lengthRead := Append.Execution.owner_length_from_items runtimeSafety before.memory owner ownerCell ⟨lifetime, 0⟩ cells.length
    valid.memory ownerFound ownerTyped itemsRead
  have ensured := Capacity.ensure_unchanged before.memory (Owner.headerAddress ⟨owner, 0⟩) capacity (Append.nextLength cells.length)
    allocate before.effects bounded capacityRead (by simp only [Append.nextLength]; omega)
  have shape := after_capacity_shape before.memory before.memory (Owner.headerAddress ⟨owner, 0⟩) cells.length item arguments
    length id sequence allocate before.effects before.effects lengthRead bounded ensured valid.memory
  exact owner_session_of_shape runtimeSafety before owner ownerCell item arguments length id sequence allocate valid ownerFound ownerTyped
    (by simpa only [Append.Execution.ownerRun, Append.Execution.ownerWithCapacity, selected, Append.Execution.run] using shape)

/-- The registry update is the existing logical vector write, paired with the
same native append. It is a refinement witness, not another native operation.
Initial correspondence derives both the reached fields and the updated vector;
no final registry, successful query or final descriptor is assumed. Pointee
payloads, allocator-field identity and caller publication remain separate. -/
theorem spare_registered (runtimeSafety : Bool) (before : Session σ) (allocator owner lifetime capacity : Nat)
    (ownerCell backing : Allocation) (cells : List Storage.Cell) (cell : Storage.Cell)
    (allocate : RegionAllocation.Allocator σ) (valid : Valid before)
    (ownerFound : before.memory.heap.lookup owner = some ownerCell) (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety)
    (ownerWritable : ownerCell.writable = true)
    (backingFound : before.memory.heap.lookup lifetime = some backing) (backingTyped : backing.type = .array capacity Expression.allocationType)
    (backingWritable : backing.writable = true)
    (itemsRead : readItems before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType ⟨lifetime, 0⟩ cells.length))
    (capacityRead : readField before.memory (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 capacity)))
    (registered : Compiler.Extraction.Memory.Vector allocator before.heap lifetime cells)
    (represented : Prefix before.memory lifetime cells) (spare : cells.length < capacity) (room : cells.length < 2 ^ 32 - 1)
    (argumentsValid : cell.arguments.length < addressLimit) :
    ∃ after : Session σ,
      Append.Execution.ownerRun runtimeSafety before.memory ⟨owner, 0⟩ ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩
        cell.arguments.length (Storage.idFor cells).toNat cell.sequence.toNat allocate before.effects =
        ((.ok (some ()), after.memory), after.effects) ∧
      after.heap = Compiler.Extraction.Memory.write before.heap lifetime (some ⟨allocator, .representatives (cells ++ [cell])⟩) ∧
      after.effects = before.effects ∧ Valid after ∧
      Compiler.Extraction.Memory.Vector allocator after.heap lifetime (cells ++ [cell]) ∧
      readHeader after.memory (Owner.headerAddress ⟨owner, 0⟩) =
        .ok (.slice itemsType ⟨lifetime, 0⟩ (cells ++ [cell]).length, .scalar (.int false 64 capacity)) ∧
      Prefix after.memory lifetime (cells ++ [cell]) ∧
      (∀ id, representativeFields after.memory (Owner.headerAddress ⟨owner, 0⟩) id =
        .ok ((Storage.representativeProgram.run (cells ++ [cell]) id).map (values id.toNat))) ∧
      (∀ previous ∈ cells, Compiler.Extraction.Memory.Resident allocator before.heap previous →
        Compiler.Extraction.Memory.Resident allocator after.heap previous) := by
  obtain ⟨memory, executed, _, shape, header, extended, _, _, queries⟩ := spare_append runtimeSafety before.memory
    owner lifetime capacity ownerCell backing cells cell allocate before.effects valid.memory ownerFound ownerTyped ownerWritable
    backingFound backingTyped backingWritable itemsRead capacityRead represented spare room argumentsValid
  have sessionValid := spare_session runtimeSafety before owner lifetime capacity ownerCell cells ⟨cell.itemAddress, 0⟩
    ⟨cell.argumentsAddress, 0⟩ cell.arguments.length (Storage.idFor cells).toNat cell.sequence.toNat allocate valid ownerFound ownerTyped
    itemsRead capacityRead spare (Append.nextLength_bounded before.memory lifetime capacity cells.length backing valid.memory backingFound backingTyped spare)
  rw [executed] at sessionValid
  obtain ⟨oldBacking, oldFound, persistent⟩ := valid.injected lifetime _ registered
  have same := Option.some.inj (oldFound.symm.trans backingFound)
  subst oldBacking
  obtain ⟨finalBacking, finalFound, sameShape⟩ := shape lifetime backing backingFound
  let after : Session σ := { before with
    memory := memory
    heap := Compiler.Extraction.Memory.write before.heap lifetime (some ⟨allocator, .representatives (cells ++ [cell])⟩) }
  refine ⟨after, executed, rfl, rfl, ?_, ?_, header, extended, queries, ?_⟩
  · exact Backing.Registry.vector_write_valid {before with memory} allocator lifetime finalBacking (cells ++ [cell])
      sessionValid finalFound (sameShape.2.2.2.trans persistent)
  · exact Compiler.Extraction.Memory.write_same _ _ _
  · intro previous _ resident
    exact Compiler.Extraction.Memory.resident_vector_write allocator before.heap previous resident lifetime cells registered _

end Compiler.Extraction.RepresentativeArray.DescriptorRelation
