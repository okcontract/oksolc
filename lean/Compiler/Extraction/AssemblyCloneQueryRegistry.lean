/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyCloneRegistry
import Compiler.Extraction.AssemblyCloneQuery
import Compiler.Extraction.RepresentativeFirstRegistry
import Compiler.Extraction.RepresentativeBorrowedQuery

namespace Compiler.Extraction.AssemblyClone.NativeFields
open Compiler.ZigAir.Memory Compiler.Algebraic
open Compiler.Extraction.Memory.Arguments.Normalization
open RepresentativeArray

/-- The actual spare append supplies the extended registry/vector and native
query correspondence together. Existing rows and the created clone retain exact
item/argument residency. Final registry contents, query acceptance and Good are
all conclusions; the new row's initial residency comes from created_resident. -/
theorem Installed.spare_registered_query {before ready : Session σ} (installed : Installed allocator object copied before ready)
    (runtimeSafety : Bool) (owner lifetime capacity : Nat) (ownerCell backing : Allocation)
    (cells : List Storage.Cell) (logical : Storage.Cell) (allocate : RegionAllocation.Allocator σ)
    (address : logical.itemAddress = object) (item : logical.item = copied.item)
    (domain : (copied.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (ownerFound : ready.memory.heap.lookup owner = some ownerCell) (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety)
    (ownerWritable : ownerCell.writable = true)
    (backingFound : ready.memory.heap.lookup lifetime = some backing) (backingTyped : backing.type = .array capacity Expression.allocationType)
    (backingWritable : backing.writable = true)
    (itemsRead : readItems ready.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType ⟨lifetime, 0⟩ cells.length))
    (capacityRead : readField ready.memory (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 capacity)))
    (registered : Memory.Vector allocator ready.heap lifetime cells)
    (represented : DescriptorRelation.Prefix ready.memory lifetime cells)
    (oldItems : ∀ cell ∈ cells, ∃ allocation, ready.memory.heap.lookup cell.itemAddress = some allocation ∧
      allocation.type = AssemblyItem.viewType ∧ Operation.Item ready.memory cell)
    (oldResident : Memory.GraphResident allocator ready.heap cells) (resident : Memory.Resident allocator ready.heap logical)
    (spare : cells.length < capacity) (room : cells.length < 2 ^ 32 - 1) (argumentsValid : logical.arguments.length < addressLimit) :
    ∃ after : Session σ,
      Append.Execution.ownerRun runtimeSafety ready.memory ⟨owner, 0⟩ ⟨logical.itemAddress, 0⟩ ⟨logical.argumentsAddress, 0⟩
        logical.arguments.length (Storage.idFor cells).toNat logical.sequence.toNat allocate ready.effects =
        ((.ok (some ()), after.memory), after.effects) ∧
      after.heap = Memory.write ready.heap lifetime (some ⟨allocator, .representatives (cells ++ [logical])⟩) ∧
      after.effects = ready.effects ∧ Valid after ∧ Memory.Vector allocator after.heap lifetime (cells ++ [logical]) ∧
      readHeader after.memory (Owner.headerAddress ⟨owner, 0⟩) =
        .ok (.slice itemsType ⟨lifetime, 0⟩ (cells.length + 1), .scalar (.int false 64 capacity)) ∧
      DescriptorRelation.Prefix after.memory lifetime (cells ++ [logical]) ∧
      Memory.GraphResident allocator after.heap (cells ++ [logical]) ∧
      OwnedCall.BorrowedQuery.Native.AcceptedQueries allocator (Owner.headerAddress ⟨owner, 0⟩) (cells ++ [logical]) after := by
  obtain ⟨after, executed, heap, effects, valid, vector, header, rows, _, _⟩ := DescriptorRelation.spare_registered
    runtimeSafety ready allocator owner lifetime capacity ownerCell backing cells logical allocate installed.valid
    ownerFound ownerTyped ownerWritable backingFound backingTyped backingWritable itemsRead capacityRead registered represented spare room argumentsValid
  obtain ⟨memory, queried, _, _, queries⟩ := installed.spare_query runtimeSafety owner lifetime capacity ownerCell backing cells logical allocate
    address item domain ownerFound ownerTyped ownerWritable backingFound backingTyped backingWritable itemsRead capacityRead represented oldItems spare room argumentsValid
  have same : after.memory = memory := congrArg (fun result => result.1.2) (executed.symm.trans queried)
  have residentAfter : Memory.GraphResident allocator after.heap (cells ++ [logical]) := by
    intro cell member
    have live : Memory.Resident allocator ready.heap cell := by
      rcases List.mem_append.mp member with old | new
      · exact oldResident cell old
      · exact (List.mem_singleton.mp new).symm ▸ resident
    rw [heap]
    exact Memory.resident_vector_write allocator ready.heap cell live lifetime cells registered _
  refine ⟨after, executed, heap, effects, valid, vector, ?_, rows, residentAfter, ?_⟩
  · simpa only [List.length_append, List.length_singleton] using header
  · exact OwnedCall.BorrowedQuery.Native.of_resident allocator (Owner.headerAddress ⟨owner, 0⟩) (cells ++ [logical]) after
      valid residentAfter (same.symm ▸ queries)

/-- First allocation registers the actual fresh backing under the selected
allocator. The created clone's residency survives that fresh write, and the
same reached session supplies all native query results and accepted borrows. -/
theorem Installed.first_registered_query {before ready : Session σ} (installed : Installed allocator object copied before ready)
    (runtimeSafety : Bool) (owner : Nat) (ownerCell : Allocation) (sentinel : Address) (logical : Storage.Cell)
    (base : Nat) (allocate : Backing.Registry.Allocate σ) (reached : σ)
    (address : logical.itemAddress = object) (item : logical.item = copied.item)
    (domain : (copied.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (ownerFound : ready.memory.heap.lookup owner = some ownerCell) (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety)
    (ownerWritable : ownerCell.writable = true)
    (itemsRead : readItems ready.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType sentinel 0))
    (capacityRead : readField ready.memory (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 0)))
    (resident : Memory.Resident allocator ready.heap logical) (argumentsValid : logical.arguments.length < addressLimit)
    (response : allocate allocator 160 8 ready.effects = (some base, reached)) (fits : RegionAllocation.Fits ready.memory ⟨160, 8⟩ base)
    (unlocked : Owner.NativeLock.checkHeader ready.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok ()) :
    ∃ after : Session σ,
      Append.Execution.ownerRun runtimeSafety ready.memory ⟨owner, 0⟩ ⟨logical.itemAddress, 0⟩ ⟨logical.argumentsAddress, 0⟩
        logical.arguments.length 0 logical.sequence.toNat (allocate allocator) ready.effects = ((.ok (some ()), after.memory), after.effects) ∧
      after.heap = Memory.write ready.heap ready.memory.nextId (some ⟨allocator, .representatives [logical]⟩) ∧
      after.effects = reached ∧ Valid after ∧ Memory.Vector allocator after.heap ready.memory.nextId [logical] ∧
      readHeader after.memory (Owner.headerAddress ⟨owner, 0⟩) =
        .ok (.slice itemsType ⟨ready.memory.nextId, 0⟩ 1, .scalar (.int false 64 5)) ∧
      DescriptorRelation.Prefix after.memory ready.memory.nextId [logical] ∧
      Memory.GraphResident allocator after.heap [logical] ∧
      OwnedCall.BorrowedQuery.Native.AcceptedQueries allocator (Owner.headerAddress ⟨owner, 0⟩) [logical] after := by
  obtain ⟨after, executed, heap, effects, valid, vector, _, header, rows, _, _, _, retained⟩ := DescriptorRelation.first_registered
    runtimeSafety ready allocator owner ownerCell sentinel logical base allocate reached installed.valid
    ownerFound ownerTyped ownerWritable itemsRead capacityRead argumentsValid response fits unlocked
  obtain ⟨memory, queried, _, _, queries⟩ := installed.first_query runtimeSafety owner ownerCell sentinel logical base (allocate allocator) reached
    address item domain ownerFound ownerTyped ownerWritable itemsRead capacityRead argumentsValid response fits unlocked
  have same : after.memory = memory := congrArg (fun result => result.1.2) (executed.symm.trans queried)
  have residentAfter : Memory.GraphResident allocator after.heap [logical] := by
    intro cell member
    exact (List.mem_singleton.mp member).symm ▸ retained logical resident
  refine ⟨after, executed, heap, effects, valid, vector, header, rows, residentAfter, ?_⟩
  exact OwnedCall.BorrowedQuery.Native.of_resident allocator (Owner.headerAddress ⟨owner, 0⟩) [logical] after
    valid residentAfter (same.symm ▸ queries)

end Compiler.Extraction.AssemblyClone.NativeFields
