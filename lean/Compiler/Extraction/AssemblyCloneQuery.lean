/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyCloneFields
import Compiler.Extraction.AssemblyItemGraphFrame
import Compiler.Extraction.RepresentativeDescriptorAppend

namespace Compiler.Extraction.AssemblyClone.NativeFields
open Compiler.ZigAir.Memory Compiler.Algebraic
open RepresentativeArray

/-- Publish the installed clone through an actual spare-capacity append, then
derive every operation query from the extended descriptors and framed items.
The old native item relation is an initial precondition; the new one follows
from the same complete clone assignment, with no final query premise. -/
theorem Installed.spare_query {before ready : Compiler.Extraction.Memory.Arguments.Normalization.Session σ} (installed : Installed allocator object copied before ready)
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
    (represented : DescriptorRelation.Prefix ready.memory lifetime cells)
    (oldItems : ∀ cell ∈ cells, ∃ allocation, ready.memory.heap.lookup cell.itemAddress = some allocation ∧
      allocation.type = AssemblyItem.viewType ∧ Operation.Item ready.memory cell)
    (spare : cells.length < capacity) (room : cells.length < 2 ^ 32 - 1) (argumentsValid : logical.arguments.length < addressLimit) :
    ∃ after, Append.Execution.ownerRun runtimeSafety ready.memory ⟨owner, 0⟩ ⟨logical.itemAddress, 0⟩ ⟨logical.argumentsAddress, 0⟩
        logical.arguments.length (Storage.idFor cells).toNat logical.sequence.toNat allocate ready.effects = ((.ok (some ()), after), ready.effects) ∧
      after.valid = true ∧ DescriptorRelation.Prefix after lifetime (cells ++ [logical]) ∧
      ∀ id opcode, Operation.run after (Owner.headerAddress ⟨owner, 0⟩) id opcode =
        .ok ((Storage.operationProgram.run (cells ++ [logical]) id opcode).map (Option.map Operation.returned)) := by
  obtain ⟨after, executed, valid, shape, header, extended, _, _, _⟩ := DescriptorRelation.spare_append
    runtimeSafety ready.memory owner lifetime capacity ownerCell backing cells logical allocate ready.effects
    installed.valid.memory ownerFound ownerTyped ownerWritable backingFound backingTyped backingWritable
    itemsRead capacityRead represented spare room argumentsValid
  have initialItems : ∀ cell ∈ cells ++ [logical], ∃ allocation, ready.memory.heap.lookup cell.itemAddress = some allocation ∧
      allocation.type = AssemblyItem.viewType ∧ Operation.Item ready.memory cell := by
    intro cell member
    rcases List.mem_append.mp member with old | new
    · exact oldItems cell old
    · have same := List.mem_singleton.mp new
      subst cell
      obtain ⟨allocation, found, typed, _⟩ := installed.owned.2
      exact ⟨allocation, address.symm ▸ found, typed, installed.query logical address item domain⟩
  have finalItems : ∀ cell ∈ cells ++ [logical], Operation.Item after cell := by
    intro cell member
    obtain ⟨allocation, found, typed, query⟩ := initialItems cell member
    have framed := AssemblyItem.Query.append_frame runtimeSafety ready.memory owner ownerCell
      ⟨logical.itemAddress, 0⟩ ⟨logical.argumentsAddress, 0⟩ logical.arguments.length (Storage.idFor cells).toNat logical.sequence.toNat
      allocate ready.effects cell allocation installed.valid.memory ownerFound ownerTyped found typed query
    rw [executed] at framed
    exact framed.2
  obtain ⟨finalBacking, finalFound, finalShape⟩ := shape lifetime backing backingFound
  refine ⟨after, executed, valid, extended, fun id opcode => ?_⟩
  exact Operation.query after _ lifetime capacity finalBacking (cells ++ [logical]) id opcode valid
    (readHeader_items _ _ _ _ header) finalFound (finalShape.2.1.trans backingTyped) (finalShape.2.2.1.trans backingWritable)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) extended finalItems

/-- First growth allocates and publishes the actual backing before appending
the installed clone. All-ID/opcode agreement follows without an initial row,
live empty sentinel or final native observation. Allocator effects are retained. -/
theorem Installed.first_query {before ready : Compiler.Extraction.Memory.Arguments.Normalization.Session σ} (installed : Installed allocator object copied before ready)
    (runtimeSafety : Bool) (owner : Nat) (ownerCell : Allocation) (sentinel : Address) (logical : Storage.Cell)
    (base : Nat) (allocate : RegionAllocation.Allocator σ) (reached : σ)
    (address : logical.itemAddress = object) (item : logical.item = copied.item)
    (domain : (copied.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (ownerFound : ready.memory.heap.lookup owner = some ownerCell) (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety)
    (ownerWritable : ownerCell.writable = true)
    (itemsRead : readItems ready.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType sentinel 0))
    (capacityRead : readField ready.memory (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 0)))
    (argumentsValid : logical.arguments.length < addressLimit)
    (response : allocate 160 8 ready.effects = (some base, reached)) (fits : RegionAllocation.Fits ready.memory ⟨160, 8⟩ base)
    (unlocked : Owner.NativeLock.checkHeader ready.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok ()) :
    ∃ after, Append.Execution.ownerRun runtimeSafety ready.memory ⟨owner, 0⟩ ⟨logical.itemAddress, 0⟩ ⟨logical.argumentsAddress, 0⟩
        logical.arguments.length 0 logical.sequence.toNat allocate ready.effects = ((.ok (some ()), after), reached) ∧
      after.valid = true ∧ DescriptorRelation.Prefix after ready.memory.nextId [logical] ∧
      ∀ id opcode, Operation.run after (Owner.headerAddress ⟨owner, 0⟩) id opcode =
        .ok ((Storage.operationProgram.run [logical] id opcode).map (Option.map Operation.returned)) := by
  obtain ⟨after, executed, valid, _, header, extended, _, _, _⟩ := DescriptorRelation.first_append
    runtimeSafety ready.memory owner ownerCell sentinel logical base allocate ready.effects reached installed.valid.memory
    ownerFound ownerTyped ownerWritable itemsRead capacityRead argumentsValid response fits unlocked
  obtain ⟨allocation, found, typed, _⟩ := installed.owned.2
  have framed := AssemblyItem.Query.append_frame runtimeSafety ready.memory owner ownerCell
    ⟨logical.itemAddress, 0⟩ ⟨logical.argumentsAddress, 0⟩ logical.arguments.length 0 logical.sequence.toNat
    allocate ready.effects logical allocation installed.valid.memory ownerFound ownerTyped (address.symm ▸ found) typed
    (installed.query logical address item domain)
  rw [executed] at framed
  have retained := DescriptorRelation.first_continuation_backing runtimeSafety ready.memory owner ownerCell sentinel
    ⟨logical.itemAddress, 0⟩ ⟨logical.argumentsAddress, 0⟩ logical.arguments.length 0 logical.sequence.toNat base allocate ready.effects reached
    installed.valid.memory ownerFound ownerTyped ownerWritable itemsRead capacityRead response fits unlocked
  rw [executed] at retained
  obtain ⟨finalBacking, finalFound, finalShape⟩ := retained.2
  refine ⟨after, executed, valid, extended, fun id opcode => ?_⟩
  exact Operation.query after _ ready.memory.nextId 5 finalBacking [logical] id opcode valid
    (readHeader_items _ _ _ _ header) finalFound finalShape.2.1 finalShape.2.2.1 (by simp) extended
    (fun cell member => (List.mem_singleton.mp member).symm ▸ framed.2)

end Compiler.Extraction.AssemblyClone.NativeFields
