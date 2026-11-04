/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeRegisteredGrowthAppendProofs

namespace Compiler.Extraction.RepresentativeArray.Append.Registered
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

/-- At zero capacity both adapters retain the exact input heaps on allocator
refusal. Empty storage never calls remap or release, regardless of the sentinel
or callbacks. Descriptor operands are not evaluated after allocation OOM. -/
theorem first_refused (runtimeSafety : Bool) (calls : Growth.Registered.Callbacks σ)
    (allocate : Backing.Registry.Allocate σ) (allocator owner : Nat)
    (before : Session σ) (ownerCell : Allocation) (sentinel : Address)
    (cell : Storage.Cell) (effects : σ)
    (valid : Valid before) (found : before.memory.heap.lookup owner = some ownerCell)
    (typed : ownerCell.type = Owner.viewType runtimeSafety)
    (items : readItems before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType sentinel 0))
    (count : readField before.memory (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 0)))
    (response : allocate allocator 160 8 before.effects = (none, effects))
    (unlocked : Owner.NativeLock.checkHeader before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok ()) :
    run runtimeSafety allocate allocator owner [] cell before = (.ok false, { before with effects }) ∧
      runWithGrowth calls runtimeSafety allocate allocator owner [] cell before = (.ok false, { before with effects }) := by
  have pure := (DescriptorRelation.first_registry_oom runtimeSafety before owner ownerCell sentinel
    ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩ cell.arguments.length
    (Storage.idFor []).toNat cell.sequence.toNat (allocate allocator) effects valid found typed items count response unlocked).1
  have pointer := readItemsData_from_loaded runtimeSafety before.memory owner ownerCell sentinel 0 valid.memory found typed items
  have saved := allocatedSlice_empty before.memory (Owner.headerAddress ⟨owner, 0⟩) sentinel pointer count
  have prepared := Growth.prepare_growing before.memory (Owner.headerAddress ⟨owner, 0⟩) sentinel 0 5 0
    (by decide) (by decide) count saved unlocked
  have failed := Backing.Fallback.oom_verified allocate calls.release allocator (Owner.headerAddress ⟨owner, 0⟩)
    sentinel 0 5 before effects valid.memory (by decide) (by decide) response
  have ensured : Capacity.Registered.ensure calls allocate allocator (Owner.headerAddress ⟨owner, 0⟩) 1 before =
      (.ok none, { before with effects }) := by
    rw [Capacity.Registered.growing calls allocate allocator 0 1 _ before (by decide) count (by decide),
      Capacity.first_capacity_checked]
    simp only [Growth.Registered.run, prepared,
      Remap.empty_old calls.remap calls.release allocator 5 sentinel before (by decide) (by decide), failed]
  have selected := Owner.root_header_pointer runtimeSafety before.memory owner ownerCell true valid.memory found typed
  have length := Execution.owner_length_from_items runtimeSafety before.memory owner ownerCell sentinel 0 valid.memory found typed items
  constructor
  · simp only [run, pure]
  · simp only [runWithGrowth, Execution.ownerWithCapacity, selected, Execution.runWithCapacity, length,
      Int.toNat_natCast, nextLength, Nat.zero_add, if_neg (by decide : ¬1 ≥ addressLimit), growingCapacity, ensured, Except.mapError]

end Compiler.Extraction.RepresentativeArray.Append.Registered
