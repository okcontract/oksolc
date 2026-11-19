/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeDescriptorRegistry

namespace Compiler.Extraction.RepresentativeArray.DescriptorRelation
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

/-- The admitted first allocation and every subsequent append outcome preserve
the existing registry's argument contents and persistent lifetime injection.
The newly reached backing is not yet a published logical descriptor. -/
theorem first_session (runtimeSafety : Bool) (before : Session σ) (owner : Nat) (ownerCell : Allocation)
    (sentinel item arguments : Address) (length : Nat) (id sequence : Int) (base : Nat)
    (allocate : RegionAllocation.Allocator σ) (reached : σ) (valid : Valid before)
    (found : before.memory.heap.lookup owner = some ownerCell) (typed : ownerCell.type = Owner.viewType runtimeSafety)
    (writable : ownerCell.writable = true)
    (items : readItems before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType sentinel 0))
    (capacity : readField before.memory (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 0)))
    (response : allocate 160 8 before.effects = (some base, reached)) (fits : RegionAllocation.Fits before.memory ⟨160, 8⟩ base)
    (unlocked : Owner.NativeLock.checkHeader before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok ()) :
    let outcome := Append.Execution.ownerRun runtimeSafety before.memory ⟨owner, 0⟩ item arguments length id sequence allocate before.effects
    Valid ({before with memory := outcome.1.2, effects := outcome.2} : Session σ) :=
  owner_session_of_shape runtimeSafety before owner ownerCell item arguments length id sequence allocate valid found typed
    (first_continuation_backing runtimeSafety before.memory owner ownerCell sentinel item arguments length id sequence base
      allocate before.effects reached valid.memory found typed writable items capacity response fits unlocked).1

/-- Even a later descriptor rejection leaves releasable backing. The registry
owner selects the existing allocator-indexed callback. Register the derived
allocation with the empty provisional vector; no completed descriptor is
published by this ownership witness. -/
theorem first_reserved (runtimeSafety : Bool) (before : Session σ) (allocator owner : Nat) (ownerCell : Allocation)
    (sentinel item arguments : Address) (length : Nat) (id sequence : Int) (base : Nat)
    (allocate : Backing.Registry.Allocate σ) (reached : σ) (valid : Valid before)
    (found : before.memory.heap.lookup owner = some ownerCell) (typed : ownerCell.type = Owner.viewType runtimeSafety)
    (writable : ownerCell.writable = true)
    (items : readItems before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType sentinel 0))
    (capacity : readField before.memory (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 0)))
    (response : allocate allocator 160 8 before.effects = (some base, reached)) (fits : RegionAllocation.Fits before.memory ⟨160, 8⟩ base)
    (unlocked : Owner.NativeLock.checkHeader before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok ()) :
    let outcome := Append.Execution.ownerRun runtimeSafety before.memory ⟨owner, 0⟩ item arguments length id sequence (allocate allocator) before.effects
    let after : Session σ := { before with
      memory := outcome.1.2
      effects := outcome.2
      heap := Compiler.Extraction.Memory.write before.heap before.memory.nextId (some ⟨allocator, .representatives []⟩) }
    Valid after ∧ Compiler.Extraction.Memory.Vector allocator after.heap before.memory.nextId [] ∧
      Backing.Release.Owned allocator ⟨before.memory.nextId, 0⟩ 5 after := by
  have sessionValid := first_session runtimeSafety before owner ownerCell sentinel item arguments length id sequence base
    (allocate allocator) reached valid found typed writable items capacity response fits unlocked
  obtain ⟨_, backing, backingFound, shape⟩ := first_continuation_backing runtimeSafety before.memory owner ownerCell sentinel
    item arguments length id sequence base (allocate allocator) before.effects reached valid.memory found typed writable items capacity response fits unlocked
  refine ⟨Backing.Registry.register_valid _ allocator before.memory.nextId backing sessionValid backingFound shape.2.2.2,
    Compiler.Extraction.Memory.write_same _ _ _, ?_⟩
  exact ⟨rfl, ⟨[], Compiler.Extraction.Memory.write_same _ _ _⟩, backing, backingFound, shape.2.1, shape.2.2.1, shape.2.2.2⟩

/-- First append establishes a registered singleton at the lifetime derived
from the actual allocation response. Native execution, final descriptors,
full-capacity ownership and allocator effects are conclusions. The registry
write uses the same owner that selects the allocation callback. It remains a
logical refinement witness, adding no native operation or pointee payload/
native allocator-field correspondence. -/
theorem first_registered (runtimeSafety : Bool) (before : Session σ) (allocator owner : Nat) (ownerCell : Allocation)
    (sentinel : Address) (cell : Storage.Cell) (base : Nat) (allocate : Backing.Registry.Allocate σ) (reached : σ)
    (valid : Valid before) (found : before.memory.heap.lookup owner = some ownerCell)
    (typed : ownerCell.type = Owner.viewType runtimeSafety) (writable : ownerCell.writable = true)
    (items : readItems before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType sentinel 0))
    (capacity : readField before.memory (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 0)))
    (argumentsValid : cell.arguments.length < addressLimit)
    (response : allocate allocator 160 8 before.effects = (some base, reached)) (fits : RegionAllocation.Fits before.memory ⟨160, 8⟩ base)
    (unlocked : Owner.NativeLock.checkHeader before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok ()) :
    ∃ after : Session σ,
      Append.Execution.ownerRun runtimeSafety before.memory ⟨owner, 0⟩ ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩
        cell.arguments.length 0 cell.sequence.toNat (allocate allocator) before.effects = ((.ok (some ()), after.memory), after.effects) ∧
      after.heap = Compiler.Extraction.Memory.write before.heap before.memory.nextId (some ⟨allocator, .representatives [cell]⟩) ∧
      after.effects = reached ∧ Valid after ∧
      Compiler.Extraction.Memory.Vector allocator after.heap before.memory.nextId [cell] ∧
      Backing.Release.Owned allocator ⟨before.memory.nextId, 0⟩ 5 after ∧
      readHeader after.memory (Owner.headerAddress ⟨owner, 0⟩) =
        .ok (.slice itemsType ⟨before.memory.nextId, 0⟩ 1, .scalar (.int false 64 5)) ∧
      Prefix after.memory before.memory.nextId [cell] ∧
      after.memory.nextId = before.memory.nextId + 1 ∧ after.memory.nextAddress = max before.memory.nextAddress (base + 160) ∧
      (∀ id, representativeFields after.memory (Owner.headerAddress ⟨owner, 0⟩) id =
        .ok ((Storage.representativeProgram.run [cell] id).map (values id.toNat))) ∧
      (∀ previous, Compiler.Extraction.Memory.Resident allocator before.heap previous →
        Compiler.Extraction.Memory.Resident allocator after.heap previous) := by
  obtain ⟨memory, executed, _, _, header, represented, nextId, nextAddress, queries⟩ :=
    first_append runtimeSafety before.memory owner ownerCell sentinel cell base (allocate allocator) before.effects reached valid.memory
      found typed writable items capacity argumentsValid response fits unlocked
  have sessionValid := first_session runtimeSafety before owner ownerCell sentinel ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩
    cell.arguments.length 0 cell.sequence.toNat base (allocate allocator) reached valid found typed writable items capacity response fits unlocked
  rw [executed] at sessionValid
  have storage := first_continuation_backing runtimeSafety before.memory owner ownerCell sentinel ⟨cell.itemAddress, 0⟩
    ⟨cell.argumentsAddress, 0⟩ cell.arguments.length 0 cell.sequence.toNat base (allocate allocator) before.effects reached valid.memory
    found typed writable items capacity response fits unlocked
  rw [executed] at storage
  obtain ⟨backing, backingFound, shape⟩ := storage.2
  let after : Session σ := { before with
    memory := memory
    effects := reached
    heap := Compiler.Extraction.Memory.write before.heap before.memory.nextId (some ⟨allocator, .representatives [cell]⟩) }
  have vector : Compiler.Extraction.Memory.Vector allocator after.heap before.memory.nextId [cell] :=
    Compiler.Extraction.Memory.write_same _ _ _
  refine ⟨after, executed, rfl, rfl, ?_, vector, ?_, header, represented, nextId, nextAddress, queries, ?_⟩
  · exact Backing.Registry.vector_write_valid {before with memory := memory, effects := reached}
      allocator before.memory.nextId backing [cell] sessionValid backingFound shape.2.2.2
  · exact ⟨rfl, ⟨[cell], vector⟩, backing, backingFound, shape.2.1, shape.2.2.1, shape.2.2.2⟩
  · intro previous resident
    exact Compiler.Extraction.Memory.resident_fresh_write allocator before.heap previous resident before.memory.nextId
      (valid.injected.fresh valid.memory) _

/-- Allocator OOM creates no backing or registry entry and skips all descriptor
inputs. Its private effects remain reached; it is not a partial-row rejection. -/
theorem first_registry_oom (runtimeSafety : Bool) (before : Session σ) (owner : Nat) (ownerCell : Allocation)
    (sentinel item arguments : Address) (length : Nat) (id sequence : Int) (allocate : RegionAllocation.Allocator σ) (reached : σ)
    (valid : Valid before) (found : before.memory.heap.lookup owner = some ownerCell) (typed : ownerCell.type = Owner.viewType runtimeSafety)
    (items : readItems before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType sentinel 0))
    (capacity : readField before.memory (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 0)))
    (response : allocate 160 8 before.effects = (none, reached))
    (unlocked : Owner.NativeLock.checkHeader before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok ()) :
    Append.Execution.ownerRun runtimeSafety before.memory ⟨owner, 0⟩ item arguments length id sequence allocate before.effects =
      ((.ok none, before.memory), reached) ∧
    Valid ({before with effects := reached} : Session σ) ∧ before.heap before.memory.nextId = none := by
  exact ⟨Append.Execution.first_oom runtimeSafety before.memory owner ownerCell sentinel item arguments length id sequence
    allocate before.effects reached valid.memory found typed items capacity response unlocked,
    ⟨valid.memory, valid.related, valid.injected⟩, valid.injected.fresh valid.memory⟩

end Compiler.Extraction.RepresentativeArray.DescriptorRelation
