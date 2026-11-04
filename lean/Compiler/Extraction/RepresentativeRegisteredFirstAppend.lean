/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeRegisteredGrowthAppendProofs

namespace Compiler.Extraction.RepresentativeArray.Capacity.Registered
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

/-- At zero old capacity, remap and release skip their external callbacks.
Both capacity adapters reach the same native publication; the registered
adapter additionally records the fresh provisional vector. The sentinel is
arbitrary, including an offset or an alias of the fresh allocation identity. -/
theorem first_pair (runtimeSafety : Bool) (calls : Growth.Registered.Callbacks σ)
    (allocate : Backing.Registry.Allocate σ) (allocator owner base : Nat)
    (before : Session σ) (ownerCell : Allocation) (sentinel : Address) (effects : σ)
    (valid : Valid before) (found : before.memory.heap.lookup owner = some ownerCell)
    (typed : ownerCell.type = Owner.viewType runtimeSafety) (writable : ownerCell.writable = true)
    (items : readItems before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType sentinel 0))
    (count : readField before.memory (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 0)))
    (response : allocate allocator 160 8 before.effects = (some base, effects))
    (fits : RegionAllocation.Fits before.memory ⟨160, 8⟩ base)
    (unlocked : Owner.NativeLock.checkHeader before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok ()) :
    ∃ after,
      Capacity.ensure before.memory (Owner.headerAddress ⟨owner, 0⟩) 1 (allocate allocator) before.effects =
        ((.ok (some ()), after), effects) ∧
      ensure calls allocate allocator (Owner.headerAddress ⟨owner, 0⟩) 1 before =
        (.ok (some ()), ⟨Compiler.Extraction.Memory.write before.heap before.memory.nextId
          (some ⟨allocator, .representatives []⟩), after, effects⟩) := by
  have pointer := readItemsData_from_loaded runtimeSafety before.memory owner ownerCell sentinel 0 valid.memory found typed items
  have saved := allocatedSlice_empty before.memory (Owner.headerAddress ⟨owner, 0⟩) sentinel pointer count
  obtain ⟨ready, reserved, readyValid, _, _, _, _, nativeFrame⟩ :=
    Backing.reserve_verified before.memory 5 base (allocate allocator) before.effects effects valid.memory
      (by decide) (by decide) response fits
  have older := (valid_lookup before.memory owner ownerCell valid.memory found).1
  have ownerFrame := nativeFrame owner (by omega)
  have readyItems := (readField_eq_of_lookup before.memory ready (Owner.headerAddress ⟨owner, 0⟩)
    itemsOffset ownerFrame).trans items
  obtain ⟨after, published, _⟩ := Publication.run_verified runtimeSafety ready owner ownerCell sentinel
    ⟨before.memory.nextId, 0⟩ 0 5 readyValid (ownerFrame.trans found) typed writable readyItems (by decide)
  let registered : Session σ := ⟨Compiler.Extraction.Memory.write before.heap before.memory.nextId
    (some ⟨allocator, .representatives []⟩), ready, effects⟩
  have allocated : Backing.Registry.run allocate allocator 5 before =
      (.ok (some ⟨before.memory.nextId, 0⟩), registered) := by
    simp only [Backing.Registry.run, reserved, show (5 : Nat) ≠ 0 by decide, ↓reduceIte,
      Compiler.Extraction.Memory.allocate, valid.injected.fresh valid.memory]
    rfl
  have relocated : Backing.Relocation.run calls.release allocator (Owner.headerAddress ⟨owner, 0⟩)
      sentinel ⟨before.memory.nextId, 0⟩ 0 5 registered =
        (.ok (), { registered with memory := after }) := by
    rw [Backing.Relocation.empty_source _ _ _ _ _ sentinel _ _ registered readyItems rfl]
    simp only [Backing.Relocation.finish, Backing.Release.empty, Publication.Registered.run,
      show registered.memory = ready from rfl, published, Except.mapError]
  have fallback := Backing.Fallback.of_steps allocate calls.release allocator (Owner.headerAddress ⟨owner, 0⟩)
    sentinel ⟨before.memory.nextId, 0⟩ 0 5 before registered _ allocated relocated
  have prepared := Growth.prepare_growing before.memory (Owner.headerAddress ⟨owner, 0⟩) sentinel 0 5 0
    (by decide) (by decide) count saved unlocked
  have native := Growth.first_of_reservation_and_publication before.memory ready after (Owner.headerAddress ⟨owner, 0⟩)
    sentinel ⟨before.memory.nextId, 0⟩ 5 (allocate allocator) before.effects effects reserved readyItems published
  refine ⟨after, ?_, ?_⟩
  · rw [Capacity.ensure_growing _ _ 0 1 _ _ (by decide) count (by decide), Capacity.first_capacity_checked]
    simpa only [Growth.run, prepared, ↓reduceIte] using native
  · rw [growing calls allocate allocator 0 1 _ before (by decide) count (by decide), Capacity.first_capacity_checked]
    simp only [Growth.Registered.run, prepared,
      Remap.empty_old calls.remap calls.release allocator 5 sentinel before (by decide) (by decide), fallback]
    rfl

end Compiler.Extraction.RepresentativeArray.Capacity.Registered

namespace Compiler.Extraction.RepresentativeArray.Append.Registered
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

/-- Successful first append is identical with either capacity adapter.
The fresh provisional registry write is replaced by the same singleton row.
No remap identity or release behavior is assumed for empty old storage. -/
theorem first_same (runtimeSafety : Bool) (calls : Growth.Registered.Callbacks σ)
    (allocate : Backing.Registry.Allocate σ) (allocator owner base : Nat)
    (before : Session σ) (ownerCell : Allocation) (sentinel : Address) (cell : Storage.Cell) (effects : σ)
    (valid : Valid before) (found : before.memory.heap.lookup owner = some ownerCell)
    (typed : ownerCell.type = Owner.viewType runtimeSafety) (writable : ownerCell.writable = true)
    (items : readItems before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType sentinel 0))
    (count : readField before.memory (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 0)))
    (argumentsValid : cell.arguments.length < addressLimit)
    (response : allocate allocator 160 8 before.effects = (some base, effects))
    (fits : RegionAllocation.Fits before.memory ⟨160, 8⟩ base)
    (unlocked : Owner.NativeLock.checkHeader before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok ()) :
    runWithGrowth calls runtimeSafety allocate allocator owner [] cell before =
      run runtimeSafety allocate allocator owner [] cell before := by
  obtain ⟨ready, pureCapacity, registeredCapacity⟩ := Capacity.Registered.first_pair runtimeSafety calls allocate
    allocator owner base before ownerCell sentinel effects valid found typed writable items count response fits unlocked
  obtain ⟨after, executed, heap, _, _, _, _, header, _⟩ := DescriptorRelation.first_registered runtimeSafety before
    allocator owner ownerCell sentinel cell base allocate effects valid found typed writable items count argumentsValid response fits unlocked
  have selected := Owner.root_header_pointer runtimeSafety before.memory owner ownerCell true valid.memory found typed
  have length := Execution.owner_length_from_items runtimeSafety before.memory owner ownerCell sentinel 0 valid.memory found typed items
  have tail : Execution.assumeCapacity ready (Owner.headerAddress ⟨owner, 0⟩) ⟨cell.itemAddress, 0⟩
      ⟨cell.argumentsAddress, 0⟩ cell.arguments.length 0 cell.sequence.toNat = (.ok (), after.memory) := by
    simp only [Execution.ownerRun, Execution.ownerWithCapacity, selected, Execution.runWithCapacity,
      length, Int.toNat_natCast, nextLength, Nat.zero_add, if_neg (by decide : ¬1 ≥ addressLimit), pureCapacity] at executed
    generalize assigned : Execution.assumeCapacity ready (Owner.headerAddress ⟨owner, 0⟩) ⟨cell.itemAddress, 0⟩
      ⟨cell.argumentsAddress, 0⟩ cell.arguments.length 0 cell.sequence.toNat = result at executed ⊢
    rcases result with ⟨outcome, memory⟩
    cases outcome with
    | error fault => cases executed
    | ok value =>
      cases value
      exact congrArg (fun state => (Except.ok (), state)) (congrArg (fun result => result.1.2) executed)
  simp only [run, runWithGrowth, Execution.ownerRun, Execution.ownerWithCapacity, selected,
    Execution.runWithCapacity, length, Int.toNat_zero, nextLength, Nat.zero_add,
    if_neg (by decide : ¬1 ≥ addressLimit), pureCapacity, growingCapacity, registeredCapacity,
    Except.mapError, show (Storage.idFor []).toNat = 0 from rfl, show (↑(0 : Nat) : Int) = 0 from rfl, tail]
  simp only [finish, readHeader_items _ _ _ _ header, List.length_nil, Nat.zero_add, and_self, ↓reduceIte,
    admit, Compiler.Extraction.Memory.write_same, valid.injected.fresh valid.memory, List.isEmpty_nil,
    beq_self_eq_true, Bool.and_self, List.nil_append]
  congr 2
  funext id
  simp only [Compiler.Extraction.Memory.write]
  split <;> rfl

end Compiler.Extraction.RepresentativeArray.Append.Registered
