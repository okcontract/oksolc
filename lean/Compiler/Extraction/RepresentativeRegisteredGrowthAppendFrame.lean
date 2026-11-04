/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeRegisteredGrowthAppend

namespace Compiler.Extraction.RepresentativeArray.Append.Registered
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

/-- Live parent allocations and offset views survive the actual shared append
control on every outcome, including allocation OOM and partial copy/publication
or descriptor failure. No final frame or successful child result is assumed. -/
theorem growth_parent_borrow (calls : Growth.Registered.Callbacks σ) (runtimeSafety : Bool)
    (allocate : Backing.Registry.Allocate σ) (allocator owner : Nat) (cells : List Storage.Cell) (cell : Storage.Cell)
    (before : Session σ) (ownerCell : Allocation) (valid : Valid before)
    (ownerFound : before.memory.heap.lookup owner = some ownerCell) (ownerType : ownerCell.type = Owner.viewType runtimeSafety)
    (parent : WordArray.View) (values : List (BitVec 32)) (extent : Nat) (parentCell : Allocation)
    (found : before.memory.heap.lookup parent.allocation = some parentCell) (typed : parentCell.type = .array extent WordArray.word)
    (represented : WordArray.Represents before.memory parent values) :
    let after := (runWithGrowth calls runtimeSafety allocate allocator owner cells cell before).2.memory
    after.valid = true ∧ after.heap.lookup parent.allocation = some parentCell ∧ WordArray.Represents after parent values := by
  dsimp only
  rw [(growth_reached calls runtimeSafety allocate allocator owner cells cell before).1]
  have apart := before.memory.heap.lookup_ne_of_type_ne parent.allocation owner parentCell ownerCell found ownerFound
    (by simp [typed, ownerType, Owner.viewType, WordArray.word])
  have selected := Owner.root_header_pointer runtimeSafety before.memory owner ownerCell true valid.memory ownerFound ownerType
  simp only [Execution.ownerWithCapacity, selected]
  unfold Execution.runWithCapacity
  split
  · exact ⟨valid.memory, found, represented⟩
  · rename_i length lengthRead
    dsimp only
    split
    · exact ⟨valid.memory, found, represented⟩
    · have kept := Capacity.Registered.parent_borrow runtimeSafety calls allocate allocator owner (Append.nextLength length.toNat)
        before ownerCell valid ownerFound ownerType parent values extent parentCell found typed represented
      unfold growingCapacity
      generalize ensured : Capacity.Registered.ensure calls allocate allocator (Owner.headerAddress ⟨owner, 0⟩)
        (Append.nextLength length.toNat) before = result at kept ⊢
      rcases result with ⟨outcome, ready⟩
      cases outcome with
      | error reason => exact ⟨kept.1.memory, kept.2⟩
      | ok target => cases target with
        | none => exact ⟨kept.1.memory, kept.2⟩
        | some value =>
          cases value
          have same := Execution.assumeCapacity_word_frame ready.memory (Owner.headerAddress ⟨owner, 0⟩)
            ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩ cell.arguments.length (Storage.idFor cells).toNat cell.sequence.toNat
            parent.allocation extent parentCell kept.1.memory kept.2.1 typed apart
          have post := Execution.assumeCapacity_storage ready.memory (Owner.headerAddress ⟨owner, 0⟩)
            ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩ cell.arguments.length (Storage.idFor cells).toNat cell.sequence.toNat kept.1.memory
          have words : WordArray.Represents
              (Execution.assumeCapacity ready.memory (Owner.headerAddress ⟨owner, 0⟩) ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩
                cell.arguments.length (Storage.idFor cells).toNat cell.sequence.toNat).2 parent values :=
            ⟨kept.2.2.1, fun index inside => (load_eq_of_lookup ready.memory _ true false WordArray.word
              (parent.address index) (same.trans kept.2.1.symm)).trans (kept.2.2.2 index inside)⟩
          generalize assigned : Execution.assumeCapacity ready.memory (Owner.headerAddress ⟨owner, 0⟩)
            ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩ cell.arguments.length (Storage.idFor cells).toNat cell.sequence.toNat = result at same post words ⊢
          rcases result with ⟨outcome, after⟩
          cases outcome <;> exact ⟨post.1, same, words⟩
  · exact ⟨valid.memory, found, represented⟩

end Compiler.Extraction.RepresentativeArray.Append.Registered
