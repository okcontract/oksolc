/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerGraphInit
import Compiler.Extraction.RepresentativeOwnerWrites
import Compiler.Extraction.RepresentativeOwnerLock

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.GraphInit.OwnerMemory
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory

/-- The captured empty header is materialized in already declared owner storage.
Its empty sentinel is not allocated or dereferenced. The complete cache defaults
establish null metadata, zero size and availability,
and the captured lock state. Allocator contents and the caller's owner allocation
remain separate obligations. -/
def run (runtimeSafety : Bool) (allocator : Nat) (before : Session σ) (owner sentinel : Address) :
    Except Compiler.ZigAir.Memory.Fault (Nat × World σ) := do
  let header ← Compiler.Extraction.RepresentativeArray.Owner.initializeHeader runtimeSafety before.memory owner sentinel 0 0
  let mapped ← Compiler.Extraction.ExpressionMap.Initialization.run runtimeSafety header owner
  let memory ← Compiler.Extraction.RepresentativeArray.Owner.NativeLock.initializeLock runtimeSafety mapped owner
  .ok (GraphInit.run allocator { before with memory })

/-- The actual stores establish the header and preserve caller validity. A live
stack owner is unregistered by the existing injection; no separation, successful
store, initialized container fields or final Valid premise is supplied. The native
owner allocation and allocator fields are not established by this theorem. -/
theorem initialize_verified (runtimeSafety : Bool) (allocator : Nat) (before : Session σ) (lifetime : Nat)
    (cell : Compiler.ZigAir.Memory.Allocation) (sentinel : Address) (meaning : Meaning) (valid : Valid before)
    (found : before.memory.heap.lookup lifetime = some cell)
    (typed : cell.type = Compiler.Extraction.RepresentativeArray.Owner.viewType runtimeSafety)
    (writable : cell.writable = true) (stack : cell.stack = true) :
    ∃ after, run runtimeSafety allocator before ⟨lifetime, 0⟩ sentinel = .ok (allocator, after) ∧
      Valid after.memory ∧ Interner.Invariant meaning after.graph ∧
      Memory.GraphResident allocator after.memory.heap [] ∧ after.graph.representatives = some [] ∧
      Compiler.Extraction.RepresentativeArray.readHeader after.memory.memory
        (Compiler.Extraction.RepresentativeArray.Owner.headerAddress ⟨lifetime, 0⟩) =
          .ok (.slice Compiler.Extraction.RepresentativeArray.itemsType sentinel 0, .scalar (.int false 64 0)) ∧
      after.memory.heap = before.heap ∧ after.memory.effects = before.effects ∧
      after.memory.memory.nextId = before.memory.nextId ∧ after.memory.memory.nextAddress = before.memory.nextAddress ∧
      (∀ other, other ≠ lifetime → after.memory.memory.heap.lookup other = before.memory.heap.lookup other) ∧
      Compiler.Extraction.ExpressionMap.readSize runtimeSafety after.memory.memory ⟨lifetime, 0⟩ = .ok (.scalar (.int false 32 0)) ∧
      (∀ key, Compiler.Extraction.ExpressionMap.getEmpty runtimeSafety after.memory.memory ⟨lifetime, 0⟩ key =
        .ok (after.graph.table key)) ∧
      Compiler.Extraction.ExpressionMap.Initialization.observeEmpty runtimeSafety after.memory.memory ⟨lifetime, 0⟩ = .ok () ∧
      before.memory.heap.RetainsShape after.memory.memory.heap ∧
      Compiler.Extraction.RepresentativeArray.Owner.NativeLock.checkUnlocked runtimeSafety after.memory.memory ⟨lifetime, 0⟩ = .ok () := by
  obtain ⟨header, initialized, headerValid, headerShape, readback, headerId, headerAddress, headerFrame⟩ :=
    Compiler.Extraction.RepresentativeArray.Owner.initializeHeader_verified runtimeSafety before.memory lifetime cell sentinel 0 0
      valid.memory found typed writable (by decide) (by decide)
  obtain ⟨headerCell, headerFound, headerCellShape⟩ := headerShape lifetime cell found
  obtain ⟨mapped, initializedMap, map⟩ :=
    Compiler.Extraction.ExpressionMap.Initialization.initialize_verified runtimeSafety header lifetime headerCell headerValid headerFound
      (headerCellShape.2.1.trans typed) (headerCellShape.2.2.1.trans writable)
  obtain ⟨mappedCell, mappedFound, mappedShape⟩ := map.shape lifetime headerCell headerFound
  obtain ⟨memory, initializedLock, lock⟩ :=
    Compiler.Extraction.RepresentativeArray.Owner.NativeLock.initialize_verified runtimeSafety mapped lifetime mappedCell
      map.valid mappedFound (mappedShape.2.1.trans (headerCellShape.2.1.trans typed))
      (mappedShape.2.2.1.trans (headerCellShape.2.2.1.trans writable))
  have complete : Compiler.Extraction.ExpressionMap.Initialization.Initialized runtimeSafety header memory lifetime :=
    ⟨map.toFrame.trans lock.toFrame, fun slot active => (lock.map slot active).trans (map.fields slot active)⟩
  have shape := headerShape.trans complete.shape
  have frame := fun other different => (complete.allocations other different).trans (headerFrame other different)
  have headerRead := complete.header.trans readback
  have countRead := complete.fields .size (by simp [Compiler.Extraction.ExpressionMap.Initialization.Slot.Active])
  rw [Compiler.Extraction.ExpressionMap.Initialization.size_read] at countRead
  have privateOwner := Injected.stack_unregistered before.heap before.memory lifetime cell valid.injected found stack
  have retained := Valid.private_memory_frame before memory lifetime valid privateOwner complete.valid shape frame
  have empty := GraphInit.initialize_verified allocator { before with memory } meaning retained
  exact ⟨(GraphInit.run allocator { before with memory }).2,
    by simp only [run, initialized, initializedMap, initializedLock, bind, Except.bind, GraphInit.run],
    empty.2.2.1, empty.2.2.2.1, empty.2.2.2.2.1, empty.2.2.2.2.2,
    headerRead, rfl, rfl, complete.nextId.trans headerId, complete.nextAddress.trans headerAddress, frame, countRead,
    fun key => Compiler.Extraction.ExpressionMap.empty_get runtimeSafety memory ⟨lifetime, 0⟩ key countRead, complete.observed, shape, lock.unlocked⟩

/-- Empty native representative queries reject every ID before inspecting the
sentinel. The observed header, rather than a supplied logical list, controls it. -/
theorem empty_representative (memory : Compiler.ZigAir.Memory.State) (header sentinel : Address) (id : NodeId)
    (loaded : Compiler.Extraction.RepresentativeArray.readHeader memory header =
      .ok (.slice Compiler.Extraction.RepresentativeArray.itemsType sentinel 0, .scalar (.int false 64 0))) :
    Compiler.Extraction.RepresentativeArray.representative memory header id = .ok (.error .invalidId) :=
  Compiler.Extraction.RepresentativeArray.invalid_from_loaded_header memory header sentinel 0 id
    (Compiler.Extraction.RepresentativeArray.readHeader_items memory header _ _ loaded) (Nat.zero_le _)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.GraphInit.OwnerMemory
