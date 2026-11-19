/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativePop
import Compiler.Extraction.RepresentativeBackingRegistry
import Compiler.Extraction.NormalizationMemoryContracts

namespace Compiler.Extraction.RepresentativeArray.Pop.Registered
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

abbrev Fault := Backing.Registry.Fault

/-- Refine the completed length decrement using the reached pointer and the
existing vector. This is a ghost registry update, not another native statement.
An absent, mistyped, misowned or stale vector rejects without rewinding memory. -/
def finish (allocator owner : Nat) (reached : Session σ) : Except Fault Unit × Session σ :=
  match readItems reached.memory (Owner.headerAddress ⟨owner, 0⟩) with
  | .error reason => (.error (.memory reason), reached)
  | .ok (.slice type data length) =>
    if type = itemsType ∧ data.offset = 0 then
      match reached.heap data.allocation with
      | none => (.error (.registry .unallocated), reached)
      | some ⟨actual, .representatives cells⟩ =>
        if actual ≠ allocator then (.error (.registry .wrongAllocator), reached) else
        if cells.length ≠ length + 1 then (.error (.registry .bounds), reached) else
        (.ok (), { reached with heap := (Compiler.Extraction.Memory.write reached.heap data.allocation
          (some ⟨allocator, .representatives cells.dropLast⟩)) })
      | some _ => (.error (.registry .wrongType), reached)
    else (.error (.memory .malformed), reached)
  | .ok _ => (.error (.memory .malformed), reached)

def run (allocator owner : Nat) (before : Session σ) : Except Fault Unit × Session σ :=
  match Pop.run before.memory (Owner.headerAddress ⟨owner, 0⟩) with
  | .error reason => (.error (.memory reason), before)
  | .ok memory => finish allocator owner { before with memory }

theorem finish_reached (allocator owner : Nat) (reached : Session σ) :
    (finish allocator owner reached).2.memory = reached.memory ∧
    (finish allocator owner reached).2.effects = reached.effects := by
  unfold finish
  split
  · exact ⟨rfl, rfl⟩
  · split
    · split
      · exact ⟨rfl, rfl⟩
      · split
        · exact ⟨rfl, rfl⟩
        · split <;> exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem rejected (allocator owner : Nat) (before : Session σ) (reason : Compiler.ZigAir.Memory.Fault)
    (executed : Pop.run before.memory (Owner.headerAddress ⟨owner, 0⟩) = .error reason) :
    run allocator owner before = (.error (.memory reason), before) := by
  simp only [run, executed]

/-- Registration cannot erase a completed native store even when it rejects. -/
theorem reached (allocator owner : Nat) (before : Session σ) (memory : State)
    (executed : Pop.run before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok memory) :
    (run allocator owner before).2.memory = memory ∧
    (run allocator owner before).2.effects = before.effects := by
  simpa only [run, executed] using finish_reached allocator owner { before with memory }

theorem finish_vector (allocator owner lifetime : Nat) (cells : List Storage.Cell) (last : Storage.Cell)
    (reached : Session σ)
    (loaded : readItems reached.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType ⟨lifetime, 0⟩ cells.length))
    (registered : Compiler.Extraction.Memory.Vector allocator reached.heap lifetime (cells ++ [last])) :
    finish allocator owner reached = (.ok (), { reached with heap := (Compiler.Extraction.Memory.write reached.heap lifetime
      (some ⟨allocator, .representatives cells⟩)) }) := by
  simp only [Compiler.Extraction.Memory.Vector] at registered
  simp [finish, loaded, registered]

theorem finish_read_rejected (allocator owner : Nat) (reached : Session σ) (reason : Compiler.ZigAir.Memory.Fault)
    (loaded : readItems reached.memory (Owner.headerAddress ⟨owner, 0⟩) = .error reason) :
    finish allocator owner reached = (.error (.memory reason), reached) := by
  simp only [finish, loaded]

theorem finish_shape_rejected (allocator owner : Nat) (reached : Session σ) (type : Ty) (data : Address) (length : Nat)
    (loaded : readItems reached.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice type data length))
    (invalid : ¬ (type = itemsType ∧ data.offset = 0)) :
    finish allocator owner reached = (.error (.memory .malformed), reached) := by
  simp only [finish, loaded, if_neg invalid]

theorem finish_missing (allocator owner lifetime length : Nat) (reached : Session σ)
    (loaded : readItems reached.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType ⟨lifetime, 0⟩ length))
    (absent : reached.heap lifetime = none) :
    finish allocator owner reached = (.error (.registry .unallocated), reached) := by
  simp only [finish, loaded, and_self, ↓reduceIte, absent]

theorem finish_wrong_type (allocator owner lifetime length actual : Nat) (values : List Compiler.Algebraic.NodeId) (reached : Session σ)
    (loaded : readItems reached.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType ⟨lifetime, 0⟩ length))
    (registered : reached.heap lifetime = some ⟨actual, .arguments values⟩) :
    finish allocator owner reached = (.error (.registry .wrongType), reached) := by
  simp only [finish, loaded, and_self, ↓reduceIte, registered]

theorem finish_wrong_owner (allocator owner lifetime length actual : Nat) (cells : List Storage.Cell) (reached : Session σ)
    (loaded : readItems reached.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType ⟨lifetime, 0⟩ length))
    (registered : reached.heap lifetime = some ⟨actual, .representatives cells⟩) (wrong : actual ≠ allocator) :
    finish allocator owner reached = (.error (.registry .wrongAllocator), reached) := by
  simp only [finish, loaded, and_self, ↓reduceIte, registered, if_pos wrong]

theorem finish_stale (allocator owner lifetime length : Nat) (cells : List Storage.Cell) (reached : Session σ)
    (loaded : readItems reached.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType ⟨lifetime, 0⟩ length))
    (registered : reached.heap lifetime = some ⟨allocator, .representatives cells⟩) (stale : cells.length ≠ length + 1) :
    finish allocator owner reached = (.error (.registry .bounds), reached) := by
  simp only [finish, loaded, and_self, ↓reduceIte, registered, ne_eq, not_true_eq_false, if_pos stale]

/-- Initial owner/header and backing geometry plus the existing vector derive
the same native write and its registry witness. No final validity, shortened
vector or successful reached read is assumed. Last-row destruction and caller
establishment of these initial facts are separate obligations. -/
theorem verified (runtimeSafety : Bool) (before : Session σ) (allocator owner lifetime capacity : Nat)
    (ownerCell backing : Allocation) (cells : List Storage.Cell) (last : Storage.Cell)
    (valid : Valid before) (ownerFound : before.memory.heap.lookup owner = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety) (ownerWritable : ownerCell.writable = true)
    (backingFound : before.memory.heap.lookup lifetime = some backing)
    (backingTyped : backing.type = .array capacity Expression.allocationType)
    (loaded : readItems before.memory (Owner.headerAddress ⟨owner, 0⟩) =
      .ok (.slice itemsType ⟨lifetime, 0⟩ (cells.length + 1)))
    (capacityRead : readField before.memory (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 capacity)))
    (registered : Compiler.Extraction.Memory.Vector allocator before.heap lifetime (cells ++ [last]))
    (occupied : cells.length < capacity) :
    ∃ after, run allocator owner before = (.ok (), after) ∧ Valid after ∧
      after.heap = Compiler.Extraction.Memory.write before.heap lifetime (some ⟨allocator, .representatives cells⟩) ∧
      Compiler.Extraction.Memory.Vector allocator after.heap lifetime cells ∧ after.effects = before.effects ∧
      readHeader after.memory (Owner.headerAddress ⟨owner, 0⟩) =
        .ok (.slice itemsType ⟨lifetime, 0⟩ cells.length, .scalar (.int false 64 capacity)) ∧
      before.memory.heap.RetainsShape after.memory.heap ∧
      after.memory.nextId = before.memory.nextId ∧ after.memory.nextAddress = before.memory.nextAddress ∧
      (∀ query, query ≠ owner → after.memory.heap.lookup query = before.memory.heap.lookup query) ∧
      (∀ cell, Compiler.Extraction.Memory.Resident allocator before.heap cell → Compiler.Extraction.Memory.Resident allocator after.heap cell) := by
  have bound := Append.nextLength_bounded before.memory lifetime capacity cells.length backing valid.memory backingFound backingTyped occupied
  obtain ⟨memory, executed, memoryValid, shape, header, nextId, nextAddress, frame⟩ := Pop.verified runtimeSafety before.memory owner ownerCell
    ⟨lifetime, 0⟩ cells.length capacity valid.memory ownerFound ownerTyped ownerWritable loaded capacityRead
    (by simp only [Append.nextLength] at bound; omega)
  have sessionValid : Valid ({ before with memory } : Session σ) := by
    refine ⟨memoryValid, ?_, valid.injected.retained shape⟩
    intro actual query values nonempty stored
    obtain ⟨⟨parent, found, typed, writable, persistent⟩, represented⟩ := valid.related actual query values nonempty stored
    have kept := frame query (before.memory.heap.lookup_ne_of_type_ne query owner parent ownerCell found ownerFound
      (by simp [typed, ownerTyped, Owner.viewType]))
    exact ⟨⟨parent, kept.trans found, typed, writable, persistent⟩, represented_frame _ values represented kept⟩
  have apart := before.memory.heap.lookup_ne_of_type_ne lifetime owner backing ownerCell backingFound ownerFound
    (by simp [backingTyped, ownerTyped, Owner.viewType])
  obtain ⟨registeredBacking, registeredFound, persistent⟩ := valid.injected lifetime _ registered
  have same : registeredBacking = backing := Option.some.inj (registeredFound.symm.trans backingFound)
  subst registeredBacking
  let after : Session σ := { before with memory, heap := (Compiler.Extraction.Memory.write before.heap lifetime
    (some ⟨allocator, .representatives cells⟩)) }
  refine ⟨after, ?_, ?_, rfl, Compiler.Extraction.Memory.write_same _ _ _, rfl, header, shape, nextId, nextAddress, frame, ?_⟩
  · simp only [run, executed]
    exact finish_vector allocator owner lifetime cells last { before with memory }
      (readHeader_items _ _ _ _ header) registered
  · exact Backing.Registry.vector_write_valid { before with memory } allocator lifetime backing cells sessionValid
      ((frame lifetime apart).trans backingFound) persistent
  · intro cell resident
    exact Compiler.Extraction.Memory.resident_vector_write allocator before.heap cell resident lifetime (cells ++ [last]) registered _

end Compiler.Extraction.RepresentativeArray.Pop.Registered
