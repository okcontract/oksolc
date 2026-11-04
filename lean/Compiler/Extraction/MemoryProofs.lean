/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.Memory

namespace Compiler.Extraction.Memory
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
set_option linter.unusedSimpArgs false

private theorem bind_ok (a : α) (next : α → Except Fault β) :
    ((.ok a : Except Fault α) >>= next) = next a := rfl
attribute [local simp] bind_ok

theorem write_same (heap : Heap) (address : Nat) (value : Option Allocation) :
    write heap address value address = value := by simp [write]

theorem write_other (heap : Heap) (address query : Nat) (value : Option Allocation) (different : query ≠ address) :
    write heap address value query = heap query := by simp [write, different]

theorem slice_read (allocator : Nat) (heap : Heap) (slice : ArgumentSlice)
    (valid : SliceValid allocator heap slice) (index : Nat) :
    readArgument heap slice index =
      match slice.items[index]? with | none => .error .bounds | some value => .ok value := by
  rcases valid with empty | stored
  · simp [readArgument, empty]
  · by_cases bound : index < slice.items.length
    · simp [readArgument, bound, stored]
    · simp [readArgument, bound, List.getElem?_eq_none (Nat.le_of_not_gt bound)]

theorem empty_release (heap : Heap) (allocator address : Nat) :
    releaseSlice heap allocator ⟨address, []⟩ = .ok heap := rfl

theorem wrong_allocator (heap : Heap) (allocator address : Nat) (allocation : Allocation)
    (stored : heap address = some allocation) (wrong : allocation.allocator ≠ allocator) :
    release heap allocator address = .error .wrongAllocator := by simp [release, stored, wrong]

theorem allocation_failure (heap : Heap) (allocator address : Nat) (block : Block) :
    allocate heap allocator address block false = .error .outOfMemory := rfl

/-- A representative buffer and a live item/operand allocation cannot occupy
the same allocation identity. Empty slices impose no fictitious allocation. -/
theorem resident_vector_write (allocator : Nat) (heap : Heap) (cell : Cell)
    (resident : Resident allocator heap cell) (address : Nat) (cells : List Cell)
    (vector : Vector allocator heap address cells) (replacement : Option Allocation) :
    Resident allocator (write heap address replacement) cell := by
  have itemDifferent : cell.itemAddress ≠ address := by
    intro same
    have item := resident.1
    rw [same, vector] at item
    cases item
  refine ⟨by simpa [write, itemDifferent] using resident.1, ?_⟩
  rcases resident.2 with empty | stored
  · exact Or.inl empty
  · have argsDifferent : cell.argumentSlice.address ≠ address := by
      intro same
      rw [same, vector] at stored
      cases stored
    exact Or.inr (by simpa [write, argsDifferent] using stored)

theorem resident_fresh_write (allocator : Nat) (heap : Heap) (cell : Cell)
    (resident : Resident allocator heap cell) (address : Nat) (fresh : heap address = none)
    (replacement : Option Allocation) : Resident allocator (write heap address replacement) cell := by
  have itemDifferent : cell.itemAddress ≠ address := by
    intro same
    have item := resident.1
    rw [same, fresh] at item
    cases item
  refine ⟨by simpa [write, itemDifferent] using resident.1, ?_⟩
  rcases resident.2 with empty | stored
  · exact Or.inl empty
  · have argsDifferent : cell.argumentSlice.address ≠ address := by
      intro same
      rw [same, fresh] at stored
      cases stored
    exact Or.inr (by simpa [write, argsDifferent] using stored)

theorem move_vector_eq (allocator : Nat) (heap : Heap) (oldAddress newAddress : Nat) (cells : List Cell)
    (vector : Vector allocator heap oldAddress cells) (fresh : heap newAddress = none) :
    moveVector heap allocator oldAddress newAddress true =
      .ok (write (write heap newAddress (some ⟨allocator, .representatives cells⟩)) oldAddress none) := by
  have different : newAddress ≠ oldAddress := by
    intro same
    rw [same, vector] at fresh
    cases fresh
  dsimp only [Vector] at vector
  simp [moveVector, vector, different, allocate, fresh, release, write, Ne.symm different]

/-- The new vector is live, the old vector is dead, and every separately
allocated old item/operand remains resident with the same contents and owner. -/
theorem move_vector_preserves (allocator : Nat) (heap : Heap) (oldAddress newAddress : Nat)
    (cells : List Cell) (vector : Vector allocator heap oldAddress cells)
    (resident : GraphResident allocator heap cells) (fresh : heap newAddress = none) :
    ∃ after, moveVector heap allocator oldAddress newAddress true = .ok after ∧
      Vector allocator after newAddress cells ∧ after oldAddress = none ∧
      GraphResident allocator after cells := by
  let allocated := write heap newAddress (some ⟨allocator, .representatives cells⟩)
  let after := write allocated oldAddress none
  have different : newAddress ≠ oldAddress := by
    intro same
    rw [same, vector] at fresh
    cases fresh
  refine ⟨after, move_vector_eq allocator heap oldAddress newAddress cells vector fresh, ?_, ?_, ?_⟩
  · simp [Vector, after, allocated, write, different]
  · simp [after, write]
  · intro cell member
    have allocatedResident := resident_fresh_write allocator heap cell (resident cell member)
      newAddress fresh (some ⟨allocator, .representatives cells⟩)
    have oldVector : Vector allocator allocated oldAddress cells := by
      simpa [Vector, allocated, write, Ne.symm different] using vector
    exact resident_vector_write allocator allocated cell allocatedResident oldAddress cells oldVector none

theorem move_vector_oom (allocator : Nat) (heap : Heap) (oldAddress newAddress : Nat)
    (cells : List Cell) (vector : Vector allocator heap oldAddress cells) :
    moveVector heap allocator oldAddress newAddress false = .error .outOfMemory := by
  dsimp only [Vector] at vector
  simp [moveVector, vector]

theorem move_vector_in_place (allocator : Nat) (heap : Heap) (address : Nat)
    (cells : List Cell) (vector : Vector allocator heap address cells) :
    moveVector heap allocator address address true = .ok heap := by
  dsimp only [Vector] at vector
  simp [moveVector, vector]

/-- Compose the extracted native nested lookup with allocation validity. No
heap read succeeds merely because a copied slice contains a ghost value. -/
theorem operation_borrow_read (allocator : Nat) (heap : Heap) (cells : List Cell)
    (resident : GraphResident allocator heap cells) (id : NodeId) (opcode : Opcode)
    (slice : ArgumentSlice) (found : operationProgram.run cells id opcode = .ok (some slice)) (index : Nat) :
    readArgument heap slice index =
      match slice.items[index]? with | none => .error .bounds | some value => .ok value := by
  obtain ⟨cell, entry, _, _, returned⟩ := operation_found cells id opcode slice found
  have valid := (resident cell (List.mem_of_getElem? entry)).2
  rw [returned] at valid
  exact slice_read allocator heap slice valid index

/-- A copied operand descriptor survives actual vector relocation. A pointer
into the retired vector itself produces an unallocated-memory fault. -/
theorem operation_borrow_after_move (allocator : Nat) (heap : Heap) (oldAddress newAddress : Nat)
    (cells : List Cell) (vector : Vector allocator heap oldAddress cells)
    (resident : GraphResident allocator heap cells) (fresh : heap newAddress = none)
    (id : NodeId) (opcode : Opcode) (slice : ArgumentSlice)
    (found : operationProgram.run cells id opcode = .ok (some slice)) :
    ∃ after, moveVector heap allocator oldAddress newAddress true = .ok after ∧
      (∀ index, readArgument after slice index = readArgument heap slice index) ∧
      (∀ index, readRepresentative after oldAddress index = .error .unallocated) := by
  obtain ⟨after, moved, _, retired, retained⟩ :=
    move_vector_preserves allocator heap oldAddress newAddress cells vector resident fresh
  refine ⟨after, moved, ?_, ?_⟩
  · intro index
    rw [operation_borrow_read allocator after cells retained id opcode slice found index,
      operation_borrow_read allocator heap cells resident id opcode slice found index]
  · intro index
    simp [readRepresentative, retired]

theorem representative_refines (allocator : Nat) (heap : Heap) (address : Nat) (cells : List Cell)
    (vector : Vector allocator heap address cells) (id : NodeId) :
    match representativeProgram.run cells id with
    | .ok cell => readRepresentative heap address id.toNat = .ok cell
    | .error .invalidId => cells.length ≤ id.toNat
    | .error _ => False := by
  rw [representative_correct]
  dsimp only [Vector] at vector
  cases entry : cells[id.toNat]? with
  | none => exact List.getElem?_eq_none_iff.mp entry
  | some cell => simp [readRepresentative, vector, entry]

/-- Appending a descriptor changes only the vector allocation. Existing
pointees remain valid even when the new descriptor is still uncommitted. -/
theorem vector_append_preserves (allocator : Nat) (heap : Heap) (address : Nat) (cells : List Cell)
    (vector : Vector allocator heap address cells) (resident : GraphResident allocator heap cells) (cell : Cell) :
    let after := write heap address (some ⟨allocator, .representatives (cells ++ [cell])⟩)
    Vector allocator after address (cells ++ [cell]) ∧ GraphResident allocator after cells := by
  constructor
  · simp [Vector, write]
  · intro previous member
    exact resident_vector_write allocator heap previous (resident previous member)
      address cells vector _

/-- Local cleanup may free an allocation made since the original borrow.
Freshness is tested against the original heap, not the current heap where the
temporary is live. This is the frame fact required on insertion rollback. -/
theorem fresh_cleanup_preserves (allocator : Nat) (original current : Heap) (cell : Cell)
    (borrowed : Resident allocator original cell) (resident : Resident allocator current cell)
    (address : Nat) (fresh : original address = none) :
    Resident allocator (write current address none) cell := by
  have itemDifferent : cell.itemAddress ≠ address := by
    intro same
    have item := borrowed.1
    rw [same, fresh] at item
    cases item
  refine ⟨by simpa [write, itemDifferent] using resident.1, ?_⟩
  rcases borrowed.2 with empty | originalArgs
  · exact Or.inl empty
  · have argsDifferent : cell.argumentSlice.address ≠ address := by
      intro same
      rw [same, fresh] at originalArgs
      cases originalArgs
    rcases resident.2 with empty | currentArgs
    · exact Or.inl empty
    · exact Or.inr (by simpa [write, argsDifferent] using currentArgs)

theorem release_success (heap after : Heap) (allocator address : Nat)
    (released : release heap allocator address = .ok after) : after = write heap address none := by
  unfold release at released
  cases stored : heap address with
  | none => simp [stored] at released
  | some allocation =>
    simp only [stored] at released
    split at released
    · exact (Except.ok.inj released).symm
    · contradiction

theorem release_fresh_preserves (allocator : Nat) (original current after : Heap) (cell : Cell)
    (borrowed : Resident allocator original cell) (resident : Resident allocator current cell)
    (address : Nat) (fresh : original address = none)
    (released : release current allocator address = .ok after) : Resident allocator after cell := by
  rw [release_success current after allocator address released]
  exact fresh_cleanup_preserves allocator original current cell borrowed resident address fresh

end Compiler.Extraction.Memory
