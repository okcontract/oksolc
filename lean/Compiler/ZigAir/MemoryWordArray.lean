/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryArrayGeometry
import Compiler.ZigAir.MemoryWordArrayTypes
import Compiler.ZigAir.MemoryPointers

/-! Writable u32 sub-slices of existing typed array allocations. No second heap
representation is introduced. Extents and permissions come from the allocation;
the descriptor alone supplies neither ownership nor initialized contents. -/
namespace Compiler.ZigAir.Memory.WordArray

theorem number_valid (n : BitVec 32) : (number n).valid = true := by
  have bound := n.isLt
  simp [number, Value.valid, Scalar.Value.valid, Scalar.Ty.contains,
    Scalar.Ty.lower, Scalar.Ty.upper]
  omega

theorem number_typed (n : BitVec 32) : (number n).hasType word = true := by
  simp [Value.hasType, number, Value.type, Scalar.Value.type, word]
  exact number_valid n

theorem array_layout (extent : Nat) : (Ty.array extent word).layout = some ⟨extent * 4, 4⟩ := rfl

theorem writable_fresh (state after : State) (extent : Nat) (pointer : Value)
    (allocated : allocate state (.array extent word) = .ok (pointer, after)) :
    Writable after ⟨state.nextId, 0, extent⟩ := by
  obtain ⟨_, base, _, _, rfl⟩ := allocate_shape state (.array extent word) pointer after allocated
  exact ⟨extent, ⟨base, .array extent word, [], true, true⟩,
    by simp [Heap.lookup_cons], rfl, rfl, by change 0 + extent ≤ extent; omega⟩

theorem allocation_fault (state : State) (extent : Nat) (fault : Fault)
    (initial : state.valid = true) (failed : allocate state (.array extent word) = .error fault) :
    fault = .outOfMemory := by
  simp only [allocate, initial, Bool.not_true, Bool.false_eq_true, ↓reduceIte, array_layout] at failed
  split at failed
  · exact (Except.error.inj failed).symm
  · contradiction

/-- Derive access checks, including physical bounds and alignment, rather than
assuming that the pointer operation or a later store succeeds. -/
theorem array_access (state : State) (id extent index bytes : Nat) (cell : Allocation)
    (initial : state.valid = true) (found : state.heap.lookup id = some cell)
    (typed : cell.type = .array extent word) (writable : cell.writable = true)
    (inside : index < extent) (size : bytes ≤ 4) (write : Bool) :
    access state ⟨id, index * 4⟩ ⟨bytes, 4⟩ write = .ok cell := by
  exact Memory.array_access state id extent index bytes word ⟨4, 4⟩ cell initial found typed writable
    rfl (by decide) (by decide) inside size write

theorem element_access (state : State) (view : View) (index bytes : Nat)
    (initial : state.valid = true) (cap : Writable state view)
    (inside : index < view.length) (size : bytes ≤ 4) (write : Bool) :
    ∃ extent cell, state.heap.lookup view.allocation = some cell ∧
      cell.type = .array extent word ∧ cell.writable = true ∧
      view.first + view.length ≤ extent ∧
      access state (view.address index) ⟨bytes, 4⟩ write = .ok cell := by
  obtain ⟨extent, cell, found, typed, writable, bound⟩ := cap
  exact ⟨extent, cell, found, typed, writable, bound,
    array_access state view.allocation extent (view.first + index) bytes cell initial found typed
      writable (by omega) size write⟩

theorem view_width (state : State) (view : View)
    (initial : state.valid = true) (cap : Writable state view) : view.length < addressLimit := by
  obtain ⟨extent, cell, found, typed, _, bound⟩ := cap
  obtain ⟨_, positive, layout, shaped, _, bounded, limit⟩ := valid_lookup state view.allocation cell initial found
  rw [typed, array_layout] at shaped
  cases Option.some.inj shaped
  dsimp only at bounded
  omega

theorem element_pointer (state : State) (view : View) (index : Nat)
    (initial : state.valid = true) (cap : Writable state view) (inside : index < view.length) :
    elementPointer state view.buffer index = .ok (view.pointer index) := by
  obtain ⟨extent, cell, found, typed, writable, bound⟩ := cap
  have firstInside : view.first < extent := by omega
  have atStart := array_access state view.allocation extent view.first 0 cell initial found typed writable
    firstInside (by omega) false
  have atEnd := array_access state view.allocation extent (view.first + index) 0 cell initial found typed writable
    (by omega) (by omega) false
  have atElement := array_access state view.allocation extent (view.first + index) 4 cell initial found typed writable
    (by omega) (by omega) false
  obtain ⟨_, positive, layout, shaped, _, bounded, limit⟩ := valid_lookup state view.allocation cell initial found
  rw [typed, array_layout] at shaped
  cases Option.some.inj shaped
  dsimp only at bounded
  have rawBounds : ¬((cell.base : Int) + ↑(view.first * 4) + ↑(index * 4) < 0 ∨
      (cell.base : Int) + ↑(view.first * 4) + ↑(index * 4) ≥ ↑addressLimit) := by omega
  have lower : ¬((cell.base : Int) + ↑(view.first * 4) + ↑(index * 4) < ↑cell.base) := by omega
  have offset : ((cell.base : Int) + ↑(view.first * 4) + ↑(index * 4)).toNat - cell.base =
      (view.first + index) * 4 := by omega
  simp only [elementPointer, View.buffer, View.pointer, View.address, Nat.add_zero,
    offsetPointer, word, Ty.layout, Ty.leafLayout, Nat.reduceEqDiff, Bool.false_eq_true, ↓reduceIte,
    atStart, bind, Except.bind, if_neg rawBounds, if_neg lower, offset, atEnd,
    pointerCast, pointerCompatible, decide_true, Bool.and_false, Bool.true_or, Bool.false_or, Bool.not_true,
    atElement]

end Compiler.ZigAir.Memory.WordArray
