/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryWordByteView
import Compiler.ZigAir.MemoryWordFrame

/-! A four-byte view of one initialized u32 object, using the existing typed
heap as its only storage. Byte updates reconstruct that word and preserve its
other bytes. This sequential adapter does not admit padding, pointer bytes,
partial word initialization, volatile/atomic access or arbitrary pointer casts.
The opt-in fresh-AIR byte profile uses these operations through ByteAccess;
its decoder and source/backend correspondence remain separate obligations. -/
namespace Compiler.ZigAir.Memory.WordByteView
open WordArray

/-- Read aliases observe the same bytes regardless of pointer qualification.
Write permission remains checked by store. -/
theorem read_alias (order : WordBytes.Order) (state : State) (address : Address) (offset : Nat)
    (writable₁ many₁ writable₂ many₂ : Bool) :
    read order state (.pointer (.pointer writable₁ many₁ word) address) offset =
      read order state (.pointer (.pointer writable₂ many₂ word) address) offset := rfl

theorem read_word (order : WordBytes.Order) (state : State) (pointer : Value) (offset : Fin 4) (value : BitVec 32)
    (loaded : load state pointer = .ok (number value)) :
    read order state pointer offset.val = .ok (WordBytes.read order value offset) := by
  simp [read, offset.isLt, loaded, number]

theorem write_word (order : WordBytes.Order) (state : State) (pointer : Value) (offset : Fin 4) (value : BitVec 32) (byte : BitVec 8)
    (loaded : load state pointer = .ok (number value)) :
    write order state pointer offset.val byte = store state pointer (number (WordBytes.write order value offset byte)) := by
  simp [write, offset.isLt, loaded, number]

/-- Total byte update and exact word/list correspondence. The initial word is
initialized through Represents; no successful store is assumed. -/
theorem write_refines (order : WordBytes.Order) (state : State) (view : View) (items : List (BitVec 32))
    (index : Nat) (offset : Fin 4) (byte : BitVec 8)
    (initial : state.valid = true) (cap : Writable state view) (represented : Represents state view items)
    (inside : index < items.length) :
    ∃ after, write order state (view.pointer index) offset.val byte = .ok after ∧
      after.valid = true ∧ Writable after view ∧
      Represents after view (items.set index (WordBytes.write order items[index] offset byte)) ∧ Frame view state after := by
  have bound : index < view.length := by simpa only [represented.1] using inside
  obtain ⟨after, stored⟩ := write_total state view index (WordBytes.write order items[index] offset byte) initial cap bound
  exact ⟨after, (write_word order state (view.pointer index) offset items[index] byte (represented.2 index inside)).trans stored,
    store_preserves_valid state _ _ after initial stored,
    writable_store state after view _ _ stored cap,
    write_represents state after view items index _ represented stored,
    frame_store state after view index _ bound stored⟩

/-- Any successful byte write is precisely one checked update of the original
word. This exposes the effect for arbitrary aliases without inventing storage. -/
theorem write_effect (order : WordBytes.Order) (state after : State) (pointer : Value) (offset : Fin 4)
    (value : BitVec 32) (byte : BitVec 8) (loaded : load state pointer = .ok (number value))
    (stored : write order state pointer offset.val byte = .ok after) :
    store state pointer (number (WordBytes.write order value offset byte)) = .ok after :=
  (write_word order state pointer offset value byte loaded).symm.trans stored

theorem read_written (order : WordBytes.Order) (state after : State) (pointer : Value) (offset other : Fin 4)
    (value : BitVec 32) (byte : BitVec 8) (loaded : load state pointer = .ok (number value))
    (stored : write order state pointer offset.val byte = .ok after) :
    read order after pointer other.val = .ok (if other = offset then byte else WordBytes.read order value other) := by
  have effect := write_effect order state after pointer offset value byte loaded stored
  rw [read_word order after pointer other _ (load_after_store state pointer _ after effect)]
  by_cases same : other = offset
  · subst other; simp [WordBytes.read_write_same]
  · simp [same, WordBytes.read_write_other order value offset other byte same]

end Compiler.ZigAir.Memory.WordByteView
