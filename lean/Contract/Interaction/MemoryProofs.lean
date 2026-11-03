/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Interaction.Eval

namespace Contract.Interaction

theorem wordBytes_length (value : Word) : (wordBytes value).length = 32 := by simp [wordBytes]

@[simp] theorem Memory.read_zero (memory : Memory) (offset : Nat) : memory.read offset 0 = [] := rfl

theorem Memory.read_write (memory : Memory) (offset : Nat) (bytes : List UInt8) :
    (memory.write offset bytes).read offset bytes.length = bytes := by
  apply List.ext_getElem
  · simp [Memory.read]
  · intro i hi hi'
    simp only [Memory.read, List.getElem_map, List.getElem_range]
    simp [Memory.write, hi']

/-- A temporary packet preserves every disjoint live memory slice, without any
assumption that either the heap or scratch bytes were initially zero. -/
theorem Memory.read_write_disjoint (memory : Memory) (offset size scratch : Nat)
    (bytes : List UInt8) (separate : offset + size ≤ scratch ∨ scratch + bytes.length ≤ offset) :
    (memory.write scratch bytes).read offset size = memory.read offset size := by
  apply List.ext_getElem
  · simp [Memory.read]
  · intro i hi hi'
    have bound : i < size := by simpa [Memory.read] using hi
    simp only [Memory.read, List.getElem_map, List.getElem_range]
    rcases separate with before | after
    · simp [Memory.write, show ¬scratch ≤ offset+i by omega]
    · simp [Memory.write, show ¬offset+i < scratch+bytes.length by omega]

theorem Memory.read_word_write (memory : Memory) (value : Word) :
    (memory.write 0 (wordBytes value)).read 0 32 = wordBytes value := by
  rw [← wordBytes_length value]
  exact Memory.read_write _ _ _

/-- Adjacent writes completely determine the concatenated read, including when
scratch memory initially contains arbitrary bytes. -/
theorem Memory.read_write_pair (memory : Memory) (offset : Nat) (left right : List UInt8) :
    ((memory.write offset left).write (offset + left.length) right).read
      offset (left.length + right.length) = left ++ right := by
  apply List.ext_getElem
  · simp [Memory.read]
  · intro i hi hi'
    simp only [Memory.read, List.getElem_map, List.getElem_range]
    by_cases h : i < left.length
    · simp [Memory.write, List.getElem_append_left h, h, show ¬offset + left.length ≤ offset + i by omega]
    · have bound : i - left.length < right.length := by simp only [List.length_append] at hi'; omega
      simp [Memory.write, List.getElem_append_right (by omega : left.length ≤ i),
        show offset + left.length ≤ offset + i by omega,
        show offset + i < offset + left.length + right.length by simp only [List.length_append] at hi'; omega,
        show offset + i - (offset + left.length) = i - left.length by omega, bound]

/-- Consecutive writes are one contiguous write, including the outside frame. -/
theorem Memory.write_append (memory : Memory) (offset : Nat) (left right : List UInt8) :
    (memory.write offset left).write (offset + left.length) right =
      memory.write offset (left ++ right) := by
  funext i
  by_cases before : i < offset
  · simp [Memory.write, show ¬offset ≤ i by omega, show ¬offset + left.length ≤ i by omega]
  · by_cases first : i < offset + left.length
    · have index : i - offset < left.length := by omega
      simp [Memory.write, show offset ≤ i by omega, first,
        show ¬offset + left.length ≤ i by omega,
        show i < offset + (left.length + right.length) by omega,
        List.getElem?_append_left index]
    · by_cases second : i < offset + left.length + right.length
      · have index : left.length ≤ i - offset := by omega
        simp [Memory.write, show offset ≤ i by omega,
          show offset + left.length ≤ i by omega, second,
          show i < offset + (left.length + right.length) by omega,
          List.getElem?_append_right index,
          show i - offset - left.length = i - (offset + left.length) by omega]
      · simp [Memory.write, first, second,
          show ¬i < offset + (left.length + right.length) by omega]

theorem Memory.read_write_prefix (memory : Memory) (offset size : Nat) (bytes : List UInt8)
    (fits : size ≤ bytes.length) :
    (memory.write offset bytes).read offset size = bytes.take size := by
  apply List.ext_getElem
  · simp [Memory.read, Nat.min_eq_left fits]
  · intro i hi hi'
    have bound : i < size := by simpa [Memory.read] using hi
    have inBytes : i < bytes.length := by omega
    simp [Memory.read, Memory.write, inBytes]

/-- A later adjacent payload replaces the tail of a selector word. The read
contains exactly the retained prefix followed by the complete payload. -/
theorem Memory.read_write_prefix_pair (memory : Memory) (offset headSize : Nat) (left right : List UInt8)
    (fits : headSize ≤ left.length) :
    ((memory.write offset left).write (offset+headSize) right).read offset (headSize+right.length) =
      left.take headSize ++ right := by
  apply List.ext_getElem
  · simp [Memory.read,Nat.min_eq_left fits]
  · intro i hi hi'
    have bound : i < headSize+right.length := by simpa [Memory.read] using hi
    simp only [Memory.read,List.getElem_map,List.getElem_range]
    by_cases first : i < headSize
    · have inLeft : i < left.length := by omega
      simp [Memory.write,show ¬offset+headSize ≤ offset+i by omega,
        show offset+i < offset+left.length by omega,
        List.getElem_append_left (by simp; omega : i < (left.take headSize).length),inLeft]
    · have inRight : i-headSize < right.length := by omega
      simp [Memory.write,show offset+headSize ≤ offset+i by omega,
        show offset+i < offset+headSize+right.length by omega,
        List.getElem_append_right (by simp; omega : (left.take headSize).length ≤ i),
        Nat.min_eq_left fits,show offset+i-(offset+headSize) = i-headSize by omega,inRight]

/-- Solidity mapping location, with the concrete shared Keccak implementation. -/
def mappingKey (key base : Word) : Word :=
  bytesWord (Contract.Export.Keccak.hash ⟨(wordBytes key ++ wordBytes base).toArray⟩).data.toList

def mappingMemory (memory : Memory) (key base : Word) : Memory :=
  (memory.write 0 (wordBytes key)).write 32 (wordBytes base)

theorem mappingMemory_read (memory : Memory) (key base : Word) :
    (mappingMemory memory key base).read 0 64 = wordBytes key ++ wordBytes base := by
  exact Memory.read_write_pair memory 0 (wordBytes key) (wordBytes base)

theorem World.store_same (world : World) (account slot value : Word) :
    (world.store account slot value).storage account slot = value := by simp [World.store]

theorem World.store_other (world : World) (account slot value a k : Word)
    (separate : a ≠ account ∨ k ≠ slot) :
    (world.store account slot value).storage a k = world.storage a k := by
  rcases separate with h | h <;> simp [World.store, h]

end Contract.Interaction
