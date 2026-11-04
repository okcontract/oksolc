/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.WyhashFinalization

set_option maxRecDepth 4096

namespace Compiler.Extraction.WyhashBuffer
open Compiler.ZigAir.Memory WyhashLocal

def buffer (first length : Nat) : ByteSlice.View := ⟨objectType, 56 + first, length⟩
def scratch : ByteSlice.View := ⟨.array 16 ByteSlice.byte, 0, 16⟩

/-- Exactly the initialized prefix and, when needed, retained suffix. Bytes in
the intervening gap may be absent and are never evaluated by finalization. -/
def Represents (source : Cells) (length : Nat) (bytes : Nat → BitVec 8) : Prop :=
  (∀ i < length, source.lookup (56 + i) = some (ByteSlice.value (bytes i))) ∧
  (length < 16 → ∀ i, 48 - (16 - length) ≤ i → i < 48 →
    source.lookup (56 + i) = some (ByteSlice.value (bytes i)))

def inputLength (length : Nat) : Nat := if length < 16 then 16 else length
def inputStart (length : Nat) : Nat := if length < 16 then 16 - length else 0
def inputBytes (length : Nat) (bytes : Nat → BitVec 8) (i : Nat) : BitVec 8 :=
  if length < 16 then
    if i < 16 - length then bytes (48 - (16 - length) + i) else bytes (i - (16 - length))
  else bytes i

/-- Both memcpy calls use the ordinary typed reader and writer. The scratch
object starts with no initialized leaves. Its local heap admission is separate. -/
def prepare (source : Cells) (length : Nat) : Except Fault (Cells × ByteSlice.View × Nat) :=
  if length > 48 then .error .sourceBounds else
  if length < 16 then do
    let rem := 16 - length
    let middle ← ByteSlice.copy source (buffer (48 - rem) rem) scratch 0 0 rem []
    let after ← ByteSlice.copy source (buffer 0 length) scratch 0 rem length middle
    .ok (after, scratch, rem)
  else .ok (source, buffer 0 length, 0)

theorem buffer_geometry (first length : Nat) (bound : first + length ≤ 48) :
    ByteSlice.Geometry (buffer first length) := by
  have table : ∀ i : Fin 48,
      leafType objectType (56 + i.val) = some ByteSlice.byte ∧
      acceptsView objectType (56 + i.val) ByteSlice.byte = true := by decide +kernel
  intro i inside
  have selected := table ⟨first + i, by change i < length at inside; omega⟩
  simpa only [buffer, Nat.add_assoc] using selected

theorem prepare_verified (source : Cells) (length : Nat) (bytes : Nat → BitVec 8)
    (bound : length ≤ 48) (represented : Represents source length bytes) :
    ∃ input view, prepare source length = .ok (input, view, inputStart length) ∧
      view.length = inputLength length ∧ ByteSlice.Geometry view ∧
      ByteSlice.Represents input view (inputBytes length bytes) := by
  by_cases short : length < 16
  · have suffix : ByteSlice.Represents source (buffer (48 - (16 - length)) (16 - length))
        (fun i => bytes (48 - (16 - length) + i)) := by
      intro i inside
      change i < 16 - length at inside
      simpa only [buffer, Nat.add_assoc] using represented.2 short (48 - (16 - length) + i) (by omega) (by omega)
    have headRead : ByteSlice.Represents source (buffer 0 length) bytes := by
      simpa only [ByteSlice.Represents, buffer, Nat.add_zero] using represented.1
    obtain ⟨middle, first, initial, _⟩ := ByteSlice.copy_verified source []
      (buffer (48 - (16 - length)) (16 - length)) scratch _
      (buffer_geometry _ _ (by omega)) (ByteSlice.array_geometry 16) suffix 0 0 (16 - length) (by simp [buffer]) (by simp [scratch] <;> omega)
    obtain ⟨after, second, appended, retained⟩ := ByteSlice.copy_verified source middle
      (buffer 0 length) scratch bytes (buffer_geometry _ _ (by omega)) (ByteSlice.array_geometry 16)
      headRead 0 (16 - length) length (by simp [buffer]) (by simp [scratch] <;> omega)
    refine ⟨after, scratch, ?_, by simp [scratch, inputLength, short], ByteSlice.array_geometry 16, ?_⟩
    · simp only [prepare, if_neg (by omega : ¬length > 48), if_pos short, first, second,
        inputStart, bind, Except.bind]
    · intro i inside
      change i < 16 at inside
      change after.lookup (0 + i) = some (ByteSlice.value (inputBytes length bytes i))
      simp only [Nat.zero_add, inputBytes, if_pos short]
      by_cases early : i < 16 - length
      · rw [if_pos early, retained i (Or.inl (by simp only [scratch]; omega))]
        simpa only [scratch, Nat.zero_add] using initial i early
      · rw [if_neg early]
        have atIndex := appended (i - (16 - length)) (by omega)
        have index : 16 - length + (i - (16 - length)) = i := by omega
        simpa only [scratch, Nat.zero_add, index] using atIndex
  · refine ⟨source, buffer 0 length, ?_, by simp [buffer, inputLength, short], buffer_geometry _ _ (by omega), ?_⟩
    · simp only [prepare, if_neg (by omega : ¬length > 48), if_neg short, inputStart]
    · simpa only [ByteSlice.Represents, inputBytes, if_neg short, buffer, Nat.add_zero] using represented.1

def readLength (source : Cells) : Except Fault Nat := do
  let .scalar (.int false 64 bits) ← source.readLeaf objectType 48 usize | .error .malformed
  .ok bits.toNat

/-- Complete local finalization for the compiler's long-key route. Its actual
input length is at least 41, so smallKey remains a distinct unsupported route. -/
def run (source : Cells) : Except Fault (BitVec 64) := do
  let length ← readLength source
  if length > 48 then .error .sourceBounds else
  let copied ← shallowCopy source
  let total ← nativeOps.read source 5
  if total.toNat ≤ 16 then .error .unsupported else
  let (input, view, start) ← prepare source length
  WyhashFinalization.finish nativeOps input view start copied

def result (length : Nat) (bytes : Nat → BitVec 8) (s0 s1 s2 total : BitVec 64) : BitVec 64 :=
  WyhashFinalization.result (inputBytes length bytes) (inputLength length) (inputStart length) s0 s1 s2 total

theorem readLength_verified (source : Cells) (length : Nat) (bound : length ≤ 48)
    (found : source.lookup 48 = some (word (BitVec.ofNat 64 length))) :
    readLength source = .ok length := by
  have declared : leafType objectType 48 = some usize := by decide +kernel
  have loaded : source.readLeaf objectType 48 usize = .ok (word (BitVec.ofNat 64 length)) := by
    simp only [Cells.readLeaf, declared, ne_self_iff_false, ↓reduceIte, found, word_typed]
  simp only [readLength, loaded, bind, Except.bind, word, Int.toNat_natCast, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]

/-- Original source cells supply length, core and initialized buffer regions.
There is no supplied scratch, chosen tail pair, updated state or read success. -/
theorem run_verified (source : Cells) (oldA oldB : Option (BitVec 64))
    (s0 s1 s2 total : BitVec 64) (length : Nat) (bytes : Nat → BitVec 8)
    (valid : source.valid objectType = true)
    (coreRead : WyhashLocal.Represents source oldA oldB s0 s1 s2 total)
    (lengthRead : source.lookup 48 = some (word (BitVec.ofNat 64 length)))
    (bounded : length ≤ 48) (long : 16 < total.toNat) (bufferRead : Represents source length bytes) :
    run source = .ok (result length bytes s0 s1 s2 total) := by
  have lengthLoaded := readLength_verified source length bounded lengthRead
  have copied := shallowCopy_verified source oldA oldB s0 s1 s2 total valid coreRead
  have totalLoaded : nativeOps.read source 5 = .ok total := by
    rw [nativeOps_eq]
    exact read_word source 40 total coreRead.2.2.2.2.2
  obtain ⟨input, view, prepared, extent, geometry, represented⟩ := prepare_verified source length bytes bounded bufferRead
  have core0 : (core oldA oldB s0 s1 s2 total).lookup 16 = some (word s0) := by
    simp only [core, Cells.lookup_set_other _ _ _ _ (by decide : 16 ≠ 40),
      Cells.lookup_set_other _ _ _ _ (by decide : 16 ≠ 32),
      Cells.lookup_set_other _ _ _ _ (by decide : 16 ≠ 24), Cells.lookup_set]
  have core1 : (core oldA oldB s0 s1 s2 total).lookup 24 = some (word s1) := by
    simp only [core, Cells.lookup_set_other _ _ _ _ (by decide : 24 ≠ 40),
      Cells.lookup_set_other _ _ _ _ (by decide : 24 ≠ 32), Cells.lookup_set]
  have core2 : (core oldA oldB s0 s1 s2 total).lookup 32 = some (word s2) := by
    simp only [core, Cells.lookup_set_other _ _ _ _ (by decide : 32 ≠ 40), Cells.lookup_set]
  have coreTotal : (core oldA oldB s0 s1 s2 total).lookup 40 = some (word total) := Cells.lookup_set ..
  have bounds : 16 ≤ view.length ∧ inputStart length ≤ view.length ∧ view.length - inputStart length ≤ 48 := by
    rw [extent]
    simp only [inputLength, inputStart]
    split <;> omega
  have finished := WyhashFinalization.finish_verified input (core oldA oldB s0 s1 s2 total) view
    (inputBytes length bytes) geometry represented (inputStart length) bounds.1 bounds.2.1 bounds.2.2
    s0 s1 s2 total core0 core1 core2 coreTotal
  simp only [run, lengthLoaded, bind, Except.bind, if_neg (by omega : ¬length > 48), copied,
    totalLoaded, if_neg (by omega : ¬total.toNat ≤ 16), prepared, finished]
  exact congrArg Except.ok (by rw [extent]; rfl)

end Compiler.Extraction.WyhashBuffer
