/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryScalarTransfer

set_option maxRecDepth 4096

namespace Compiler.Extraction.WyhashLocal
open Compiler.ZigAir.Memory

/-- Complete pinned 64-bit target layout and captured nominal type identity.
Zig places buf_len before buf. -/
def objectType : Ty := .aggregate "hash.wyhash.Wyhash" ⟨104, 8⟩
  [(0, .scalar (.int false 64)), (8, .scalar (.int false 64)),
   (16, .object (.array 3 usize)), (40, .scalar (.int false 64)),
   (48, .scalar (.int false 64)), (56, .object (.array 48 (.scalar (.int false 8))))]

def word (value : BitVec 64) : Value := .scalar (.int false 64 value.toNat)
def put (cells : Cells) (offset : Nat) (value : Option (BitVec 64)) : Cells :=
  match value with | none => cells | some value => cells.set offset (word value)
def core (a b : Option (BitVec 64)) (s0 s1 s2 total : BitVec 64) : Cells :=
  ((((put (put [] 0 a) 8 b).set 16 (word s0)).set 24 (word s1)).set 32 (word s2)).set 40 (word total)

/-- The source's buffer may be partially initialized. Only the six core words
are transferred, and a/b may themselves be absent. -/
def Represents (source : Cells) (a b : Option (BitVec 64)) (s0 s1 s2 total : BitVec 64) : Prop :=
  source.lookup 0 = a.map word ∧ source.lookup 8 = b.map word ∧
  source.lookup 16 = some (word s0) ∧ source.lookup 24 = some (word s1) ∧
  source.lookup 32 = some (word s2) ∧ source.lookup 40 = some (word total)

def copyFields (source : Cells) : List Nat → Cells → Except Fault Cells
  | [], target => .ok target
  | offset :: rest, target => do
      let after ← source.transferScalar objectType offset target objectType offset (.int false 64)
      copyFields source rest after

/-- A fresh by-value result starts with no initialized leaves. This is the full
shallowCopy field order, with its undefined buffer and buf_len left absent. The
caller's heap allocation of such a local object is a separate boundary. -/
def shallowCopy (source : Cells) : Except Fault Cells := copyFields source [0, 8, 16, 24, 32, 40] []

theorem word_valid (value : BitVec 64) : (word value).valid = true := by
  have bound := value.isLt
  simp [word, Value.valid, Compiler.ZigAir.Scalar.Value.valid, Compiler.ZigAir.Scalar.Ty.contains,
    Compiler.ZigAir.Scalar.Ty.lower, Compiler.ZigAir.Scalar.Ty.upper]
  omega

theorem word_type (value : BitVec 64) : (word value).type = usize := rfl

theorem word_typed (value : BitVec 64) : (word value).hasType usize = true := by
  simp only [Value.hasType, word_type, decide_true, Bool.true_and, word_valid]

theorem geometry (offset : Nat) (member : offset ∈ [0, 8, 16, 24, 32, 40]) :
    leafType objectType offset = some usize ∧ acceptsView objectType offset usize = true := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem transfer_word (source target : Cells) (offset : Nat)
    (valid : source.valid objectType = true) (member : offset ∈ [0, 8, 16, 24, 32, 40]) :
    source.transferScalar objectType offset target objectType offset (.int false 64) =
      .ok (match source.lookup offset with
        | none => target.forget offset 8
        | some value => target.set offset value) :=
  Cells.transferScalar_eq _ _ _ _ _ _ _ ⟨8, 8⟩ valid (geometry offset member).1
    (geometry offset member).1 (geometry offset member).2 rfl (by decide)

theorem shallowCopy_verified (source : Cells) (a b : Option (BitVec 64)) (s0 s1 s2 total : BitVec 64)
    (valid : source.valid objectType = true) (represented : Represents source a b s0 s1 s2 total) :
    shallowCopy source = .ok (core a b s0 s1 s2 total) := by
  rcases represented with ⟨ha, hb, h0, h1, h2, ht⟩
  have step := transfer_word source
  have at0 := fun target => step target 0 valid (by decide)
  have at8 := fun target => step target 8 valid (by decide)
  have at16 := fun target => step target 16 valid (by decide)
  have at24 := fun target => step target 24 valid (by decide)
  have at32 := fun target => step target 32 valid (by decide)
  have at40 := fun target => step target 40 valid (by decide)
  cases a <;> cases b <;>
    simp [shallowCopy, copyFields, at0, at8, at16, at24, at32, at40,
      ha, hb, h0, h1, h2, ht, core, put, Cells.forget, Cells.set, bind, Except.bind]

def readWord (cells : Cells) (offset : Nat) : Except Fault (BitVec 64) := do
  let some value := cells.lookup offset | .error .uninitialized
  if !value.hasType usize then .error .malformed else
  let .scalar (.int false 64 bits) := value | .error .malformed
  .ok (BitVec.ofInt 64 bits)

/-- Specialize the existing typed writer to this complete core field table.
The equality below checks the specialization; no storage callback is assumed. -/
def writeWord (cells : Cells) (offset : Nat) (value : BitVec 64) : Except Fault Cells :=
  if offset ∈ [0, 8, 16, 24, 32, 40] then .ok (cells.set offset (word value)) else .error .unsupported

def product (a b : BitVec 64) : BitVec 128 := a.zeroExtend 128 * b.zeroExtend 128
def lo (value : BitVec 128) : BitVec 64 := value.truncate 64
def hi (value : BitVec 128) : BitVec 64 := (value >>> 64).truncate 64
def mix (a b : BitVec 64) : BitVec 64 := lo (product a b) ^^^ hi (product a b)
def secret0 : BitVec 64 := 0xa0761d6478bd642f
def secret1 : BitVec 64 := 0xe7037ed1a0b428db

/-- The six statically selected core fields; this interface is derived below,
not supplied by a caller. -/
structure Ops where
  read : Cells → Fin 6 → Except Fault (BitVec 64)
  write : Cells → Fin 6 → BitVec 64 → Except Fault Cells

def nativeOps : Ops := ⟨fun cells slot => do
    let .scalar (.int false 64 bits) ← cells.readLeaf objectType (8 * slot.val) usize | .error .malformed
    .ok (BitVec.ofInt 64 bits),
  fun cells slot value => cells.write objectType (8 * slot.val) (word value)⟩
def localOps : Ops := ⟨fun cells slot => readWord cells (8 * slot.val),
  fun cells slot value => writeWord cells (8 * slot.val) value⟩

/-- The native mum assignment order, reading both operands before writing. -/
def mum (ops : Ops) (cells : Cells) : Except Fault Cells := do
  let a ← ops.read cells 0
  let b ← ops.read cells 1
  let x := product a b
  let cells ← ops.write cells 0 (lo x)
  ops.write cells 1 (hi x)

/-- The two xor assignments at the start of native final2. -/
def xorOperands (ops : Ops) (cells : Cells) : Except Fault Cells := do
  let a ← ops.read cells 0
  let cells ← ops.write cells 0 (a ^^^ secret1)
  let b ← ops.read cells 1
  let s0 ← ops.read cells 2
  ops.write cells 1 (b ^^^ s0)

def finishProduct (ops : Ops) (cells : Cells) : Except Fault (BitVec 64) := do
  let a ← ops.read cells 0
  let total ← ops.read cells 5
  let b ← ops.read cells 1
  .ok (mix (a ^^^ secret0 ^^^ total) (b ^^^ secret1))

/-- Full native final2, retaining each read and assignment in source order. -/
def final2 (ops : Ops) (cells : Cells) : Except Fault (BitVec 64) := do
  let cells ← xorOperands ops cells
  let cells ← mum ops cells
  finishProduct ops cells

/-- The two final1 tail assignments followed by final2. The preceding buffer
reads and final1 rounds are still separate obligations; these values are their
results, not a claim that the native input has already been read. -/
def overwriteTail (ops : Ops) (cells : Cells) (a b : BitVec 64) : Except Fault Cells := do
  let cells ← ops.write cells 0 a
  ops.write cells 1 b

def finishTail (ops : Ops) (cells : Cells) (a b : BitVec 64) : Except Fault (BitVec 64) := do
  let cells ← overwriteTail ops cells a b
  final2 ops cells

def result (a b s0 total : BitVec 64) : BitVec 64 :=
  let x := product (a ^^^ secret1) (b ^^^ s0)
  mix (lo x ^^^ secret0 ^^^ total) (hi x ^^^ secret1)

theorem write_word (cells : Cells) (offset : Nat) (value : BitVec 64)
    (member : offset ∈ [0, 8, 16, 24, 32, 40]) :
    writeWord cells offset value = .ok (cells.set offset (word value)) := by
  simp only [writeWord, if_pos member]

theorem write_word_native (cells : Cells) (offset : Nat) (value : BitVec 64)
    (member : offset ∈ [0, 8, 16, 24, 32, 40]) :
    writeWord cells offset value = cells.write objectType offset (word value) := by
  rw [write_word _ _ _ member]
  exact (Cells.write_single _ _ _ _ (word_valid value) (geometry offset member).2
    (by simp only [leafFits, (geometry offset member).1, word_type, decide_true, Bool.true_and, word_valid]) rfl).symm

theorem read_word (cells : Cells) (offset : Nat) (value : BitVec 64)
    (found : cells.lookup offset = some (word value)) : readWord cells offset = .ok value := by
  simp only [readWord, found, word_typed, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  simp only [word, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem slot_member (slot : Fin 6) : 8 * slot.val ∈ [0, 8, 16, 24, 32, 40] := by
  have bound := slot.isLt
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem Ops.eq (left right : Ops) (reads : left.read = right.read) (writes : left.write = right.write) : left = right := by
  cases left
  cases right
  cases reads
  cases writes
  rfl

/-- Both local operations equal the original typed cell operations for every
selected field. The composed native consumer rewrites by this complete equality. -/
theorem nativeOps_eq : nativeOps = localOps := by
  apply Ops.eq
  · funext cells slot
    have declared := (geometry _ (slot_member slot)).1
    simp only [nativeOps, localOps, readWord, Cells.readLeaf, declared, ne_self_iff_false, ↓reduceIte]
    cases found : cells.lookup (8 * slot.val) with
    | none => rfl
    | some value =>
      by_cases typed : value.hasType usize = true
      · simp only [typed, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind, Except.bind]
      · have no : value.hasType usize = false := Bool.eq_false_iff.mpr typed
        simp only [no, Bool.false_eq_true, Bool.not_false, ↓reduceIte, bind, Except.bind]
  · dsimp only [nativeOps, localOps]
    funext cells slot value
    exact (write_word_native cells _ value (slot_member slot)).symm

theorem read_set_same (cells : Cells) (offset : Nat) (value : BitVec 64) :
    readWord (cells.set offset (word value)) offset = .ok value :=
  read_word _ _ _ (Cells.lookup_set ..)

theorem read_set_other (cells : Cells) (offset query : Nat) (value : BitVec 64) (apart : query ≠ offset) :
    readWord (cells.set offset (word value)) query = readWord cells query := by
  simp only [readWord, Cells.lookup_set_other _ _ _ _ apart]

private theorem local_read (cells : Cells) (slot : Fin 6) :
    localOps.read cells slot = readWord cells (8 * slot.val) := rfl
private theorem local_write (cells : Cells) (slot : Fin 6) (value : BitVec 64) :
    localOps.write cells slot value = writeWord cells (8 * slot.val) value := rfl

private theorem off0 : 8 * (0 : Fin 6).val = 0 := rfl
private theorem off1 : 8 * (1 : Fin 6).val = 8 := rfl
private theorem off2 : 8 * (2 : Fin 6).val = 16 := rfl
private theorem off5 : 8 * (5 : Fin 6).val = 40 := rfl

theorem mum_verified (cells : Cells) (a b : BitVec 64)
    (ha : cells.lookup 0 = some (word a)) (hb : cells.lookup 8 = some (word b)) :
    mum localOps cells = .ok ((cells.set 0 (word (lo (product a b)))).set 8 (word (hi (product a b)))) := by
  simp only [mum, local_read, local_write, off0, off1, read_word _ _ _ ha, read_word _ _ _ hb, bind, Except.bind,
    write_word _ 0 _ (by decide), write_word _ 8 _ (by decide)]

theorem xorOperands_verified (cells : Cells) (a b s0 : BitVec 64)
    (ha : cells.lookup 0 = some (word a)) (hb : cells.lookup 8 = some (word b))
    (hs : cells.lookup 16 = some (word s0)) :
    xorOperands localOps cells = .ok ((cells.set 0 (word (a ^^^ secret1))).set 8 (word (b ^^^ s0))) := by
  simp only [xorOperands, local_read, local_write, off0, off1, off2,
    read_word _ _ _ ha, bind, Except.bind, write_word _ 0 _ (by decide),
    read_set_other _ 0 8 _ (by decide), read_word _ _ _ hb,
    read_set_other _ 0 16 _ (by decide), read_word _ _ _ hs, write_word _ 8 _ (by decide)]

theorem finishProduct_verified (cells : Cells) (a b total : BitVec 64)
    (ha : cells.lookup 0 = some (word a)) (hb : cells.lookup 8 = some (word b))
    (ht : cells.lookup 40 = some (word total)) :
    finishProduct localOps cells = .ok (mix (a ^^^ secret0 ^^^ total) (b ^^^ secret1)) := by
  simp only [finishProduct, local_read, off0, off1, off5,
    read_word _ _ _ ha, read_word _ _ _ hb, read_word _ _ _ ht, bind, Except.bind]

theorem xorOperands_outcome (cells : Cells) (a b s0 total : BitVec 64)
    (ha : cells.lookup 0 = some (word a)) (hb : cells.lookup 8 = some (word b))
    (hs : cells.lookup 16 = some (word s0)) (ht : cells.lookup 40 = some (word total)) :
    ∃ after, xorOperands localOps cells = .ok after ∧
      after.lookup 0 = some (word (a ^^^ secret1)) ∧ after.lookup 8 = some (word (b ^^^ s0)) ∧
      after.lookup 40 = some (word total) := by
  refine ⟨_, xorOperands_verified cells a b s0 ha hb hs, ?_, Cells.lookup_set .., ?_⟩
  · simp [Cells.lookup_set_other, Cells.lookup_set]
  · simpa [Cells.lookup_set_other] using ht

theorem mum_outcome (cells : Cells) (a b total : BitVec 64)
    (ha : cells.lookup 0 = some (word a)) (hb : cells.lookup 8 = some (word b))
    (ht : cells.lookup 40 = some (word total)) :
    ∃ after, mum localOps cells = .ok after ∧
      after.lookup 0 = some (word (lo (product a b))) ∧ after.lookup 8 = some (word (hi (product a b))) ∧
      after.lookup 40 = some (word total) := by
  refine ⟨_, mum_verified cells a b ha hb, ?_, Cells.lookup_set .., ?_⟩
  · simp [Cells.lookup_set_other, Cells.lookup_set]
  · simpa [Cells.lookup_set_other] using ht

theorem final2_verified (cells : Cells) (a b s0 total : BitVec 64)
    (ha : cells.lookup 0 = some (word a)) (hb : cells.lookup 8 = some (word b))
    (hs : cells.lookup 16 = some (word s0)) (ht : cells.lookup 40 = some (word total)) :
    final2 localOps cells = .ok (result a b s0 total) := by
  obtain ⟨middle, first, ma, mb, mt⟩ := xorOperands_outcome cells a b s0 total ha hb hs ht
  obtain ⟨after, multiplied, aa, ab, totalAfter⟩ := mum_outcome middle (a ^^^ secret1) (b ^^^ s0) total ma mb mt
  simp only [final2, first, bind, Except.bind, multiplied]
  exact finishProduct_verified after _ _ total aa ab totalAfter

theorem overwriteTail_outcome (cells : Cells) (a b s0 total : BitVec 64)
    (state : cells.lookup 16 = some (word s0)) (length : cells.lookup 40 = some (word total)) :
    ∃ after, overwriteTail localOps cells a b = .ok after ∧
      after.lookup 0 = some (word a) ∧ after.lookup 8 = some (word b) ∧
      after.lookup 16 = some (word s0) ∧ after.lookup 40 = some (word total) := by
  refine ⟨(cells.set 0 (word a)).set 8 (word b), ?_, ?_, Cells.lookup_set .., ?_, ?_⟩
  · simp only [overwriteTail, local_write, off0, off1, write_word _ 0 _ (by decide),
      write_word _ 8 _ (by decide), bind, Except.bind]
  · simp [Cells.lookup_set_other, Cells.lookup_set]
  · simpa [Cells.lookup_set_other] using state
  · simpa [Cells.lookup_set_other] using length

theorem bind_result {α β : Type} (operation : Except Fault α) (continuation : α → Except Fault β)
    (value : α) (answer : β) (first : operation = .ok value) (second : continuation value = .ok answer) :
    operation.bind continuation = .ok answer := by
  rw [first]
  exact second

/-- Neither a nor b needs an initialized prior value. All subsequent reads use
the actual overwrites; arbitrary copied initial values yield the same result. -/
theorem finishTail_verified (cells : Cells) (a b s0 total : BitVec 64)
    (state : cells.lookup 16 = some (word s0)) (length : cells.lookup 40 = some (word total)) :
    finishTail localOps cells a b = .ok (result a b s0 total) := by
  obtain ⟨after, written, ha, hb, hs, ht⟩ := overwriteTail_outcome cells a b s0 total state length
  exact bind_result (overwriteTail localOps cells a b) (final2 localOps) after (result a b s0 total)
    written (final2_verified after a b s0 total ha hb hs ht)

theorem shallowCopy_outcome (source : Cells) (oldA oldB : Option (BitVec 64)) (s0 s1 s2 total : BitVec 64)
    (valid : source.valid objectType = true) (represented : Represents source oldA oldB s0 s1 s2 total) :
    ∃ copied, shallowCopy source = .ok copied ∧ copied.lookup 16 = some (word s0) ∧ copied.lookup 40 = some (word total) := by
  refine ⟨_, shallowCopy_verified source oldA oldB s0 s1 s2 total valid represented, ?_, Cells.lookup_set ..⟩
  simp only [core, Cells.lookup_set_other _ _ _ _ (by decide : 16 ≠ 40),
    Cells.lookup_set_other _ _ _ _ (by decide : 16 ≠ 32),
    Cells.lookup_set_other _ _ _ _ (by decide : 16 ≠ 24), Cells.lookup_set]

/-- The actual copied local object feeds the overwrite/final2 consumer. Original
source validity and core words suffice; initialized a/b are never required. -/
theorem shallowCopy_finishTail (source : Cells) (oldA oldB : Option (BitVec 64))
    (s0 s1 s2 total a b : BitVec 64)
    (valid : source.valid objectType = true) (represented : Represents source oldA oldB s0 s1 s2 total) :
    (do let copied ← shallowCopy source; finishTail nativeOps copied a b) = .ok (result a b s0 total) := by
  obtain ⟨copied, ran, hs, ht⟩ := shallowCopy_outcome source oldA oldB s0 s1 s2 total valid represented
  have finish : finishTail nativeOps copied a b = .ok (result a b s0 total) := by
    rw [nativeOps_eq]
    exact finishTail_verified copied a b s0 total hs ht
  exact bind_result (shallowCopy source) (fun cells => finishTail nativeOps cells a b) copied _ ran finish

end Compiler.Extraction.WyhashLocal
