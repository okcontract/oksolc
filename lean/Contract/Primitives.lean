/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Check.Axioms

/-! Unified 256-bit EVM word, 160-bit address, byte-addressed memory, and
Yellow Paper Appendix H arithmetic/bitwise/shift/signed/modular primitives. -/
namespace Contract

abbrev Word := BitVec 256
abbrev Address := BitVec 160
abbrev Memory := Nat → UInt8

def maxWord : Word := BitVec.allOnes 256
def addressMask : Word := (1#256 <<< 160) - 1#256

structure Context where
  caller : Address := 0
  self : Address := 0
  origin : Address := 0
  coinbase : Address := 0
  deriving DecidableEq, Repr

def Address.toWord (a : Address) : Word := a.zeroExtend 256

theorem Address.toWord_and_mask (a : Address) :
    a.toWord &&& addressMask = a.toWord := by
  unfold Address.toWord addressMask
  apply BitVec.eq_of_toNat_eq
  have hm : (((1#256 <<< 160) - 1#256) : Word).toNat = 2 ^ 160 - 1 := rfl
  have hz : (a.zeroExtend 256).toNat = a.toNat := BitVec.toNat_setWidth_of_le (by omega)
  rw [BitVec.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod, hz]
  exact Nat.mod_eq_of_lt a.isLt

def boolWord (b : Bool) : Word := if b then 1#256 else 0#256

def evmDiv (a b : Word) : Word := if b = 0#256 then 0#256 else a / b

def evmMod (a b : Word) : Word := if b = 0#256 then 0#256 else a % b

/-- Yellow Paper Eq. 291: two's complement signed division truncating toward zero,
with `0` on division by zero and `-2^255` on `(-2^255) / (-1)`. -/
def evmSdiv (a b : Word) : Word :=
  if b = 0#256 then 0#256
  else if a = (1#256 <<< 255) && b = ~~~0#256 then 1#256 <<< 255
  else
    let magA := if a.msb then -a else a
    let magB := if b.msb then -b else b
    let q := magA / magB
    if a.msb != b.msb then -q else q

/-- Yellow Paper Eq. 292: two's complement signed remainder with the sign of the
dividend `a` and `0` when `b = 0`. -/
def evmSmod (a b : Word) : Word :=
  if b = 0#256 then 0#256
  else
    let magA := if a.msb then -a else a
    let magB := if b.msb then -b else b
    let r := magA % magB
    if a.msb then -r else r

def evmAddmod (a b m : Word) : Word :=
  if m = 0#256 then 0#256 else BitVec.ofNat 256 ((a.toNat + b.toNat) % m.toNat)

def evmMulmod (a b m : Word) : Word :=
  if m = 0#256 then 0#256 else BitVec.ofNat 256 ((a.toNat * b.toNat) % m.toNat)

/-- Binary square-and-multiply over the `k` low bits of `exp` in `ZMod (2^256)`.
Executes in at most 256 steps for any 256-bit exponent (including `2^256 - 1`)
while matching `BitVec.ofNat 256 (base.toNat ^ exp.toNat)`. -/
def expLoop : Nat → Word → Nat → Word → Word
  | 0, _, _, acc => acc
  | k + 1, base, exp, acc =>
    let acc' := if exp % 2 = 1 then acc * base else acc
    expLoop k (base * base) (exp / 2) acc'

def evmExp (base exp : Word) : Word :=
  expLoop 256 base exp.toNat 1#256

private theorem word_pow_eq (base : Word) (n : Nat) :
    BitVec.ofNat 256 (base.toNat ^ n) =
      Nat.rec (motive := fun _ => Word) 1#256 (fun _ prev => prev * base) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Nat.pow_succ, ← ih]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul, Nat.mul_mod]

private theorem expLoop_correct (k : Nat) (base : Word) (exp : Nat) (acc : Word)
    (hexp : exp < 2 ^ k) :
    expLoop k base exp acc = acc * BitVec.ofNat 256 (base.toNat ^ exp) := by
  induction k generalizing base exp acc with
  | zero =>
    have : exp = 0 := by omega
    subst this
    simp [expLoop]
  | succ k ih =>
    have hdiv : exp / 2 < 2 ^ k := by
      rw [Nat.pow_succ] at hexp
      omega
    unfold expLoop
    rw [ih (base * base) (exp / 2) _ hdiv]
    have hsplit : exp = 2 * (exp / 2) + exp % 2 := (Nat.div_add_mod exp 2).symm
    have hsq : BitVec.ofNat 256 ((base * base).toNat ^ (exp / 2)) =
        BitVec.ofNat 256 (base.toNat ^ (2 * (exp / 2))) := by
      rw [word_pow_eq, word_pow_eq]
      generalize exp / 2 = m
      induction m with
      | zero => rfl
      | succ m ihm =>
        have h2 : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
        rw [h2]
        dsimp only
        rw [← ihm, BitVec.mul_assoc]
    rw [hsq]
    have hrem : exp % 2 = 0 ∨ exp % 2 = 1 := by omega
    rcases hrem with h0 | h1
    · have he : exp = 2 * (exp / 2) := by omega
      simp [h0, ← he]
    · have he : exp = 2 * (exp / 2) + 1 := by omega
      simp only [h1, ↓reduceIte]
      conv => rhs; rw [he, Nat.pow_add, Nat.pow_one]
      rw [BitVec.mul_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_mul, Nat.mul_comm, Nat.mul_mod]

theorem evmExp_eq_pow (base exp : Word) :
    evmExp base exp = BitVec.ofNat 256 (base.toNat ^ exp.toNat) := by
  unfold evmExp
  rw [expLoop_correct 256 base exp.toNat 1#256 exp.isLt, BitVec.one_mul]

/-- Yellow Paper H.2 `SIGNEXTEND`: extend sign bit `b * 8 + 7` for `b < 31`. -/
def evmSignextend (b x : Word) : Word :=
  if b.ult 31#256 then
    let bit := b.toNat * 8 + 7
    let mask := (1#256 <<< bit) - 1#256
    if (x &&& (1#256 <<< bit)) != 0#256 then x ||| ~~~mask else x &&& mask
  else x

/-- Yellow Paper H.2 `BYTE`: extract big-endian byte `i` (`0 ≤ i < 32`). -/
def evmByte (i x : Word) : Word :=
  if i.ult 32#256 then (x >>> (8 * (31 - i.toNat))) &&& 0xff#256 else 0#256

def evmShl (shift val : Word) : Word :=
  if shift.ult 256#256 then val <<< shift.toNat else 0#256

def evmShr (shift val : Word) : Word :=
  if shift.ult 256#256 then val >>> shift.toNat else 0#256

def evmSar (shift val : Word) : Word :=
  if shift.ult 256#256 then val.sshiftRight shift.toNat
  else if val.msb then ~~~0#256 else 0#256

theorem evmShl_eq_shiftLeft (shift val : Word) :
    evmShl shift val = val <<< shift.toNat := by
  unfold evmShl
  by_cases h : shift.ult 256#256
  · simp [h]
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    have hge : 256 ≤ shift.toNat := by
      simp [BitVec.ult] at h
      exact h
    symm
    apply BitVec.eq_of_getLsbD_eq
    intro i
    simp [BitVec.getLsbD_shiftLeft]
    omega

theorem evmShr_eq_ushiftRight (shift val : Word) :
    evmShr shift val = val >>> shift.toNat := by
  unfold evmShr
  by_cases h : shift.ult 256#256
  · simp [h]
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    have hge : 256 ≤ shift.toNat := by
      simp [BitVec.ult] at h
      exact h
    symm
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
    exact BitVec.getLsbD_of_ge val (shift.toNat + i) (by omega)

/-- Big-endian byte/word conversions and byte-addressed EVM memory. -/
def bytesWord (xs : List UInt8) : Word :=
  xs.foldl (fun w b => (w <<< 8) ||| b.toBitVec.zeroExtend 256) 0#256

def wordBytes (w : Word) : List UInt8 :=
  (List.range 32).map fun i => UInt8.ofBitVec ((w >>> (8 * (31 - i))).truncate 8)

def readBytesPadded (bytes : List UInt8) (source size : Nat) : List UInt8 :=
  (List.range size).map fun i => (bytes[source + i]?).getD 0

def Memory.read (mem : Memory) (offset size : Nat) : List UInt8 :=
  (List.range size).map fun i => mem (offset + i)

def Memory.write (mem : Memory) (offset : Nat) (bytes : List UInt8) : Memory :=
  fun addr =>
    if addr ≥ offset ∧ addr < offset + bytes.length then
      (bytes[addr - offset]?).getD 0
    else mem addr

@[simp] theorem wordBytes_length (w : Word) : (wordBytes w).length = 32 := by
  simp [wordBytes]

@[simp] theorem readBytesPadded_length (bytes : List UInt8) (source size : Nat) :
    (readBytesPadded bytes source size).length = size := by
  simp [readBytesPadded]

@[simp] theorem Memory.read_length (mem : Memory) (offset size : Nat) :
    (Memory.read mem offset size).length = size := by
  simp [Memory.read]

theorem Memory.read_write_same (mem : Memory) (offset : Nat) (bytes : List UInt8) :
    Memory.read (Memory.write mem offset bytes) offset bytes.length = bytes := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [Memory.read, List.getElem_map, List.getElem_range, Memory.write]
    have hi : offset + i ≥ offset ∧ offset + i < offset + bytes.length := ⟨by omega, by omega⟩
    simp only [hi, and_self, ↓reduceIte, Nat.add_sub_cancel_left]
    simp [h2]

theorem Memory.read_write_disjoint (mem : Memory) (wOff : Nat) (bytes : List UInt8)
    (rOff rSize : Nat) (hdisj : rOff + rSize ≤ wOff ∨ wOff + bytes.length ≤ rOff) :
    Memory.read (Memory.write mem wOff bytes) rOff rSize = Memory.read mem rOff rSize := by
  simp only [Memory.read, Memory.write]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have hnot : ¬(rOff + i ≥ wOff ∧ rOff + i < wOff + bytes.length) := by omega
  simp [hnot]

private theorem reassemble_step (x : Word) :
    ((x >>> 8) <<< 8) ||| (x.truncate 8).zeroExtend 256 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h8 : i < 8
  · simp [h8, hi]
  · have hsub : 8 + (i - 8) = i := by omega
    simp [h8, hsub, hi]

private theorem bytesWord_wordBytes_prefix (w : Word) (k : Nat) (hk : k ≤ 32) :
    bytesWord ((List.range k).map fun i => UInt8.ofBitVec ((w >>> (8 * (31 - i))).truncate 8)) =
      w >>> (8 * (32 - k)) := by
  induction k with
  | zero =>
    simp only [List.range_zero, List.map_nil, bytesWord, List.foldl_nil]
    symm
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
    exact BitVec.getLsbD_of_ge w _ (by omega)
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.map_singleton]
    unfold bytesWord at ih ⊢
    rw [List.foldl_append, ih (by omega)]
    simp only [List.foldl_cons, List.foldl_nil]
    have hshift : w >>> (8 * (32 - k)) = (w >>> (8 * (31 - k))) >>> 8 := by
      apply BitVec.eq_of_getLsbD_eq
      intro i _
      simp only [BitVec.getLsbD_ushiftRight]
      congr 1
      omega
    have hrhs : 8 * (32 - (k + 1)) = 8 * (31 - k) := by omega
    rw [hshift, hrhs]
    exact reassemble_step (w >>> (8 * (31 - k)))

theorem bytesWord_wordBytes (w : Word) : bytesWord (wordBytes w) = w := by
  simpa [wordBytes] using bytesWord_wordBytes_prefix w 32 (by omega)

#audit_contract_proof evmExp_eq_pow
#audit_contract_proof bytesWord_wordBytes
#audit_contract_proof Memory.read_write_same
#audit_contract_proof Memory.read_write_disjoint

end Contract
