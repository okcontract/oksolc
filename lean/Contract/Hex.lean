/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Check.Axioms

/-! Canonical hexadecimal encoding and decoding over `UInt8` and `Char`,
shared across `Contract.Export.Keccak`, `Compiler.Validation.Solidity`,
and `Compiler.Validation.Main` so hex syntax is specified in one place. -/
namespace Contract.Hex

def nibbleChar (n : UInt8) : Char :=
  if n == 0 then '0' else if n == 1 then '1' else if n == 2 then '2' else if n == 3 then '3'
  else if n == 4 then '4' else if n == 5 then '5' else if n == 6 then '6' else if n == 7 then '7'
  else if n == 8 then '8' else if n == 9 then '9' else if n == 10 then 'a' else if n == 11 then 'b'
  else if n == 12 then 'c' else if n == 13 then 'd' else if n == 14 then 'e' else 'f'

def charNibble? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (10 + (c.toNat - 'a'.toNat))
  else if 'A' ≤ c ∧ c ≤ 'F' then some (10 + (c.toNat - 'A'.toNat))
  else none

def encodeBytes (bytes : List UInt8) : String :=
  String.ofList <| bytes.foldr (fun b acc =>
    nibbleChar (b >>> (4 : UInt8)) :: nibbleChar (b &&& (0x0f : UInt8)) :: acc) []

def stripHexPrefix (chars : List Char) : List Char :=
  match chars with
  | '0' :: 'x' :: rest => rest
  | '0' :: 'X' :: rest => rest
  | _ => chars

def decodeBytes? (s : String) : Option (List UInt8) :=
  let rec go : List Char → List UInt8 → Option (List UInt8)
    | [], acc => some acc.reverse
    | [_], _ => none
    | hi :: lo :: rest, acc => do
      let h ← charNibble? hi
      let l ← charNibble? lo
      go rest (UInt8.ofNat (h * 16 + l) :: acc)
  go (stripHexPrefix s.toList) []

private theorem charNibble_nibbleChar (n : UInt8) (hn : n.toNat < 16) :
    charNibble? (nibbleChar n) = some n.toNat := by
  have hcases :
      n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
      n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 := by
    have : n.toNat = 0 ∨ n.toNat = 1 ∨ n.toNat = 2 ∨ n.toNat = 3 ∨
           n.toNat = 4 ∨ n.toNat = 5 ∨ n.toNat = 6 ∨ n.toNat = 7 ∨
           n.toNat = 8 ∨ n.toNat = 9 ∨ n.toNat = 10 ∨ n.toNat = 11 ∨
           n.toNat = 12 ∨ n.toNat = 13 ∨ n.toNat = 14 ∨ n.toNat = 15 := by omega
    rcases this with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl (UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h))
    · exact Or.inr (Or.inl (UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)))
    · exact Or.inr (Or.inr (Or.inl (UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h))))))))))))))))
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem nibbleChar_not_x (n : UInt8) :
    nibbleChar n ≠ 'x' ∧ nibbleChar n ≠ 'X' := by
  unfold nibbleChar
  by_cases h0 : n == 0 <;> simp only [h0, ↓reduceIte]
  · constructor <;> decide
  · by_cases h1 : n == 1 <;> simp only [h1, ↓reduceIte]
    · constructor <;> decide
    · by_cases h2 : n == 2 <;> simp only [h2, ↓reduceIte]
      · constructor <;> decide
      · by_cases h3 : n == 3 <;> simp only [h3, ↓reduceIte]
        · constructor <;> decide
        · by_cases h4 : n == 4 <;> simp only [h4, ↓reduceIte]
          · constructor <;> decide
          · by_cases h5 : n == 5 <;> simp only [h5, ↓reduceIte]
            · constructor <;> decide
            · by_cases h6 : n == 6 <;> simp only [h6, ↓reduceIte]
              · constructor <;> decide
              · by_cases h7 : n == 7 <;> simp only [h7, ↓reduceIte]
                · constructor <;> decide
                · by_cases h8 : n == 8 <;> simp only [h8, ↓reduceIte]
                  · constructor <;> decide
                  · by_cases h9 : n == 9 <;> simp only [h9, ↓reduceIte]
                    · constructor <;> decide
                    · by_cases h10 : n == 10 <;> simp only [h10, ↓reduceIte]
                      · constructor <;> decide
                      · by_cases h11 : n == 11 <;> simp only [h11, ↓reduceIte]
                        · constructor <;> decide
                        · by_cases h12 : n == 12 <;> simp only [h12, ↓reduceIte]
                          · constructor <;> decide
                          · by_cases h13 : n == 13 <;> simp only [h13, ↓reduceIte]
                            · constructor <;> decide
                            · by_cases h14 : n == 14 <;> simp only [h14, ↓reduceIte] <;> constructor <;> decide

private theorem stripHexPrefix_encode (bytes : List UInt8) :
    stripHexPrefix (bytes.foldr (fun b r =>
      nibbleChar (b >>> (4 : UInt8)) :: nibbleChar (b &&& (0x0f : UInt8)) :: r) []) =
    bytes.foldr (fun b r =>
      nibbleChar (b >>> (4 : UInt8)) :: nibbleChar (b &&& (0x0f : UInt8)) :: r) [] := by
  cases bytes with
  | nil => rfl
  | cons b bs =>
    have hnx := nibbleChar_not_x (b &&& (0x0f : UInt8))
    simp only [List.foldr_cons, stripHexPrefix]
    split
    · rename_i rest heq
      injection heq with _ htail
      injection htail with hx _
      exact absurd hx hnx.1
    · rename_i rest heq
      injection heq with _ htail
      injection htail with hx _
      exact absurd hx hnx.2
    · rfl

private theorem decode_go_encode (bytes acc : List UInt8) :
    decodeBytes?.go (bytes.foldr (fun b r =>
      nibbleChar (b >>> (4 : UInt8)) :: nibbleChar (b &&& (0x0f : UInt8)) :: r) []) acc =
      some (acc.reverse ++ bytes) := by
  induction bytes generalizing acc with
  | nil => simp [decodeBytes?.go]
  | cons b bs ih =>
    have hhi : (b >>> (4 : UInt8)).toNat < 16 := by
      have hb : b.toNat < 256 := b.toBitVec.isLt
      have hs : (b >>> (4 : UInt8)).toNat = b.toNat / 16 := by
        simp [Nat.shiftRight_eq_div_pow, UInt8.toNat_shiftRight]
      omega
    have hlo : (b &&& (0x0f : UInt8)).toNat < 16 := by
      have ha : (b &&& (0x0f : UInt8)).toNat = b.toNat % 16 := by
        have : (0x0f : UInt8).toNat = 2 ^ 4 - 1 := rfl
        rw [UInt8.toNat_and, this, Nat.and_two_pow_sub_one_eq_mod]
      omega
    have hrecomb : UInt8.ofNat ((b >>> (4 : UInt8)).toNat * 16 + (b &&& (0x0f : UInt8)).toNat) = b := by
      apply UInt8.eq_of_toBitVec_eq
      apply BitVec.eq_of_toNat_eq
      have hs : (b >>> (4 : UInt8)).toNat = b.toNat / 16 := by
        simp [Nat.shiftRight_eq_div_pow, UInt8.toNat_shiftRight]
      have ha : (b &&& (0x0f : UInt8)).toNat = b.toNat % 16 := by
        have : (0x0f : UInt8).toNat = 2 ^ 4 - 1 := rfl
        rw [UInt8.toNat_and, this, Nat.and_two_pow_sub_one_eq_mod]
      have hb : b.toNat < 256 := b.toBitVec.isLt
      have hdiv : b.toNat / 16 * 16 + b.toNat % 16 = b.toNat := by omega
      change ((b >>> (4 : UInt8)).toNat * 16 + (b &&& (0x0f : UInt8)).toNat) % 256 = b.toNat
      rw [hs, ha, hdiv]
      exact Nat.mod_eq_of_lt hb
    simp only [List.foldr_cons, decodeBytes?.go, charNibble_nibbleChar _ hhi,
      charNibble_nibbleChar _ hlo, bind, Option.bind_some, hrecomb]
    rw [ih (b :: acc)]
    simp [List.reverse_cons, List.append_assoc]

theorem decodeBytes_encodeBytes (bytes : List UInt8) :
    decodeBytes? (encodeBytes bytes) = some bytes := by
  unfold decodeBytes? encodeBytes
  rw [String.toList_ofList, stripHexPrefix_encode]
  simpa using decode_go_encode bytes []

theorem decodeBytes_0x_encodeBytes (bytes : List UInt8) :
    decodeBytes? ("0x" ++ encodeBytes bytes) = some bytes := by
  unfold decodeBytes? encodeBytes
  have hlist : ("0x" ++ String.ofList (bytes.foldr (fun b acc =>
      nibbleChar (b >>> (4 : UInt8)) :: nibbleChar (b &&& (0x0f : UInt8)) :: acc) [])).toList =
    '0' :: 'x' :: bytes.foldr (fun b acc =>
      nibbleChar (b >>> (4 : UInt8)) :: nibbleChar (b &&& (0x0f : UInt8)) :: acc) [] := by
    simp [String.toList_append, String.toList_ofList]
  rw [hlist, stripHexPrefix]
  simpa using decode_go_encode bytes []

#audit_contract_proof decodeBytes_encodeBytes
#audit_contract_proof decodeBytes_0x_encodeBytes

end Contract.Hex
