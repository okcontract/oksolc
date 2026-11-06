/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Check.Axioms

/-! Ethereum Keccak-256 (136-byte sponge rate, 24-round Keccak-f[1600]
permutation, legacy `0x01` domain separator rather than FIPS-202 SHA-3 `0x06`).
Representing the 5×5 state as an explicit 25-lane structure eliminates dependent
index proofs from kernel reduction, enabling pure `rfl` kernel verification of
standard Ethereum vectors and sponge-rate boundaries without `native_decide`. -/
namespace Contract.Export.Keccak

structure Lanes where
  l00 : UInt64 := 0
  l10 : UInt64 := 0
  l20 : UInt64 := 0
  l30 : UInt64 := 0
  l40 : UInt64 := 0
  l01 : UInt64 := 0
  l11 : UInt64 := 0
  l21 : UInt64 := 0
  l31 : UInt64 := 0
  l41 : UInt64 := 0
  l02 : UInt64 := 0
  l12 : UInt64 := 0
  l22 : UInt64 := 0
  l32 : UInt64 := 0
  l42 : UInt64 := 0
  l03 : UInt64 := 0
  l13 : UInt64 := 0
  l23 : UInt64 := 0
  l33 : UInt64 := 0
  l43 : UInt64 := 0
  l04 : UInt64 := 0
  l14 : UInt64 := 0
  l24 : UInt64 := 0
  l34 : UInt64 := 0
  l44 : UInt64 := 0
  deriving DecidableEq, Repr

private def rot (a l r : UInt64) : UInt64 :=
  (a <<< l) ||| (a >>> r)

private def constants : List UInt64 := [
  0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
  0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
  0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

private def round (a : Lanes) (rc : UInt64) : Lanes :=
  -- θ (theta)
  let c0 := a.l00 ^^^ a.l01 ^^^ a.l02 ^^^ a.l03 ^^^ a.l04
  let c1 := a.l10 ^^^ a.l11 ^^^ a.l12 ^^^ a.l13 ^^^ a.l14
  let c2 := a.l20 ^^^ a.l21 ^^^ a.l22 ^^^ a.l23 ^^^ a.l24
  let c3 := a.l30 ^^^ a.l31 ^^^ a.l32 ^^^ a.l33 ^^^ a.l34
  let c4 := a.l40 ^^^ a.l41 ^^^ a.l42 ^^^ a.l43 ^^^ a.l44
  let d0 := c4 ^^^ rot c1 1 63
  let d1 := c0 ^^^ rot c2 1 63
  let d2 := c1 ^^^ rot c3 1 63
  let d3 := c2 ^^^ rot c4 1 63
  let d4 := c3 ^^^ rot c0 1 63
  -- ρ (rho)
  let t00 := a.l00 ^^^ d0
  let t10 := rot (a.l10 ^^^ d1) 1 63
  let t20 := rot (a.l20 ^^^ d2) 62 2
  let t30 := rot (a.l30 ^^^ d3) 28 36
  let t40 := rot (a.l40 ^^^ d4) 27 37
  let t01 := rot (a.l01 ^^^ d0) 36 28
  let t11 := rot (a.l11 ^^^ d1) 44 20
  let t21 := rot (a.l21 ^^^ d2) 6 58
  let t31 := rot (a.l31 ^^^ d3) 55 9
  let t41 := rot (a.l41 ^^^ d4) 20 44
  let t02 := rot (a.l02 ^^^ d0) 3 61
  let t12 := rot (a.l12 ^^^ d1) 10 54
  let t22 := rot (a.l22 ^^^ d2) 43 21
  let t32 := rot (a.l32 ^^^ d3) 25 39
  let t42 := rot (a.l42 ^^^ d4) 39 25
  let t03 := rot (a.l03 ^^^ d0) 41 23
  let t13 := rot (a.l13 ^^^ d1) 45 19
  let t23 := rot (a.l23 ^^^ d2) 15 49
  let t33 := rot (a.l33 ^^^ d3) 21 43
  let t43 := rot (a.l43 ^^^ d4) 8 56
  let t04 := rot (a.l04 ^^^ d0) 18 46
  let t14 := rot (a.l14 ^^^ d1) 2 62
  let t24 := rot (a.l24 ^^^ d2) 61 3
  let t34 := rot (a.l34 ^^^ d3) 56 8
  let t44 := rot (a.l44 ^^^ d4) 14 50
  -- π (pi)
  let b00 := t00; let b10 := t11; let b20 := t22; let b30 := t33; let b40 := t44
  let b01 := t30; let b11 := t41; let b21 := t02; let b31 := t13; let b41 := t24
  let b02 := t10; let b12 := t21; let b22 := t32; let b32 := t43; let b42 := t04
  let b03 := t40; let b13 := t01; let b23 := t12; let b33 := t23; let b43 := t34
  let b04 := t20; let b14 := t31; let b24 := t42; let b34 := t03; let b44 := t14
  -- χ (chi) and ι (iota)
  { l00 := (b00 ^^^ ((~~~b10) &&& b20)) ^^^ rc
    l10 := b10 ^^^ ((~~~b20) &&& b30)
    l20 := b20 ^^^ ((~~~b30) &&& b40)
    l30 := b30 ^^^ ((~~~b40) &&& b00)
    l40 := b40 ^^^ ((~~~b00) &&& b10)
    l01 := b01 ^^^ ((~~~b11) &&& b21)
    l11 := b11 ^^^ ((~~~b21) &&& b31)
    l21 := b21 ^^^ ((~~~b31) &&& b41)
    l31 := b31 ^^^ ((~~~b41) &&& b01)
    l41 := b41 ^^^ ((~~~b01) &&& b11)
    l02 := b02 ^^^ ((~~~b12) &&& b22)
    l12 := b12 ^^^ ((~~~b22) &&& b32)
    l22 := b22 ^^^ ((~~~b32) &&& b42)
    l32 := b32 ^^^ ((~~~b42) &&& b02)
    l42 := b42 ^^^ ((~~~b02) &&& b12)
    l03 := b03 ^^^ ((~~~b13) &&& b23)
    l13 := b13 ^^^ ((~~~b23) &&& b33)
    l23 := b23 ^^^ ((~~~b33) &&& b43)
    l33 := b33 ^^^ ((~~~b43) &&& b03)
    l43 := b43 ^^^ ((~~~b03) &&& b13)
    l04 := b04 ^^^ ((~~~b14) &&& b24)
    l14 := b14 ^^^ ((~~~b24) &&& b34)
    l24 := b24 ^^^ ((~~~b34) &&& b44)
    l34 := b34 ^^^ ((~~~b44) &&& b04)
    l44 := b44 ^^^ ((~~~b04) &&& b14) }

private def permute (a : Lanes) : Lanes := constants.foldl round a

private def packLane : List UInt8 → UInt64 × List UInt8
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
    (b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24) |||
     (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) ||| (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56), rest)
  | _ => (0, [])

private def absorbBlock (s : Lanes) (bytes : List UInt8) : Lanes × List UInt8 :=
  let (w00, r) := packLane bytes
  let (w10, r) := packLane r
  let (w20, r) := packLane r
  let (w30, r) := packLane r
  let (w40, r) := packLane r
  let (w01, r) := packLane r
  let (w11, r) := packLane r
  let (w21, r) := packLane r
  let (w31, r) := packLane r
  let (w41, r) := packLane r
  let (w02, r) := packLane r
  let (w12, r) := packLane r
  let (w22, r) := packLane r
  let (w32, r) := packLane r
  let (w42, r) := packLane r
  let (w03, r) := packLane r
  let (w13, r) := packLane r
  (permute { s with
    l00 := s.l00 ^^^ w00, l10 := s.l10 ^^^ w10, l20 := s.l20 ^^^ w20, l30 := s.l30 ^^^ w30, l40 := s.l40 ^^^ w40
    l01 := s.l01 ^^^ w01, l11 := s.l11 ^^^ w11, l21 := s.l21 ^^^ w21, l31 := s.l31 ^^^ w31, l41 := s.l41 ^^^ w41
    l02 := s.l02 ^^^ w02, l12 := s.l12 ^^^ w12, l22 := s.l22 ^^^ w22, l32 := s.l32 ^^^ w32, l42 := s.l42 ^^^ w42
    l03 := s.l03 ^^^ w03, l13 := s.l13 ^^^ w13 }, r)

private def absorbAll : Nat → Lanes → List UInt8 → Lanes
  | 0, s, _ => s
  | _ + 1, s, [] => s
  | fuel + 1, s, bytes =>
    let (s', rest) := absorbBlock s bytes
    absorbAll fuel s' rest

private def pad101 (input : List UInt8) : List UInt8 :=
  let rem := input.length % 136
  if rem = 135 then input ++ [0x81]
  else input ++ (0x01 :: List.replicate (134 - rem) 0x00) ++ [0x80]

private def unpackLane (w : UInt64) : List UInt8 :=
  [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8,
   (w >>> 32).toUInt8, (w >>> 40).toUInt8, (w >>> 48).toUInt8, (w >>> 56).toUInt8]

def hashBytes (input : List UInt8) : List UInt8 :=
  let padded := pad101 input
  let s := absorbAll (input.length / 136 + 1) {} padded
  unpackLane s.l00 ++ unpackLane s.l10 ++ unpackLane s.l20 ++ unpackLane s.l30

def hash (input : ByteArray) : ByteArray := ⟨(hashBytes input.toList).toArray⟩

private def hexDigit (n : UInt8) : Char :=
  if n == 0 then '0' else if n == 1 then '1' else if n == 2 then '2' else if n == 3 then '3'
  else if n == 4 then '4' else if n == 5 then '5' else if n == 6 then '6' else if n == 7 then '7'
  else if n == 8 then '8' else if n == 9 then '9' else if n == 10 then 'a' else if n == 11 then 'b'
  else if n == 12 then 'c' else if n == 13 then 'd' else if n == 14 then 'e' else 'f'

def hexBytes (bytes : List UInt8) : String :=
  String.ofList <| bytes.foldr (fun b acc =>
    hexDigit (b >>> (4 : UInt8)) :: hexDigit (b &&& (0x0f : UInt8)) :: acc) []

def hex (bytes : ByteArray) : String := hexBytes bytes.toList

def asciiBytes (s : String) : List UInt8 :=
  s.toList.map fun c => UInt8.ofNat c.toNat

def selectorBits (bytes : List UInt8) : BitVec 32 :=
  match hashBytes bytes with
  | b0 :: b1 :: b2 :: b3 :: _ =>
    (b0.toBitVec.zeroExtend 32 <<< 24) |||
    (b1.toBitVec.zeroExtend 32 <<< 16) |||
    (b2.toBitVec.zeroExtend 32 <<< 8) |||
    b3.toBitVec.zeroExtend 32
  | _ => 0#32

def selector (signature : String) : Nat :=
  (selectorBits signature.toUTF8.toList).toNat

theorem hashBytes_length (input : List UInt8) : (hashBytes input).length = 32 := rfl

theorem selector_lt (signature : String) : selector signature < 2 ^ 32 :=
  (selectorBits signature.toUTF8.toList).isLt

-- Kernel-checked Ethereum Keccak-256 vectors (`decide` reduces purely inside the Lean kernel).
theorem keccak256_empty :
    hashBytes [] =
      [0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c,
       0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0,
       0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b,
       0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70] := by decide

theorem keccak256_abc :
    hashBytes [0x61, 0x62, 0x63] =
      [0x4e, 0x03, 0x65, 0x7a, 0xea, 0x45, 0xa9, 0x4f,
       0xc7, 0xd4, 0x7b, 0xa8, 0x26, 0xc8, 0xd6, 0x67,
       0xc0, 0xd1, 0xe6, 0xe3, 0x3a, 0x64, 0xa0, 0x36,
       0xec, 0x44, 0xf5, 0x8f, 0xa1, 0x2d, 0x6c, 0x45] := by decide

-- ASCII bytes of "transfer(address,uint256)" -> selector 0xa9059cbb.
set_option maxRecDepth 200000 in
theorem keccak256_erc20_transfer_selector :
    (hashBytes
      [0x74, 0x72, 0x61, 0x6e, 0x73, 0x66, 0x65, 0x72, 0x28, 0x61, 0x64, 0x64, 0x72,
       0x65, 0x73, 0x73, 0x2c, 0x75, 0x69, 0x6e, 0x74, 0x32, 0x35, 0x36, 0x29]).take 4 =
      [0xa9, 0x05, 0x9c, 0xbb] := by decide

theorem pad101_rate_boundaries (input : List UInt8) :
    (pad101 input).length % 136 = 0 ∧ input.length < (pad101 input).length := by
  dsimp [pad101]
  have hrem : input.length % 136 < 136 := Nat.mod_lt _ (by omega)
  split <;> simp [List.length_append, List.length_replicate] <;> omega

#audit_contract_proof keccak256_empty
#audit_contract_proof keccak256_abc
#audit_contract_proof keccak256_erc20_transfer_selector
#audit_contract_proof selector_lt
#audit_contract_proof pad101_rate_boundaries

end Contract.Export.Keccak
