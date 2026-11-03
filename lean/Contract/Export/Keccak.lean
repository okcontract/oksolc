/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Std

/-! Host-side Ethereum Keccak-256 for selectors and content identities. This
implements the Keccak team's permutation specification with 136-byte rate and
legacy suffix 0x01 (not SHA3's 0x06). Known-vector tests are not a cryptographic
correctness theorem. No hash operation is added to the contract language. -/
namespace Contract.Export.Keccak

private abbrev Lanes := Vector UInt64 25

private def lane (a : Lanes) (x y : Nat) : UInt64 :=
  a[(⟨x % 5 + 5 * (y % 5), by omega⟩ : Fin 25)]

private def rot (a : UInt64) (n : Nat) : UInt64 :=
  if n = 0 then a else (a <<< n.toUInt64) ||| (a >>> (64 - n).toUInt64)

private def offsets : Vector Nat 25 :=
  #v[0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39,
     41, 45, 15, 21, 8, 18, 2, 61, 56, 14]

private def constants : List UInt64 := [
  0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
  0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
  0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

private def round (a : Lanes) (rc : UInt64) : Lanes := Id.run do
  let c : Vector UInt64 5 := Vector.ofFn fun x =>
    lane a x.val 0 ^^^ lane a x.val 1 ^^^ lane a x.val 2 ^^^ lane a x.val 3 ^^^ lane a x.val 4
  let theta : Lanes := Vector.ofFn fun i =>
    let x := i.val % 5
    a[i] ^^^ c[(⟨(x + 4) % 5, by omega⟩ : Fin 5)] ^^^
      rot c[(⟨(x + 1) % 5, by omega⟩ : Fin 5)] 1
  let b : Lanes := Vector.ofFn fun i =>
    let x := i.val % 5
    let y := i.val / 5
    let source : Fin 25 := ⟨(x + 3 * y) % 5 + 5 * x, by omega⟩
    rot theta[source] offsets[source]
  return Vector.ofFn fun i =>
    let x := i.val % 5
    let y := i.val / 5
    let value := lane b x y ^^^ ((~~~lane b (x + 1) y) &&& lane b (x + 2) y)
    if i.val = 0 then value ^^^ rc else value

private def permute (a : Lanes) : Lanes := constants.foldl round a

def hash (input : ByteArray) : ByteArray := Id.run do
  let blocks := input.size / 136 + 1
  let paddedSize := blocks * 136
  let byteAt (i : Nat) : UInt8 :=
    (if h : i < input.size then input[i] else if i = input.size then 1 else 0) ^^^
      (if i + 1 = paddedSize then 0x80 else 0)
  let mut state : Lanes := Vector.replicate 25 0
  for block in [:blocks] do
    let absorbed : Lanes := Vector.ofFn fun i =>
      if i.val < 17 then
        let word := (List.range 8).foldl (fun (v : UInt64) j =>
          v ||| ((byteAt (block * 136 + i.val * 8 + j)).toUInt64 <<< (8 * j).toUInt64)) 0
        state[i] ^^^ word
      else state[i]
    state := permute absorbed
  return ⟨(List.range 32).toArray.map fun i =>
    (state[(⟨i / 8 % 25, by omega⟩ : Fin 25)] >>> (8 * (i % 8)).toUInt64).toUInt8⟩

def hex (bytes : ByteArray) : String :=
  bytes.foldl (fun s b => s ++ String.ofList [
    "0123456789abcdef".toList[b.toNat / 16]!,
    "0123456789abcdef".toList[b.toNat % 16]!]) ""

def selector (signature : String) : Nat :=
  ((hash signature.toUTF8).extract 0 4).foldl (fun n b => n * 256 + b.toNat) 0

end Contract.Export.Keccak
