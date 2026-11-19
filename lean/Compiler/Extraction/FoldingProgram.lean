/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.Folding

namespace Compiler.Extraction.Folding
open Contract.Yul

-- Source SHA-256: 4f77329fcde8c89bb2429491fd7f8545f343c04b6630065c919e558c460fbf6d
-- Opcodes SHA-256: 49798b18d069e27354224c7aa6f551399c2b4bf3612bb7e1b55dacc764751ea2

def signedDivision (left right : Word) : Result :=
  if right = 0 then .ok 0
  else if left.toInt = -(2 ^ 255) ∧ right.toInt = -1 then .ok left
  else Zig.divTrunc left right

def signedModulo (left right : Word) : Result :=
  if right = 0 then .ok 0
  else if right.toInt = 1 ∨ right.toInt = -1 then .ok 0
  else Zig.rem left right

def powerLoop : Nat → Word → Word → Word → Result
  | 0, _, exponent, result => if exponent = 0 then .ok result else .error .recursionLimit
  | fuel + 1, base, exponent, result =>
    if exponent = 0 then .ok result else
      powerLoop fuel (base * base) (exponent >>> 1)
        (if (exponent &&& 1) ≠ 0 then result * base else result)

def wrappingPower (base exponent : Word) : Result := powerLoop 256 base exponent 1

def byteValue (index value : Word) : Result := do
  if index.toNat ≥ 32 then return 0
  let distance ← Zig.checkedSub 31 index.toNat
  let wide ← Zig.checkedMul 256 8 distance
  let shift ← Zig.narrow 8 wide
  return (value >>> shift) &&& 255

def addMod (left right modulus : Word) : Result := do
  if modulus = 0 then return 0
  let sum ← Zig.checkedAdd 257 (left.setWidth 257).toNat (right.setWidth 257).toNat
  let result ← Zig.narrow 256 (sum % (modulus.setWidth 257).toNat)
  return BitVec.ofNat 256 result

def mulMod (left right modulus : Word) : Result := do
  if modulus = 0 then return 0
  let product ← Zig.checkedMul 512 (left.setWidth 512).toNat (right.setWidth 512).toNat
  let result ← Zig.narrow 256 (product % (modulus.setWidth 512).toNat)
  return BitVec.ofNat 256 result

def signExtend (index value : Word) : Result := do
  if index.toNat ≥ 31 then return value
  let times ← Zig.checkedMul 256 index.toNat 8
  let wide ← Zig.checkedAdd 256 times 7
  let testBit ← Zig.narrow 8 wide
  let high : Word := (1 : Word) <<< testBit
  let low ← Zig.checkedSub high.toNat 1
  let mask := BitVec.ofNat 256 low
  return if (value &&& high) ≠ 0 then value ||| ~~~mask else value &&& mask

def shiftLeft (amount value : Word) : Result := do
  if amount.toNat ≥ 256 then return 0
  let shift ← Zig.narrow 8 amount.toNat
  return value <<< shift

def shiftRight (amount value : Word) : Result := do
  if amount.toNat ≥ 256 then return 0
  let shift ← Zig.narrow 8 amount.toNat
  return value >>> shift

def helpers : Helpers := ⟨signedDivision, signedModulo, wrappingPower, byteValue, addMod, mulMod, signExtend, shiftLeft, shiftRight⟩

def clauses : List Clause := [
  { opcode := 1, arity := 2, body := { op := .add, indices := [0, 1], zeroGuard := none } },
  { opcode := 2, arity := 2, body := { op := .mul, indices := [0, 1], zeroGuard := none } },
  { opcode := 3, arity := 2, body := { op := .sub, indices := [0, 1], zeroGuard := none } },
  { opcode := 4, arity := 2, body := { op := .div, indices := [0, 1], zeroGuard := some (1, 0) } },
  { opcode := 5, arity := 2, body := { op := .sdiv, indices := [0, 1], zeroGuard := none } },
  { opcode := 6, arity := 2, body := { op := .mod, indices := [0, 1], zeroGuard := some (1, 0) } },
  { opcode := 7, arity := 2, body := { op := .smod, indices := [0, 1], zeroGuard := none } },
  { opcode := 10, arity := 2, body := { op := .exp, indices := [0, 1], zeroGuard := none } },
  { opcode := 25, arity := 1, body := { op := .not, indices := [0], zeroGuard := none } },
  { opcode := 16, arity := 2, body := { op := .lt, indices := [0, 1], zeroGuard := none } },
  { opcode := 17, arity := 2, body := { op := .gt, indices := [0, 1], zeroGuard := none } },
  { opcode := 18, arity := 2, body := { op := .slt, indices := [0, 1], zeroGuard := none } },
  { opcode := 19, arity := 2, body := { op := .sgt, indices := [0, 1], zeroGuard := none } },
  { opcode := 20, arity := 2, body := { op := .eq, indices := [0, 1], zeroGuard := none } },
  { opcode := 21, arity := 1, body := { op := .iszero, indices := [0], zeroGuard := none } },
  { opcode := 22, arity := 2, body := { op := .and, indices := [0, 1], zeroGuard := none } },
  { opcode := 23, arity := 2, body := { op := .or, indices := [0, 1], zeroGuard := none } },
  { opcode := 24, arity := 2, body := { op := .xor, indices := [0, 1], zeroGuard := none } },
  { opcode := 26, arity := 2, body := { op := .byte, indices := [0, 1], zeroGuard := none } },
  { opcode := 8, arity := 3, body := { op := .addmod, indices := [0, 1, 2], zeroGuard := none } },
  { opcode := 9, arity := 3, body := { op := .mulmod, indices := [0, 1, 2], zeroGuard := none } },
  { opcode := 11, arity := 2, body := { op := .signextend, indices := [0, 1], zeroGuard := none } },
  { opcode := 27, arity := 2, body := { op := .shl, indices := [0, 1], zeroGuard := none } },
  { opcode := 28, arity := 2, body := { op := .shr, indices := [0, 1], zeroGuard := none } }]

end Compiler.Extraction.Folding
