/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Std

namespace Contract

/-- Unsigned EVM word operations. Division/remainder by zero yield zero;
shift counts at least 256 yield zero, without materializing a huge host shift. -/
inductive WordOp where
  | mul | div | mod | and | or | xor | shl | shr
  deriving DecidableEq, Repr

def WordOp.eval : WordOp → BitVec 256 → BitVec 256 → BitVec 256
  | .mul, a, b => a * b
  | .div, a, b => a / b
  | .mod, a, b => if b = 0 then 0 else a % b
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b
  | .shl, a, b => if b.toNat < 256 then a <<< b.toNat else 0
  | .shr, a, b => if b.toNat < 256 then a >>> b.toNat else 0

inductive CheckedOp where
  | add | sub | mul | div | mod
  deriving DecidableEq, Repr

/-- ABI encoding of Panic(uint256); codes 1, 0x11 and 0x12 are used below. -/
def panic (code : UInt8) : List UInt8 := [0x4e, 0x48, 0x7b, 0x71] ++ List.replicate 31 0 ++ [code]

def CheckedOp.eval (op : CheckedOp) (a b : BitVec 256) : Except (List UInt8) (BitVec 256) :=
  match op with
  | .add => if a.toNat + b.toNat < 2^256 then .ok (a + b) else .error (panic 0x11)
  | .sub => if b ≤ a then .ok (a - b) else .error (panic 0x11)
  | .mul => if a.toNat * b.toNat < 2^256 then .ok (a * b) else .error (panic 0x11)
  | .div => if b = 0 then .error (panic 0x12) else .ok (a / b)
  | .mod => if b = 0 then .error (panic 0x12) else .ok (a % b)

end Contract
