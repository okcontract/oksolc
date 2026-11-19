/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Interaction.Basic

namespace Contract.Interaction

def bytesWord (xs : List UInt8) : Word :=
  BitVec.ofNat 256 (xs.foldl (fun n b => n * 256 + b.toNat) 0)

def wordBytes (w : Word) : List UInt8 :=
  (List.range 32).map fun i => (w.toNat / 256^(31-i) % 256).toUInt8

/-- Copy a byte source with zero padding. Positions use Nat addition, not
word arithmetic: an oversized source position cannot wrap to byte zero. -/
def readBytesPadded (bytes : List UInt8) (source size : Nat) : List UInt8 :=
  (List.range size).map fun i => (bytes[source+i]?).getD 0

@[simp] theorem readBytesPadded_length (bytes : List UInt8) (source size : Nat) :
    (readBytesPadded bytes source size).length = size := by simp [readBytesPadded]

@[simp] theorem readBytesPadded_zero (bytes : List UInt8) (source : Nat) :
    readBytesPadded bytes source 0 = [] := rfl

@[simp] theorem readBytesPadded_empty (source size : Nat) :
    readBytesPadded [] source size = List.replicate size 0 := by
  simp [readBytesPadded,List.map_const']

end Contract.Interaction
