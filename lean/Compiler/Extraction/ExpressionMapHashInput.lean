/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapSearchMemory

namespace Compiler.Extraction.ExpressionMap.HashInput
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray
open Compiler.Extraction.Cache (Key)

/-- The captured target is little-endian. The c_int tag occupies four bytes;
only scalar representation bytes are included, never key padding or pointers. -/
def word (value : BitVec 32) : List (BitVec 8) :=
  (List.finRange 4).map (Compiler.ZigAir.WordBytes.read .little value)

def data (value : BitVec 256) : List (BitVec 8) :=
  (List.range 32).map (fun index => BitVec.ofNat 8 (value.toNat / 256 ^ index))

/-- Use the same initialized word-byte codec as native argument comparison. -/
def arguments (values : List (BitVec 32)) : List (BitVec 8) :=
  (List.range (values.length * 4)).map (ArgumentScan.encoded (fun i => values[i]?.getD 0) 0)

/-- The exact five update boundaries in ExpressionKeyContext.hash. This is a
byte-image specification, not an implementation of incremental Wyhash. -/
def encode (key : Key) : List (List (BitVec 8)) :=
  [word key.kind, [key.instruction], data key.data, arguments key.arguments, word key.sequence]

/-- Observe actual argument bytes through the existing typed heap. By-value
scalar fields have fixed widths; the source slice's byte extent is checked before
its bytes are read. The digest and its local buffers are outside this operation. -/
def read (state : State) (key : Key) (source : View) : Except Fault (List (List (BitVec 8))) := do
  if ¬source.length * 4 < addressLimit then .error .memoryValidity else do
  let bytes ← ArgumentScan.bytes state source 0 (List.range (source.length * 4))
  .ok [word key.kind, [key.instruction], data key.data, bytes, word key.sequence]

theorem shape (key : Key) : (encode key).map List.length = [4, 1, 32, key.arguments.length * 4, 4] := by
  simp [encode, word, data, arguments]

theorem total_length (key : Key) : (encode key).flatten.length = 41 + key.arguments.length * 4 := by
  simp [encode, word, data, arguments]
  omega

/-- No argument byte or chosen byte image is supplied. This same initialized
word-byte observation is consumed after the captured slice helper returns. -/
theorem arguments_read_verified (state : State) (source : View) (items : List (BitVec 32))
    (represented : Represents state source items) :
    ArgumentScan.bytes state source 0 (List.range (source.length * 4)) = .ok (arguments items) := by
  have reads (offset : Nat) (member : offset ∈ List.range (source.length * 4)) :
      load state (source.pointer (0 + offset / 4)) =
        .ok (number (items[offset / 4]?.getD 0)) := by
    have inside : offset / 4 < items.length := by
      have := List.mem_range.mp member
      have := represented.1
      omega
    simpa only [Nat.zero_add, List.getElem?_eq_getElem inside, Option.getD_some] using represented.2 (offset / 4) inside
  have observed := ArgumentScan.bytes_verified state source 0 (List.range (source.length * 4))
    (fun i => items[i]?.getD 0) (by simpa only [Nat.zero_add] using reads)
  simpa only [← represented.1, arguments] using observed

theorem read_verified (state : State) (key : Key) (source : View)
    (represented : Represents state source key.arguments) (bounded : source.length * 4 < addressLimit) :
    read state key source = .ok (encode key) := by
  simp only [read, if_neg (not_not_intro bounded), arguments_read_verified state source key.arguments represented,
    bind, Except.bind, encode]

theorem oversized_rejected (state : State) (key : Key) (source : View)
    (oversized : addressLimit ≤ source.length * 4) : read state key source = .error .memoryValidity := by
  simp only [read, if_pos (by omega : ¬source.length * 4 < addressLimit)]

end Compiler.Extraction.ExpressionMap.HashInput
