/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryScalarBytes
import Compiler.ZigAir.MemoryStackFrame

/-! Byte-range operations for captured AIR. Reads resolve the original typed
integer leaves; padding and undefined storage never acquire invented bytes.
Writes use the ordinary byte store. A failed copy retains its completed prefix.
The caller's slice checks and the non-overlap requirement remain explicit. -/
namespace Compiler.ZigAir.Memory.ByteRange

def byte : Ty := .scalar (.int false 8)

def read (state : State) (address : Address) (count : Nat) : Except Fault (List (BitVec 8)) :=
  (List.range count).mapM fun index => ScalarBytes.readAt state
    { address with offset := address.offset + index }

def copyByte (state : State) (source target : Address) (index : Nat) : Except Fault State := do
  let bits ← ScalarBytes.readAt state { source with offset := source.offset + index }
  store state (.pointer (.pointer true false byte)
    { target with offset := target.offset + index }) (.scalar (.int false 8 bits.toNat))

def copyLoop (state : State) (source target : Address) (index : Nat) :
    Nat → Except Fault Unit × State
  | 0 => (.ok (), state)
  | count + 1 =>
    match copyByte state source target index with
    | .error fault => (.error fault, state)
    | .ok after => copyLoop after source target (index + 1) count

def destination : Value → Except Fault (Address × Nat)
  | .slice (.slice true (.scalar (.int false 8))) address count => .ok (address, count)
  | .pointer (.pointer true false (.array count (.scalar (.int false 8)))) address => .ok (address, count)
  | .slice (.slice false _) _ _ | .pointer (.pointer false _ _) _ => .error .readOnly
  | _ => .error .unsupported

def source (value : Value) (count : Nat) : Except Fault Address := do
  match value with
  | .pointer (.pointer _ true (.scalar (.int false 8))) address => .ok address
  | .pointer (.pointer _ false (.array length (.scalar (.int false 8)))) address
  | .slice (.slice _ (.scalar (.int false 8))) address length =>
    if count = length then .ok address else .error .sourceBounds
  | _ => .error .unsupported

def copy (state : State) (target input : Value) : Except Fault Unit × State :=
  match destination target with
  | .error fault => (.error fault, state)
  | .ok (dest, count) =>
    match source input count with
    | .error fault => (.error fault, state)
    | .ok src =>
      if count > 0 ∧ src.allocation = dest.allocation ∧
          src.offset < dest.offset + count ∧ dest.offset < src.offset + count then
        (.error .memoryValidity, state)
      else copyLoop state src dest 0 count

theorem copyByte_valid (state after : State) (source target : Address) (index : Nat)
    (initial : state.valid = true) (copied : copyByte state source target index = .ok after) :
    after.valid = true := by
  unfold copyByte at copied
  cases read : ScalarBytes.readAt state { source with offset := source.offset + index } with
  | error fault =>
    simp only [read, bind, Except.bind] at copied
    cases copied
  | ok bits =>
    simp only [read, bind, Except.bind] at copied
    exact store_preserves_valid _ _ _ _ initial copied

theorem copyLoop_valid (state : State) (source target : Address) (index count : Nat)
    (initial : state.valid = true) : (copyLoop state source target index count).2.valid = true := by
  induction count generalizing state index with
  | zero => exact initial
  | succ count ih =>
    rw [copyLoop]
    cases copied : copyByte state source target index with
    | error fault => exact initial
    | ok after => exact ih after (index + 1) (copyByte_valid _ _ _ _ _ initial copied)

theorem copy_valid (state : State) (target input : Value) (initial : state.valid = true) :
    (copy state target input).2.valid = true := by
  unfold copy
  split
  · exact initial
  · split
    · exact initial
    · split
      · exact initial
      · exact copyLoop_valid _ _ _ _ _ initial

end Compiler.ZigAir.Memory.ByteRange
