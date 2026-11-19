/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryWordByteView

/-! Representation-aware byte operations for u32 subobjects. Ordinary byte
pointers retain the allocation identity and byte offset. Resolving a byte to
its containing word uses checked typed storage; padding, pointer bytes and
partially initialized words remain unsupported. The target byte order and
cast alignment are explicit operands, never inferred from the Lean host. -/
namespace Compiler.ZigAir.Memory.ByteAccess
open WordArray

def byte : Ty := .scalar (.int false 8)
def number (value : BitVec 8) : Value := .scalar (.int false 8 value.toNat)
def pointer (writable many : Bool) (address : Address) : Value := .pointer (.pointer writable many byte) address

def wordAddress (address : Address) : Address :=
  { address with offset := address.offset / 4 * 4 }
def wordPointer (writable : Bool) (address : Address) : Value :=
  .pointer (.pointer writable false word) (wordAddress address)

/-- A u32 cast can retain or weaken its ABI alignment. It cannot invent a
stronger alignment, upgrade constness or manufacture a typed subobject. The
cast itself does not read the word and therefore permits uninitialized storage. -/
def cast (state : State) (writable many : Bool) (alignment : Nat) (source : Value) : Except Fault Value := do
  let .pointer (.pointer sourceWritable _ (.scalar (.int false 32))) address := source | .error .unsupported
  if writable && !sourceWritable then .error .readOnly else
  if alignment ≠ 1 ∧ alignment ≠ 2 ∧ alignment ≠ 4 then .error .unsupported else
  let cell ← access state address ⟨4, 4⟩ false
  if !acceptsView cell.type address.offset word then .error .unsupported else
  if (cell.base + address.offset) % alignment ≠ 0 then .error .memoryValidity else
  .ok (pointer writable many address)

/-- Only initialized u32 representations are admitted. A genuine byte array
continues to use the ordinary typed load operation. -/
def read (order : WordBytes.Order) (state : State) (source : Value) : Except Fault Value := do
  let .pointer (.pointer writable _ (.scalar (.int false 8))) address := source | .error .unsupported
  let value ← WordByteView.read order state (wordPointer writable address) (address.offset % 4)
  .ok (number value)

def write (order : WordBytes.Order) (state : State) (destination value : Value) : Except Fault State := do
  let .pointer (.pointer writable _ (.scalar (.int false 8))) address := destination | .error .unsupported
  let .scalar (.int false 8 bits) := value | .error .malformed
  if !value.valid then .error .malformed else
  WordByteView.write order state (wordPointer writable address) (address.offset % 4) (BitVec.ofInt 8 bits)

/-- Successful byte writes expose one actual typed store. This equation is
available below the AIR invariant layer, avoiding a proof/interpreter cycle. -/
theorem write_store (order : WordBytes.Order) (state after : State) (destination value : Value)
    (success : write order state destination value = .ok after) :
    ∃ wordPointer wordValue, store state wordPointer wordValue = .ok after := by
  unfold write at success
  repeat' first | split at success | contradiction
  rename_i writable many address bits valid
  unfold WordByteView.write at success
  split at success
  · split at success
    · contradiction
    · exact ⟨_, _, success⟩
    · contradiction
  · contradiction

end Compiler.ZigAir.Memory.ByteAccess
