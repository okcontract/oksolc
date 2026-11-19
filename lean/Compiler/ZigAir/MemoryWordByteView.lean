/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WordBytes
import Compiler.ZigAir.MemoryWordArrayTypes

/-! Runtime byte views use the typed word's storage and initialization state.
No second heap or default bytes are introduced. -/
namespace Compiler.ZigAir.Memory.WordByteView
open WordArray

def read (order : WordBytes.Order) (state : State) (pointer : Value) (offset : Nat) : Except Fault (BitVec 8) :=
  if inside : offset < 4 then
    match load state pointer with
    | .error reason => .error reason
    | .ok (.scalar (.int false 32 value)) => .ok (WordBytes.read order (BitVec.ofInt 32 value) ⟨offset, inside⟩)
    | .ok _ => .error .unsupported
  else .error .sourceBounds

def write (order : WordBytes.Order) (state : State) (pointer : Value) (offset : Nat) (byte : BitVec 8) : Except Fault State :=
  if inside : offset < 4 then
    match load state pointer with
    | .error reason => .error reason
    | .ok (.scalar (.int false 32 value)) =>
      store state pointer (number (WordBytes.write order (BitVec.ofInt 32 value) ⟨offset, inside⟩ byte))
    | .ok _ => .error .unsupported
  else .error .sourceBounds

end Compiler.ZigAir.Memory.WordByteView
