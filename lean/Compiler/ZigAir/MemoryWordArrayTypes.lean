/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.Memory

namespace Compiler.ZigAir.Memory.WordArray

abbrev word : Ty := .scalar (.int false 32)
def number (n : BitVec 32) : Value := .scalar (.int false 32 n.toNat)

structure View where
  allocation : Nat
  first : Nat
  length : Nat
  deriving DecidableEq, Repr

def View.address (view : View) (index : Nat) : Address :=
  ⟨view.allocation, (view.first + index) * 4⟩

def View.pointer (view : View) (index : Nat) : Value :=
  .pointer (.pointer true false word) (view.address index)

def View.buffer (view : View) : Value :=
  .pointer (.pointer true true word) (view.address 0)

def Writable (state : State) (view : View) : Prop :=
  ∃ extent cell, state.heap.lookup view.allocation = some cell ∧
    cell.type = .array extent word ∧ cell.writable = true ∧
    view.first + view.length ≤ extent

end Compiler.ZigAir.Memory.WordArray
