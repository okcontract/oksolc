/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Validation.SolidityWord
import Contract.Proofs.Words
import Contract.Interaction.MemoryProofs

/-! Checked evaluation of the same resolved uint256 expression tree. Overflow
propagates the shared Solidity Panic(0x11) bytes. Bitwise and shift operations
retain their unchecked word semantics. There are no effects or other panic
codes in this fragment, so operand evaluation order is unobservable. -/
namespace Compiler.Validation.SolidityWord
open Contract.Yul

def Binary.evalChecked (op : Binary) (a b : Word) : Except (List UInt8) Word :=
  match op with
  | .add => Contract.CheckedOp.add.eval a b
  | .sub => Contract.CheckedOp.sub.eval a b
  | .mul => Contract.CheckedOp.mul.eval a b
  | other => .ok (other.eval a b)

def Expr.evalChecked (locals : String → Word) : Expr → Except (List UInt8) Word
  | .literal n => .ok (BitVec.ofNat 256 n)
  | .input name => .ok (locals name)
  | .bitnot arg => do return ~~~(← arg.evalChecked locals)
  | .binary op a b => do op.evalChecked (← a.evalChecked locals) (← b.evalChecked locals)

theorem add_guard_le (a b : Word) :
    a.toNat ≤ (a.toNat + b.toNat) % 2^256 ↔ a.toNat + b.toNat < 2^256 := by
  have ha := a.isLt
  have hb := b.isLt
  omega

theorem shift_one (a : Word) : a <<< 1 = 2#256 * a := by
  simpa only [show BitVec.twoPow 256 1 = 2#256 from rfl, BitVec.mul_comm] using
    BitVec.shiftLeft_eq_mul_twoPow a 1

theorem division (a b : Word) : (if b = 0#256 then 0#256 else a / b) = a / b := by
  by_cases zero : b = 0#256 <;> simp [zero]

theorem mul_guard (a b : Word) :
    (a ≠ 0#256 → a * b / a = b) ↔
      a.toNat * b.toNat < 2^256 := by
  have checked := Contract.WordProofs.multiplication_guard_exact b a
  by_cases zero : a = 0#256
  · simp [zero]
  · simpa [zero, BitVec.mul_comm, Nat.mul_comm] using checked

theorem mul_guard_reverse (a b : Word) :
    (a ≠ 0#256 → b = a * b / a) ↔ a.toNat * b.toNat < 2^256 := by
  constructor
  · intro h; exact (mul_guard a b).mp (fun nonzero => (h nonzero).symm)
  · intro h nonzero; exact ((mul_guard a b).mpr h nonzero).symm

/-- Exact emitted panic memory, including the overlapping selector/payload
writes. No assumption about pre-existing scratch bytes is needed. -/
theorem panic_overflow_memory (memory : Contract.Interaction.Memory) :
    ((memory.write 0 (Contract.Interaction.wordBytes (0x4e487b7100000000000000000000000000000000000000000000000000000000#256))).write 4
      (Contract.Interaction.wordBytes 0x11#256)).read 0 36 = Contract.panic 0x11 := by
  have written := Contract.Interaction.Memory.read_write_prefix_pair memory 0 4
    (Contract.Interaction.wordBytes (0x4e487b7100000000000000000000000000000000000000000000000000000000#256))
    (Contract.Interaction.wordBytes 0x11#256) (by decide)
  simp only [Contract.Interaction.wordBytes_length, Nat.reduceAdd] at written
  rw [written]
  decide

end Compiler.Validation.SolidityWord
