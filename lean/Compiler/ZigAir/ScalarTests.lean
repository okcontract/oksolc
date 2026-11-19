/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.NumericProofs

namespace Compiler.ZigAir.ScalarTests
open Scalar

private def u8 (x : Int) : Ref := .constant (.int false 8 x)
private def deadAdd (mode : Overflow) : Program :=
  ⟨[], .int false 8, .bind 0 (.int false 8)
    (.arithmetic .add mode (u8 255) (u8 1)) (.ret (u8 7))⟩

theorem dead_unchecked_overflow : (deadAdd .unchecked).run [] = .error .illegalBehavior := by rfl
theorem dead_checked_overflow : (deadAdd .checked).run [] = .error .safetyPanic := by rfl
theorem dead_wrapping_continues : (deadAdd .wrapping).run [] = .ok (.int false 8 7) := by rfl
theorem unsigned_wrap : integer false 8 256 .wrapping = .ok (.int false 8 0) := by rfl
theorem signed_wrap : integer true 8 128 .wrapping = .ok (.int true 8 (-128)) := by rfl
theorem zero_width_wrap : integer true 0 (-1) .wrapping = .ok (.int true 0 0) := by rfl
theorem checked_cast_negative :
    (Prim.cast .checked (.int false 8) (.constant (.int true 8 (-1)))).eval [] (fun _ => none) =
      .error .safetyPanic := by rfl
theorem unchecked_cast_negative :
    (Prim.cast .unchecked (.int false 8) (.constant (.int true 8 (-1)))).eval [] (fun _ => none) =
      .error .illegalBehavior := by rfl
theorem signed_bitcast :
    (Prim.cast .bitcast (.int true 8) (u8 255)).eval [] (fun _ => none) =
      .ok (.int true 8 (-1)) := by rfl
theorem signed_truncation :
    (Prim.cast .trunc (.int true 4) (.constant (.int true 8 (-17)))).eval [] (fun _ => none) =
      .ok (.int true 4 (-1)) := by rfl

private def branchTest : Program :=
  ⟨[], .int false 8, .branch (.constant (.bool false)) (deadAdd .unchecked).body (.ret (u8 9))⟩
theorem unselected_fault_is_not_executed : branchTest.run [] = .ok (.int false 8 9) := by rfl

private def earlyReturn : Program :=
  ⟨[], .int false 8, .block 0 .unit (.ret (u8 11)) (deadAdd .unchecked).body⟩
theorem return_skips_continuation : earlyReturn.run [] = .ok (.int false 8 11) := by rfl

private def blockValue : Program :=
  ⟨[], .int false 8, .block 0 (.int false 8)
    (.block 1 .unit (.jump 0 (u8 13)) (deadAdd .unchecked).body) (.ret (.local 0))⟩
theorem outer_jump_propagates_and_binds : blockValue.run [] = .ok (.int false 8 13) := by rfl

theorem unmatched_jump_rejects :
    (Program.mk [] (.int false 8) (.jump 0 (u8 1))).run [] = .error .malformed := by rfl
theorem wrong_block_value_rejects :
    (Program.mk [] (.int false 8) (.block 0 .unit (.jump 0 (u8 1)) (.ret (u8 2)))).run [] =
      .error .malformed := by rfl
theorem wrong_return_type_rejects :
    (Program.mk [] .unit (.ret (u8 1))).run [] = .error .malformed := by rfl
theorem missing_argument_rejects : Generated.u2s.run [] = .error .malformed := by rfl
theorem invalid_argument_rejects : Generated.u2s.run [.int false 256 (-1)] = .error .malformed := by rfl
theorem wrong_argument_type_rejects : Generated.u2s.run [.int true 256 0] = .error .malformed := by rfl
theorem missing_local_rejects :
    (Program.mk [] .unit (.ret (.local 99))).run [] = .error .malformed := by rfl

end Compiler.ZigAir.ScalarTests
