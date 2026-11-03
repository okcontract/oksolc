/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.BitwiseProofs

namespace Compiler.ZigAir.Scalar.BitwiseTests

private def u (width : Nat) (x : Int) : Ref := .constant (.int false width x)
private def evaluate (prim : Prim) := prim.eval [] (fun _ => none)

theorem unsigned_high_bit : evaluate (.bitAnd (u 256 (2^255+1)) (u 256 (2^255))) =
    .ok (.int false 256 (2^255)) := by rfl
theorem shift_high_bit : evaluate (.shiftRight (u 256 (2^255)) (u 8 255)) =
    .ok (.int false 256 1) := by rfl
theorem shift_zero : evaluate (.shiftRight (u 256 (2^255+1)) (u 8 0)) =
    .ok (.int false 256 (2^255+1)) := by rfl
theorem shift_single_bit : evaluate (.shiftRight (u 1 1) (u 0 0)) =
    .ok (.int false 1 1) := by rfl
theorem shift_count_width_rejects : evaluate (.shiftRight (u 256 4) (u 256 1)) =
    .error .malformed := by rfl
theorem shift_zero_width_rejects : evaluate (.shiftRight (u 0 0) (u 0 0)) =
    .error .malformed := by rfl
theorem shift_past_width_is_illegal : evaluate (.shiftRight (u 3 7) (u 2 3)) =
    .error .illegalBehavior := by rfl
theorem invalid_count_rejects : evaluate (.shiftRight (u 8 7) (u 3 (-1))) =
    .error .malformed := by rfl
theorem signed_count_rejects : evaluate (.shiftRight (u 8 7) (.constant (.int true 3 1))) =
    .error .malformed := by rfl
theorem signed_left_rejects : evaluate (.shiftRight (.constant (.int true 8 (-1))) (u 3 1)) =
    .error .malformed := by rfl
theorem and_mismatched_width_rejects : evaluate (.bitAnd (u 8 1) (u 16 1)) =
    .error .malformed := by rfl
theorem and_signed_rejects : evaluate (.bitAnd (.constant (.int true 8 (-1))) (u 8 1)) =
    .error .malformed := by rfl
theorem invalid_left_rejects : evaluate (.bitAnd (u 8 256) (u 8 1)) =
    .error .malformed := by rfl
theorem dead_shift_still_faults :
    (Program.mk [] .unit (.bind 0 (.int false 3) (.shiftRight (u 3 7) (u 2 3))
      (.ret (.constant .unit)))).run [] = .error .illegalBehavior := by rfl

end Compiler.ZigAir.Scalar.BitwiseTests
