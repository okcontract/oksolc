/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.WyhashLocal
import Compiler.Extraction.ExpressionMapHashInputTests

namespace Compiler.Extraction.WyhashLocal.Tests
open Compiler.ZigAir.Memory

set_option maxRecDepth 4096

private theorem empty_lookup (offset : Nat) : Cells.lookup [] offset = none := rfl

theorem core_valid (a b : Option (BitVec 64)) (s0 s1 s2 total : BitVec 64) :
    (core a b s0 s1 s2 total).valid objectType = true := by
  have set (cells : Cells) (offset : Nat) (value : BitVec 64) (valid : cells.valid objectType = true)
      (member : offset ∈ [0, 8, 16, 24, 32, 40]) : (cells.set offset (word value)).valid objectType = true :=
    Cells.set_preserves_valid cells objectType offset (word value) valid
      (by simp only [leafFits, (geometry offset member).1, word_type, decide_true, Bool.true_and, word_valid])
  unfold core
  apply set _ _ _ _ (by decide)
  apply set _ _ _ _ (by decide)
  apply set _ _ _ _ (by decide)
  apply set _ _ _ _ (by decide)
  cases a <;> cases b <;> simp only [put]
  · rfl
  · exact set _ _ _ rfl (by decide)
  · exact set _ _ _ rfl (by decide)
  · exact set _ _ _ (set _ _ _ rfl (by decide)) (by decide)

theorem core_represents (a b : Option (BitVec 64)) (s0 s1 s2 total : BitVec 64) :
    Represents (core a b s0 s1 s2 total) a b s0 s1 s2 total := by
  cases a <;> cases b <;> simp [Represents, core, put, Cells.lookup_set, Cells.lookup_set_other, empty_lookup]

theorem missing_copy (s0 s1 s2 total : BitVec 64) :
    shallowCopy (core none none s0 s1 s2 total) = .ok (core none none s0 s1 s2 total) :=
  shallowCopy_verified _ _ _ _ _ _ _ (core_valid ..) (core_represents ..)

theorem absent_reads (s0 s1 s2 total : BitVec 64) :
    readWord (core none none s0 s1 s2 total) 0 = .error .uninitialized ∧
    readWord (core none none s0 s1 s2 total) 8 = .error .uninitialized ∧
    (core none none s0 s1 s2 total).lookup 48 = none ∧
    (core none none s0 s1 s2 total).lookup 56 = none := by
  simp [readWord, core, put, Cells.lookup_set_other, empty_lookup]

theorem old_values_irrelevant (oldA oldB : Option (BitVec 64)) (s0 s1 s2 total a b : BitVec 64) :
    (do let copied ← shallowCopy (core oldA oldB s0 s1 s2 total); finishTail nativeOps copied a b) =
      .ok (result a b s0 total) :=
  shallowCopy_finishTail _ oldA oldB s0 s1 s2 total a b (core_valid ..) (core_represents ..)

theorem wide_product : lo (product 0xffffffffffffffff 0xffffffffffffffff) = 1 ∧
    hi (product 0xffffffffffffffff 0xffffffffffffffff) = 0xfffffffffffffffe := by decide +kernel

theorem undefined_transfer :
    Cells.transferScalar [] usize 0 [(0, word 17)] usize 0 (.int false 64) = .ok [] := by decide +kernel

theorem defined_transfer :
    Cells.transferScalar [(0, word 17)] usize 0 [] usize 0 (.int false 64) = .ok [(0, word 17)] := by decide +kernel

theorem invalid_source_rejected :
    Cells.transferScalar [] usize 8 [] usize 0 (.int false 64) = .error .unsupported := by decide +kernel

theorem invalid_target_rejected :
    Cells.transferScalar [] usize 0 [] (.scalar (.int false 8)) 0 (.int false 64) = .error .unsupported := by decide +kernel

theorem malformed_rejected :
    Cells.transferScalar [(0, .scalar (.int false 32 17))] usize 0 [] usize 0 (.int false 64) = .error .malformed := by decide +kernel

theorem zero_width_rejected :
    Cells.transferScalar [] (.scalar .unit) 0 [] (.scalar .unit) 0 .unit = .error .unsupported := by decide +kernel

theorem missing_state_rejected : finishTail nativeOps [] 3 5 = .error .uninitialized := by
  rw [nativeOps_eq]
  decide +kernel

theorem missing_length_rejected : finishTail nativeOps [(16, word 7)] 3 5 = .error .uninitialized := by
  rw [nativeOps_eq]
  decide +kernel

theorem transfer_frames_other :
    Cells.transferScalar [] objectType 0 [(0, word 17), (8, word 19)] objectType 0 (.int false 64) = .ok [(8, word 19)] := by decide +kernel

end Compiler.Extraction.WyhashLocal.Tests
