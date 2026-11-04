/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InsertionSortNormalization

namespace Compiler.Extraction.InsertionSort.Tests

theorem empty : run [] = .ok [] := by decide
theorem singleton : run [7] = .ok [7] := by decide
theorem ordered : run [0, 1, 2, 3] = .ok [0, 1, 2, 3] := by decide
theorem reversed : run [3, 2, 1, 0] = .ok [0, 1, 2, 3] := by decide
theorem duplicates : run [2, 1, 2, 0, 1] = .ok [0, 1, 1, 2, 2] := by decide
theorem unsigned : run [4294967295, 0, 2147483648, 1] = .ok [0, 1, 2147483648, 4294967295] := by decide
theorem equal : run [9, 9, 9] = .ok [9, 9, 9] := by decide
theorem alternating : run [5, 1, 4, 2, 3, 0] = .ok [0, 1, 2, 3, 4, 5] := by decide

theorem exhausted : passes 0 2 1 [2, 1] = .fault .incomplete [2, 1] := by decide
theorem exhausted_keeps_exchange : passes 1 2 1 [2, 1] = .fault .incomplete [1, 2] := by decide
theorem invalid_inner : insert 2 [2, 1] = .fault .bounds [2, 1] := by decide
theorem invalid_stop : passes 3 3 1 [2, 1] = .fault .bounds [1, 2] := by decide
theorem zero_guard_skips_reads : insert 0 [] = .ok [] := by decide
theorem native_max_counter :
    (2^64 - 2 : Nat) + 1 < 2^64 ∧ (2^64 - 2 : Nat) ≠ 2^64 - 3 := by decide
theorem checked_small : checked [2, 0, 1] = .ok [0, 1, 2] := by decide

end Compiler.Extraction.InsertionSort.Tests
