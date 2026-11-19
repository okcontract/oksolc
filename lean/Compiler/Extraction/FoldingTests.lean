/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.FoldingProgram

namespace Compiler.Extraction.Folding
open Contract.Yul
set_option exponentiation.threshold 1024
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

-- Kernel execution of the generated program, independently chosen results.
example : run helpers clauses 5 [BitVec.ofNat 256 (2^255), -1] =
    .ok (some (BitVec.ofNat 256 (2^255))) := by rfl
example : run helpers clauses 7 [-1, 2] = .ok (some (-1)) := by rfl
example : run helpers clauses 7 [BitVec.ofNat 256 (2^255), -1] = .ok (some 0) := by rfl
example : run helpers clauses 8 [-1, 8, 9] = .ok (some 5) := by rfl
example : run helpers clauses 9 [-1, -1, 7] = .ok (some 1) := by rfl
example : run helpers clauses 9 [-1, -1, 0] = .ok (some 0) := by rfl
example : run helpers clauses 10 [1, -1] = .ok (some 1) := by rfl
example : run helpers clauses 10 [0, 0] = .ok (some 1) := by rfl
example : run helpers clauses 26 [31, 511] = .ok (some 255) := by rfl
example : run helpers clauses 26 [32, -1] = .ok (some 0) := by rfl
example : run helpers clauses 11 [0, 255] = .ok (some (-1)) := by rfl
example : run helpers clauses 11 [0, 383] = .ok (some 127) := by rfl
example : run helpers clauses 11 [30, BitVec.ofNat 256 (2^248-1)] = .ok (some (-1)) := by rfl
example : run helpers clauses 11 [31, 123] = .ok (some 123) := by rfl
example : run helpers clauses 27 [256, -1] = .ok (some 0) := by rfl
example : run helpers clauses 28 [255, -1] = .ok (some 1) := by rfl
example : run helpers clauses 1 [] = .ok none := by rfl
example : run helpers clauses 1 [1, 2, 3] = .ok none := by rfl
example : run helpers clauses 255 [1, 2] = .ok none := by rfl

end Compiler.Extraction.Folding
