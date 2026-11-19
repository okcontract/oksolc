/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.BinaryLogarithmProofs

namespace Compiler.Extraction.BinaryLogarithm.Tests
set_option maxRecDepth 4096

example : binaryLogarithm 64 0 = .ok none := by rfl
example : binaryLogarithm 32 1 = .ok (some 0) := by rfl
example : binaryLogarithm 64 2 = .ok (some 1) := by rfl
example : binaryLogarithm 64 3 = .ok none := by rfl
example : binaryLogarithm 64 6 = .ok none := by rfl
example : binaryLogarithm 64 (BitVec.allOnes 256) = .ok none := by rfl
example : binaryLogarithm 64 (BitVec.twoPow 256 255) = .ok (some 255) := by rfl
example : binaryLogarithm 32 (BitVec.twoPow 256 128) = .ok (some 128) := by rfl
example : binaryLogarithm 16 (BitVec.twoPow 256 254) = .ok (some 254) := by rfl
example : binaryLogarithm 8 (BitVec.twoPow 256 255) = .ok (some 255) := by rfl
example : binaryLogarithm 64 (BitVec.twoPow 256 255 + BitVec.twoPow 256 128) = .ok none := by rfl
example : binaryLogarithm 64 (BitVec.twoPow 256 128 + 1) = .ok none := by rfl
-- Deliberately undersized target casts stay explicit faults. Early rejections
-- do not perform the subtraction or cast; the accepted value 1 has count zero.
example : binaryLogarithm 7 (BitVec.twoPow 256 128) = .error .invalidCast := by rfl
example : binaryLogarithm 7 (BitVec.twoPow 256 127) = .ok (some 127) := by rfl
example : binaryLogarithm 0 0 = .ok none := by rfl
example : binaryLogarithm 0 3 = .ok none := by rfl
example : binaryLogarithm 0 1 = .ok (some 0) := by rfl
example : binaryLogarithm 0 2 = .error .invalidCast := by rfl

end Compiler.Extraction.BinaryLogarithm.Tests
