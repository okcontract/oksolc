/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryTypes

namespace Compiler.Extraction.RepresentativeArray.Capacity

-- Captured aarch64 target and 32-byte nonzero Expression, checked by native admission.
-- Complete ensureTotalCapacity/growCapacity and cache-line policy bodies are bound.
-- std/array_list.zig SHA-256: 0420c0177c67490083f1055cff6de253f9ee8fb28755c5200002627640ff7aee
-- std/atomic.zig SHA-256: 85b467837478ff64aba29bf52cf9eef9b973ddb3ec6b5472901500a8e4a925c5
def initialCapacity : Nat := max 1 (128 / 32)
def grow (minimum : Nat) : Nat :=
  min (Compiler.ZigAir.Memory.addressLimit - 1) (minimum + (minimum / 2 + initialCapacity))

end Compiler.Extraction.RepresentativeArray.Capacity
