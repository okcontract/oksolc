/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
namespace Compiler.Extraction.RepresentativeArray.Growth

-- Nonzero captured Expression layout; complete growth and remap bodies admitted.
-- For positive new capacity, zero old capacity returns null before rawRemap.
-- Nonempty growth requires separately admitted remap callback execution.
-- std/array_list.zig SHA-256: 0420c0177c67490083f1055cff6de253f9ee8fb28755c5200002627640ff7aee
-- std/mem/Allocator.zig SHA-256: 25099a1aaed1fe80b811e1eaedf8c3e2059a3fe7b6c29db868a68da3085b7997
inductive Branch where | unchanged | firstAllocation | existingGrowth deriving DecidableEq
def choose (oldCapacity newCapacity : Nat) : Branch :=
  if oldCapacity ≥ newCapacity then .unchanged else
  if oldCapacity = 0 then .firstAllocation else .existingGrowth

end Compiler.Extraction.RepresentativeArray.Growth
