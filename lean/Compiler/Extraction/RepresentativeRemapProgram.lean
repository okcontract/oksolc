/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
namespace Compiler.Extraction.RepresentativeArray.Remap

-- std/mem/Allocator.zig SHA-256: 25099a1aaed1fe80b811e1eaedf8c3e2059a3fe7b6c29db868a68da3085b7997
-- Complete noRemap body; callback identity must be bound at the caller.
-- Other remap implementations have no admitted preservation contract.
def noRemap (_context _base _bytes _alignment _newBytes _returnAddress : Nat) : Option Nat := none

end Compiler.Extraction.RepresentativeArray.Remap
