/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
namespace Compiler.Extraction.RepresentativeArray.Append

-- Admitted insertOwned descriptor and unmanaged Aligned append helpers.
-- Growth/relocation is retained in admission and not covered by these equations.
-- Source SHA-256: d66c002eb6f32b6886bc4c6cb24b33b4551f47a98d95fd5c5ad84a97f64b0603
-- std/array_list.zig SHA-256: 0420c0177c67490083f1055cff6de253f9ee8fb28755c5200002627640ff7aee
def nextLength (length : Nat) : Nat := length + 1
def hasCapacity (capacity newLength : Nat) : Bool := decide (capacity ≥ newLength)
def selectedIndex (newLength : Nat) : Nat := newLength - 1

end Compiler.Extraction.RepresentativeArray.Append
