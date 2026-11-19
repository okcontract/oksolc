/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
namespace Compiler.Extraction.RepresentativeArray.Publication

-- Shared reached suffix of both ensureTotalCapacityPrecise growth branches.
-- New-memory evaluation and preceding effects remain caller obligations.
-- std/array_list.zig SHA-256: 0420c0177c67490083f1055cff6de253f9ee8fb28755c5200002627640ff7aee
inductive Update where | itemsPointer | capacity deriving DecidableEq
def program : List Update := [.itemsPointer, .capacity]

end Compiler.Extraction.RepresentativeArray.Publication
