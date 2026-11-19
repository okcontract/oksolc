/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryTypes

namespace Compiler.Extraction.RepresentativeArray

-- Captured items/capacity prefix of std.ArrayList(Expression).
-- The native safety-lock suffix is represented separately in the complete owner view.
-- Source SHA-256: d66c002eb6f32b6886bc4c6cb24b33b4551f47a98d95fd5c5ad84a97f64b0603
-- std/array_list.zig SHA-256: 0420c0177c67490083f1055cff6de253f9ee8fb28755c5200002627640ff7aee
def elementType : Compiler.ZigAir.Memory.Ty := .record "src/libevmasm/expression_classes.zig::Expression" ⟨32, 8⟩
def itemsType : Compiler.ZigAir.Memory.Ty := .slice true elementType
def itemsOffset : Nat := 0
def capacityOffset : Nat := 16

def allocationType : Compiler.ZigAir.Memory.Ty :=
  .aggregate "std.ArrayList(src/libevmasm/expression_classes.zig::Expression)::DataFields" ⟨24, 8⟩
    [(0, .recordSlice true "src/libevmasm/expression_classes.zig::Expression" ⟨32, 8⟩),
    (16, .scalar (.int false 64))]

end Compiler.Extraction.RepresentativeArray
