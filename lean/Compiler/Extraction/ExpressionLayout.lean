/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryTypes

namespace Compiler.Extraction.Expression

-- Complete captured Expression fields; item storage and graph/container correspondence remain open.
-- Source SHA-256: d66c002eb6f32b6886bc4c6cb24b33b4551f47a98d95fd5c5ad84a97f64b0603
def itemOffset : Nat := 0
def argumentsOffset : Nat := 8
def idOffset : Nat := 24
def sequence_numberOffset : Nat := 28

def allocationType : Compiler.ZigAir.Memory.Ty :=
  .aggregate "src/libevmasm/expression_classes.zig::Expression" ⟨32, 8⟩
    [(0, .pointer true "src/libevmasm/assembly_item.zig::AssemblyItem" ⟨224, 16⟩),
    (8, .slice true (.int false 32)),
    (24, .scalar (.int false 32)),
    (28, .scalar (.int false 32))]

end Compiler.Extraction.Expression
