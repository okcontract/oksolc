/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryTypes

namespace Compiler.Extraction.AssemblyItem

-- Captured Zig 0.17.0, aarch64/macos/none, little-endian, LLVM.
-- Allocation extent only: native field projection is not admitted.
def allocationType : Compiler.ZigAir.Memory.Ty :=
  .record "src/libevmasm/assembly_item.zig::AssemblyItem" ⟨224, 16⟩

end Compiler.Extraction.AssemblyItem
