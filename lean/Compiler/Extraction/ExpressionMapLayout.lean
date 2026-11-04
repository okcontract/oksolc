/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryTypes

namespace Compiler.Extraction.ExpressionMap

-- Complete captured HashMapUnmanaged field inventory in all three admitted modes.
-- Nullable metadata pointers are atomic values, not pointer/tag byte projections.
-- ReleaseFast's captured zero-byte lock at offset 16 has no storage leaf.
-- Source SHA-256: d66c002eb6f32b6886bc4c6cb24b33b4551f47a98d95fd5c5ad84a97f64b0603
-- std/hash_map.zig SHA-256: da14a2401ab5c12d6ca25bbf49e950596859ffc9e4b6d7726ade7ea8fd4a1b34
-- std/debug.zig SHA-256: 98e84c2194011077e8b8156cb3b2cb7b310a08dd34f396ee3654c102796e8f59
def metadataPointerType : Compiler.ZigAir.Memory.Ty := .pointer true true (.record "hash_map.Custom(libevmasm.expression_classes.ExpressionKey,u32,libevmasm.expression_classes.ExpressionKeyContext,80).Metadata" ⟨1, 1⟩)
def metadataType : Compiler.ZigAir.Memory.Ty := .optionalObject metadataPointerType ⟨8, 8⟩
def lockType : Compiler.ZigAir.Memory.Ty :=
  .aggregate "debug.SafetyLock" ⟨8, 8⟩ [(0, .scalar (.int false 64))]
def metadataOffset : Nat := 0
def sizeOffset (runtimeSafety : Bool) : Nat := if runtimeSafety then 16 else 8
def availableOffset (runtimeSafety : Bool) : Nat := if runtimeSafety then 20 else 12
def lockOffset (runtimeSafety : Bool) : Nat := if runtimeSafety then 8 else 16
def countType : Compiler.ZigAir.Memory.Ty := .scalar (.int false 32)
def allocationType (runtimeSafety : Bool) : Compiler.ZigAir.Memory.Ty :=
  .aggregate "hash_map.Custom(libevmasm.expression_classes.ExpressionKey,u32,libevmasm.expression_classes.ExpressionKeyContext,80)" ⟨if runtimeSafety then 24 else 16, 8⟩
    ([(0, .object metadataType)] ++ (if runtimeSafety then [(8, .object lockType)] else []) ++
      [(sizeOffset runtimeSafety, .scalar (.int false 32)), (availableOffset runtimeSafety, .scalar (.int false 32))])

end Compiler.Extraction.ExpressionMap
