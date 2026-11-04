/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryTypes

namespace Compiler.Extraction.ExpressionMap.Buckets

-- Source-bound extent of the one aligned byte allocation. Component pointers
-- are observed without reading padding or copying private stdlib declarations.
-- This opaque allocation type admits no bucket/header/key field operations.
-- Initialization, ownership by a map, probing and release remain obligations.
-- Source SHA-256: d66c002eb6f32b6886bc4c6cb24b33b4551f47a98d95fd5c5ad84a97f64b0603
-- std/hash_map.zig SHA-256: da14a2401ab5c12d6ca25bbf49e950596859ffc9e4b6d7726ade7ea8fd4a1b34
-- std/mem.zig SHA-256: db78007af4878dd75a0fc1c24f1fdb90f44f2d15c4c6177c43e388262a17a44e
def alignForward (value alignment : Nat) : Nat := (value + alignment - 1) / alignment * alignment
def headerBytes : Nat := 24
def metadataBytes : Nat := 1
def keyBytes : Nat := 64
def keyAlignment : Nat := 16
def valueBytes : Nat := 4
def valueAlignment : Nat := 4
def allocationAlignment : Nat := 16

def keysOffset (capacity : Nat) : Nat := alignForward (headerBytes + capacity * metadataBytes) keyAlignment
def valuesOffset (capacity : Nat) : Nat := alignForward (keysOffset capacity + capacity * keyBytes) valueAlignment
def bytes (capacity : Nat) : Nat := alignForward (valuesOffset capacity + capacity * valueBytes) allocationAlignment

def allocationType (capacity : Nat) : Compiler.ZigAir.Memory.Ty :=
  .record "std/hash_map.zig::aligned(ExpressionKey,u32)" ⟨bytes capacity, allocationAlignment⟩

end Compiler.Extraction.ExpressionMap.Buckets
