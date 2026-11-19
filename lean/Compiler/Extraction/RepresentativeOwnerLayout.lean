/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeArrayLayout
import Compiler.Extraction.ExpressionMapLayout

namespace Compiler.Extraction.RepresentativeArray.Owner

-- Complete captured owner metadata; allocator/cache contents and native initialization remain open.
-- Runtime safety selects the captured Debug/ReleaseSafe layout; false selects ReleaseFast.
-- Each native mode must match its captured extent; this is not an ABI rule for other builds.
-- Source SHA-256: d66c002eb6f32b6886bc4c6cb24b33b4551f47a98d95fd5c5ad84a97f64b0603
-- std/array_list.zig SHA-256: 0420c0177c67490083f1055cff6de253f9ee8fb28755c5200002627640ff7aee
-- std/debug.zig SHA-256: 98e84c2194011077e8b8156cb3b2cb7b310a08dd34f396ee3654c102796e8f59
-- std/hash_map.zig SHA-256: da14a2401ab5c12d6ca25bbf49e950596859ffc9e4b6d7726ade7ea8fd4a1b34
-- std/meta.zig SHA-256: af1d7b90ee1a3f019aae7c6b94b7db3845402af86434f6f2847bafcbfe2cd76a
-- std/std.zig SHA-256: 053cdeca0cb3632a98117ddbef4ffa1a65cf30bcc6555af9437dc3ee3781d12e
def layout (runtimeSafety : Bool) : Compiler.ZigAir.Memory.Layout := ⟨if runtimeSafety then 72 else 56, 8⟩
def allocationType (runtimeSafety : Bool) : Compiler.ZigAir.Memory.Ty := .record "src/libevmasm/expression_classes.zig::ExpressionClasses" (layout runtimeSafety)
def allocatorOffset : Nat := 0
def allocatorLayout : Compiler.ZigAir.Memory.Layout := ⟨16, 8⟩
def representativesOffset : Nat := 16
def representativesLayout : Compiler.ZigAir.Memory.Layout := ⟨24, 8⟩
def representativesStorageLayout (runtimeSafety : Bool) : Compiler.ZigAir.Memory.Layout := ⟨if runtimeSafety then 32 else 24, 8⟩
def representativesLockOffset : Nat := 40
def expressionsOffset (runtimeSafety : Bool) : Nat := if runtimeSafety then 48 else 40
def expressionsLayout (runtimeSafety : Bool) : Compiler.ZigAir.Memory.Layout := ⟨if runtimeSafety then 24 else 16, 8⟩

def regions (runtimeSafety : Bool) : List (Nat × Compiler.ZigAir.Memory.Layout) :=
  [(allocatorOffset, allocatorLayout), (representativesOffset, representativesStorageLayout runtimeSafety), (expressionsOffset runtimeSafety, expressionsLayout runtimeSafety)]

-- Decompose the native representative field into its data prefix and lock suffix.
-- This groups the same captured leaves; it adds no storage or native allocation.
def viewType (runtimeSafety : Bool) : Compiler.ZigAir.Memory.Ty :=
  .aggregate "src/libevmasm/expression_classes.zig::ExpressionClasses" (layout runtimeSafety)
    ([(allocatorOffset, .object (.record "mem.Allocator" allocatorLayout)),
      (representativesOffset, .object Compiler.Extraction.RepresentativeArray.allocationType)] ++
      (if runtimeSafety then [(representativesLockOffset, .object Compiler.Extraction.ExpressionMap.lockType)] else []) ++
      [(expressionsOffset runtimeSafety, .object (Compiler.Extraction.ExpressionMap.allocationType runtimeSafety))])

end Compiler.Extraction.RepresentativeArray.Owner
