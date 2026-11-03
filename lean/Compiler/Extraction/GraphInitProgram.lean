/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerGraphInitOwnership

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.GraphInit

-- Generated from the complete graph initializer and owner fields.
-- Source SHA-256: d66c002eb6f32b6886bc4c6cb24b33b4551f47a98d95fd5c5ad84a97f64b0603
-- std/array_list.zig SHA-256: 0420c0177c67490083f1055cff6de253f9ee8fb28755c5200002627640ff7aee
-- std/debug.zig SHA-256: 98e84c2194011077e8b8156cb3b2cb7b310a08dd34f396ee3654c102796e8f59
-- std/hash_map.zig SHA-256: da14a2401ab5c12d6ca25bbf49e950596859ffc9e4b6d7726ade7ea8fd4a1b34
-- std/meta.zig SHA-256: af1d7b90ee1a3f019aae7c6b94b7db3845402af86434f6f2847bafcbfe2cd76a
-- std/std.zig SHA-256: 053cdeca0cb3632a98117ddbef4ffa1a65cf30bcc6555af9437dc3ee3781d12e
def zigInit (allocator : Nat) (before : Session σ) : Nat × World σ := run allocator before

-- Complete container defaults in a declared owner; native owner allocation and allocator contents remain open.
def zigInitInOwner (runtimeSafety : Bool) (allocator : Nat) (before : Session σ)
    (owner sentinel : Compiler.ZigAir.Memory.Address) : Except Compiler.ZigAir.Memory.Fault (Nat × World σ) :=
  OwnerMemory.run runtimeSafety allocator before owner sentinel

-- Pinned null-metadata keyIterator/FieldIterator.next branch establishes empty key ownership.
def zigInitOwned (runtimeSafety : Bool) (allocator : Nat) (before : Session σ)
    (owner sentinel : Compiler.ZigAir.Memory.Address) :=
  Ownership.run runtimeSafety allocator before owner sentinel

-- Pinned std get/getContext/getAdapted/getIndex empty branch; nonempty probing rejects.
def zigEmptyCacheGet (runtimeSafety : Bool) (state : Compiler.ZigAir.Memory.State)
    (owner : Compiler.ZigAir.Memory.Address) (key : Compiler.Extraction.Cache.Key) :=
  Compiler.Extraction.ExpressionMap.getEmpty runtimeSafety state owner key

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.GraphInit
