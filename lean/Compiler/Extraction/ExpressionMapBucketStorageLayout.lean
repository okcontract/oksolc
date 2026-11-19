/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapKeyLayout

namespace Compiler.Extraction.ExpressionMap.Buckets
open Compiler.ZigAir.Memory

-- Declared component regions use the captured key fields and packed-u8 backing.
def metadataType : Ty := .aggregate "hash_map.Custom(libevmasm.expression_classes.ExpressionKey,u32,libevmasm.expression_classes.ExpressionKeyContext,80).Metadata" ⟨1, 1⟩ [(0, .scalar (.int false 8))]
def headerType : Ty := .aggregate "hash_map.Custom(libevmasm.expression_classes.ExpressionKey,u32,libevmasm.expression_classes.ExpressionKeyContext,80).Header" ⟨24, 8⟩
  [(0, .object (.pointer true true (.scalar (.int false 32)))),
   (8, .object (.pointer true true keyType)), (16, .scalar (.int false 32))]
def storageFields (capacity : Nat) : List (Nat × Field) :=
  [(0, .object headerType), (24, .object (.array capacity metadataType)),
   (keysOffset capacity, .object (.array capacity keyType)),
   (valuesOffset capacity, .object (.array capacity (.scalar (.int false 32))))]
def storageType (capacity : Nat) : Ty :=
  .aggregate "std/hash_map.zig::aligned(ExpressionKey,u32)" ⟨bytes capacity, 16⟩ (storageFields capacity)

end Compiler.Extraction.ExpressionMap.Buckets
