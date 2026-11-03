/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapBucketLayout
import Compiler.Extraction.CacheIR

namespace Compiler.Extraction.ExpressionMap.Buckets

-- Complete native key field inventory from the existing three-mode capture.
-- The argument slice retains its constness and allocation identity; padding
-- is not a field or a readable byte representation.
def keyType : Compiler.ZigAir.Memory.Ty :=
  .aggregate "libevmasm.expression_classes.ExpressionKey" ⟨64, 16⟩ [(0, .scalar (.int false 256)), (32, .slice false (.int false 32)), (48, .scalar (.int false 32)), (52, .scalar (.int false 32)), (56, .scalar (.int false 8))]

-- Bind field identity as well as type: two u32 fields may exchange offsets.
def KeyFields.offset : Compiler.Extraction.Cache.Field → Nat
  | .kind => 48
  | .instruction => 56
  | .data => 0
  | .arguments => 32
  | .sequence => 52

end Compiler.Extraction.ExpressionMap.Buckets
