/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapHashSlice
import Compiler.ZigAir.WyhashUpdateAirEmpty

namespace Compiler.Extraction.ExpressionMap.HashSlice
open Compiler.ZigAir Compiler.ZigAir.Memory Compiler.ZigAir.AggregateAir
open Compiler.Extraction.Cache (Key)

/-- Connecting the captured argument view directly to the captured update
exposes the adapter's anonymous-empty-slice rejection. The cell-model runner's
successful empty update cannot discharge this native call. Earlier allocation
failure remains possible, and neither outcome changes caller storage. -/
theorem empty_native_update (state : State) (keyId self : Nat) (key : Key) (source : WordArray.View)
    (valid : state.valid = true) (binding : HashKey.Binding state keyId key (source.address 0))
    (represented : WordArray.Represents state source key.arguments) (empty : source.length = 0) :
    ∃ output viewed, view state keyId = (output, viewed) ∧ StackFrame state viewed ∧
      viewed.heap = state.heap ∧
      (output = .error .outOfMemory ∨ output = .ok .emptyBytes ∧ ∃ fuel result after,
        GeneratedWyhashUpdate.update.runFuel fuel [.value (WyhashUpdateAir.selfPointer self), .emptyBytes] viewed =
          .finished result after ∧ StackFrame state after ∧ after.heap = state.heap ∧
          (result = .error .outOfMemory ∨ result = .error .unsupported)) := by
  obtain ⟨output, viewed, observed, frame, heap, success | failed⟩ :=
    view_verified state keyId key source valid binding represented (by rw [empty]; decide)
  · have returned : output = .ok .emptyBytes := by simpa only [SliceBytesAir.result, if_pos empty] using success
    obtain ⟨fuel, result, after, ran, _, same, stack, rejected⟩ :=
      WyhashUpdateAir.empty_literal viewed self frame.valid
    exact ⟨output, viewed, observed, frame, heap, Or.inr ⟨returned, fuel, result, after,
      ran, frame.trans stack, same.trans heap, rejected⟩⟩
  · exact ⟨output, viewed, observed, frame, heap, Or.inl failed⟩

end Compiler.Extraction.ExpressionMap.HashSlice
