/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirLongTests
import Compiler.Extraction.ExpressionMapHashNativeEmpty
import Compiler.Extraction.ExpressionMapHashBytesTests

set_option maxRecDepth 8192

namespace Compiler.ZigAir.WyhashUpdateAirTests
open Memory AggregateAir Compiler.Extraction WyhashUpdateAir

/-- The existing 49-byte input now specializes the entire invocation, including
parameter saves, index admission and cleanup, rather than only its loop cut. -/
theorem complete_invocation_specializes : ∃ fuel result after,
    GeneratedWyhashUpdate.update.runFuel fuel (WyhashUpdateAir.arguments 0 ⟨1, 0⟩ 49) loopBase =
      .finished result after ∧ after.valid = true ∧
      (result = .error .outOfMemory ∨ ∃ cells buffered,
        result = .ok (.value (.scalar .unit)) ∧
        WyhashUpdate.update loopContext.source loopContext.view initial = .ok cells ∧
        WyhashUpdate.Invariant cells 49 buffered ∧ StackFrame (loopContext.frame.install cells) after) := by
  obtain ⟨fuel, result, after, ran, valid, failed | ⟨cells, buffered, success, _, model, invariant, stack⟩⟩ :=
    invocation loopContext.frame loopContext.valid loopContext.typed loopContext.address
      loopContext.source loopContext.view loopContext.bytes loopContext.geometry loopContext.represented
      loopContext.reads loopContext.apart 0 0 (WyhashUpdate.init_invariant 0) (by decide) loopContext.budget
  · exact ⟨fuel, result, after, ran, valid, Or.inl failed.1⟩
  · exact ⟨fuel, result, after, ran, valid, Or.inr ⟨cells, buffered, success, model, invariant, stack⟩⟩

/-- This is an adapter rejection with ample allocation space, not a resource
failure. Both parameter locals retire and the original heap remains exact. -/
theorem anonymous_empty_rejected :
    (match GeneratedWyhashUpdate.update.runFuel 20 (emptyArguments 0) (caller initial []) with
    | .finished result after => decide (result = .error .unsupported ∧
        after = { caller initial [] with nextId := 4, nextAddress := 160 })
    | _ => false) = true := by
  decide +kernel

/-- Use the existing empty-key fixture's actual returned register. The gap is
observable at the caller boundary; converting that register to [] hides it. -/
theorem caller_empty_view_rejected :
    (let state := ExpressionMap.HashBytes.Tests.state
    let (output, viewed) := ExpressionMap.HashSlice.view state 0
    decide (output = .ok .emptyBytes) &&
      match GeneratedWyhashUpdate.update.runFuel 20 [.value (selfPointer 0), .emptyBytes] viewed with
      | .finished result after => decide (result = .error .unsupported ∧
          after = { viewed with nextId := viewed.nextId + 2, nextAddress := viewed.nextAddress + 24 })
      | _ => false) = true := by
  decide +kernel

end Compiler.ZigAir.WyhashUpdateAirTests
