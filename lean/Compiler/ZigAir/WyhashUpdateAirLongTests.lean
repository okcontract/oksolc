/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirLongExecution
import Compiler.ZigAir.WyhashUpdateAirLoopTests

namespace Compiler.ZigAir.WyhashUpdateAirTests
open Memory AggregateAir Compiler.Extraction WyhashUpdateAir Control.Machine

/-- Reuse the admitted 49-byte loop case: it takes a full round and the retained
suffix branch. The general composition now reaches the original return. -/
theorem loop_return_specializes : ∃ after, after.valid = true ∧
    (Steps AggregateCall.semantics [] (.suspended ⟨Loop.entry, loopEnv, loopState, []⟩)
      (.finished (.fault .outOfMemory after)) ∨
     ∃ cells,
       (do
         let (rounded, stop) ← WyhashUpdate.loop loopContext.source loopContext.view 0 initial
         WyhashUpdate.remainder loopContext.source loopContext.view stop rounded) = .ok cells ∧
       WyhashUpdate.Core cells 0 ∧ StackFrame (loopContext.frame.install cells) after ∧
       Steps AggregateCall.semantics [] (.suspended ⟨Loop.entry, loopEnv, loopState, []⟩)
         (.finished (.returned (.value (.scalar .unit)) after))) := by
  obtain ⟨after, ⟨_, _, _, stack, path⟩ | ⟨cells, ran, core, stack, path⟩⟩ :=
    Loop.through_return loopContext initial loop_admitted [] loopEnv [] (by unfold Loop.Locals; decide +kernel)
  · exact ⟨after, stack.valid, Or.inl path⟩
  · exact ⟨after, stack.valid, Or.inr ⟨cells, ran, core, stack, path⟩⟩

end Compiler.ZigAir.WyhashUpdateAirTests
