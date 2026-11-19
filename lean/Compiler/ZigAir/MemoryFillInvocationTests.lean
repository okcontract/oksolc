/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryFillInvocation

namespace Compiler.ZigAir.MemoryFill
open Memory MemoryAir GeneratedMemory

private def singleWord (n : Int) (nextId nextAddress : Nat) : State :=
  ⟨[(0, ⟨8, word, [(0, .scalar (.int false 32 n))], true, false⟩)], nextId, nextAddress⟩

/-- Instantiate the universal theorem on a nonempty valid heap. This witness
checks that its lifetime and input preconditions admit a successful fill. -/
theorem fill_nonempty_witness :
    ∃ fuel, fn_fill.runFuel fuel (arguments 1 (.int false 32 9) ⟨0, 0⟩) (singleWord 1 1 12) =
      .finished (.ok (.scalar .unit)) (singleWord 9 3 32) := by
  have expected : specification 1 (.int false 32 9) ⟨0, 0⟩ (singleWord 1 1 12) =
      (.ok (.scalar .unit), singleWord 9 3 32) := by rfl'
  simpa only [expected] using fill_terminates 1 (.int false 32 9) ⟨0, 0⟩ (singleWord 1 1 12)
    (by rfl') (by decide) (by rfl) (by decide)

theorem fill_first_allocation_oom :
    fn_fill.runFuel 16 (arguments 1 (.int false 32 9) ⟨0, 0⟩) ⟨[], 1, addressLimit⟩ =
      .finished (.error .outOfMemory) ⟨[], 1, addressLimit⟩ ∧
    specification 1 (.int false 32 9) ⟨0, 0⟩ ⟨[], 1, addressLimit⟩ =
      (.error .outOfMemory, ⟨[], 1, addressLimit⟩) := by constructor <;> rfl'

/-- The first allocation's cursor effects survive failure of the second, while
the call's saved-pointer allocation is removed by cleanup. -/
theorem fill_second_allocation_oom :
    fn_fill.runFuel 16 (arguments 1 (.int false 32 9) ⟨0, 0⟩) ⟨[], 1, addressLimit - 16⟩ =
      .finished (.error .outOfMemory) ⟨[], 2, addressLimit - 8⟩ ∧
    specification 1 (.int false 32 9) ⟨0, 0⟩ ⟨[], 1, addressLimit - 16⟩ =
      (.error .outOfMemory, ⟨[], 2, addressLimit - 8⟩) := by constructor <;> rfl'

end Compiler.ZigAir.MemoryFill
