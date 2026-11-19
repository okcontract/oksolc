/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirExecution
import Compiler.ZigAir.WyhashUpdateAirTests

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Compiler.ZigAir.WyhashUpdateAirTests
open Memory AggregateAir Compiler.Extraction

def bufferedFrame : CellFrame (caller initial (bytes 4)) 0 :=
  ⟨⟨16, WyhashLocal.objectType, initial, true, false⟩, ⟨104, 8⟩, rfl, rfl, by decide +kernel⟩

/-- Specialize the general invocation theorem to the existing nonempty fixture.
The separate `buffered` regression observes its successful execution. -/
theorem buffered_preserves : ∃ fuel result after,
    GeneratedWyhashUpdate.update.runFuel fuel (arguments 4) (caller initial (bytes 4)) =
      .finished result after ∧ after.valid = true ∧
    ((result = .error .outOfMemory ∧ after.heap = (caller initial (bytes 4)).heap) ∨
      ∃ cells length, result = .ok (.value (.scalar .unit)) ∧
        after.heap = (bufferedFrame.install cells).heap ∧
        WyhashUpdate.update (ByteSlice.cellsFrom (bytes 4) 0) (ByteSlice.imageView (bytes 4)) initial = .ok cells ∧
        WyhashUpdate.Invariant cells 4 length) := by
  have reads : ByteRange.Reads (caller initial (bytes 4)) ⟨1, 0⟩ 4 (fun i => (bytes 4)[i]?.getD 0) := by
    intro i inside
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> decide +kernel
  exact WyhashUpdateAir.buffered_invocation bufferedFrame
    (by decide +kernel) rfl ⟨1, 0⟩ (ByteSlice.cellsFrom (bytes 4) 0) (ByteSlice.imageView (bytes 4))
    (fun i => (bytes 4)[i]?.getD 0) (ByteSlice.array_geometry _) (ByteSlice.image_represents _) reads (by decide)
    0 0 (WyhashUpdate.init_invariant 0) (by decide) (by decide)

theorem empty_full_buffer_one_past : agrees (prepared 48) [] = true := by decide +kernel

theorem second_parameter_oom_cleans_first :
    (let state := { caller initial (bytes 4) with nextAddress := addressLimit - 24 }
    match GeneratedWyhashUpdate.update.runFuel 10000 (arguments 4) state with
    | .finished (.error .outOfMemory) after =>
        decide (after.valid = true ∧ after.heap = state.heap ∧ after.nextId = state.nextId + 1 ∧
          after.nextAddress = addressLimit - 16)
    | _ => false) = true := by decide +kernel

theorem no_initial_spare_address_required :
    (let state := { caller initial (bytes 4) with nextAddress := addressLimit }
    state.valid && match GeneratedWyhashUpdate.update.runFuel 10000 (arguments 4) state with
      | .finished (.error .outOfMemory) after => decide (after = state)
      | _ => false) = true := by decide +kernel

end Compiler.ZigAir.WyhashUpdateAirTests
