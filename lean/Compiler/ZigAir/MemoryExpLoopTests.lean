/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryExpLoop

namespace Compiler.ZigAir.MemoryExp.Tests
open Memory MemoryAir Control.Machine

private def scratch (base exponent result : Word) (baseWritable exponentWritable resultWritable : Bool := true) : State :=
  ⟨[(0, ⟨16, wordType, [(0, number base)], baseWritable, true⟩),
    (1, ⟨48, wordType, [(0, number exponent)], exponentWritable, true⟩),
    (2, ⟨80, wordType, [(0, number result)], resultWritable, true⟩)], 3, 112⟩

private def locals : Env := ((Control.Env.set (fun _ => none) 2 (slot ⟨0, 0⟩)).set 5 (slot ⟨1, 0⟩)).set 8 (slot ⟨2, 0⟩)

theorem nonempty_witness :
    ∃ fuel, run semantics [] fuel (entry locals (scratch 2 10 1) []) =
      .finished (.returned (number 1024) (scratch 65536 0 1024)) := by
  have computed : effects ⟨0, 0⟩ ⟨1, 0⟩ ⟨2, 0⟩ 2 10 1 (scratch 2 10 1) =
      (.ok 1024, scratch 65536 0 1024) := by rfl'
  simpa only [computed, outcome] using initialized_terminates 2 10 1 [] locals (scratch 2 10 1)
    ⟨0, 0⟩ ⟨1, 0⟩ ⟨2, 0⟩ [] (by unfold Locals; decide) (by refine ⟨?_, ?_, ?_⟩ <;> rfl') (by unfold Separate; decide)

theorem result_write_fault :
    ∃ fuel, run semantics [] fuel (entry locals (scratch 3 1 2 true true false) []) =
      .finished (.fault .readOnly (scratch 3 1 2 true true false)) := by
  have computed : effects ⟨0, 0⟩ ⟨1, 0⟩ ⟨2, 0⟩ 3 1 2 (scratch 3 1 2 true true false) =
      (.error .readOnly, scratch 3 1 2 true true false) := by rfl'
  simpa only [computed, outcome] using initialized_terminates 3 1 2 [] locals (scratch 3 1 2 true true false)
    ⟨0, 0⟩ ⟨1, 0⟩ ⟨2, 0⟩ [] (by unfold Locals; decide) (by refine ⟨?_, ?_, ?_⟩ <;> rfl') (by unfold Separate; decide)

theorem base_write_fault_keeps_result :
    ∃ fuel, run semantics [] fuel (entry locals (scratch 3 1 2 false true true) []) =
      .finished (.fault .readOnly (scratch 3 1 6 false true true)) := by
  have computed : effects ⟨0, 0⟩ ⟨1, 0⟩ ⟨2, 0⟩ 3 1 2 (scratch 3 1 2 false true true) =
      (.error .readOnly, scratch 3 1 6 false true true) := by rfl'
  simpa only [computed, outcome] using initialized_terminates 3 1 2 [] locals (scratch 3 1 2 false true true)
    ⟨0, 0⟩ ⟨1, 0⟩ ⟨2, 0⟩ [] (by unfold Locals; decide) (by refine ⟨?_, ?_, ?_⟩ <;> rfl') (by unfold Separate; decide)

theorem exponent_write_fault_keeps_result_and_base :
    ∃ fuel, run semantics [] fuel (entry locals (scratch 3 1 2 true false true) []) =
      .finished (.fault .readOnly (scratch 9 1 6 true false true)) := by
  have computed : effects ⟨0, 0⟩ ⟨1, 0⟩ ⟨2, 0⟩ 3 1 2 (scratch 3 1 2 true false true) =
      (.error .readOnly, scratch 9 1 6 true false true) := by rfl'
  simpa only [computed, outcome] using initialized_terminates 3 1 2 [] locals (scratch 3 1 2 true false true)
    ⟨0, 0⟩ ⟨1, 0⟩ ⟨2, 0⟩ [] (by unfold Locals; decide) (by refine ⟨?_, ?_, ?_⟩ <;> rfl') (by unfold Separate; decide)

theorem zero_exponent_needs_no_writes :
    ∃ fuel, run semantics [] fuel (entry locals (scratch 3 0 7 false false false) []) =
      .finished (.returned (number 7) (scratch 3 0 7 false false false)) := by
  have computed : effects ⟨0, 0⟩ ⟨1, 0⟩ ⟨2, 0⟩ 3 0 7 (scratch 3 0 7 false false false) =
      (.ok 7, scratch 3 0 7 false false false) := by rfl'
  simpa only [computed, outcome] using initialized_terminates 3 0 7 [] locals (scratch 3 0 7 false false false)
    ⟨0, 0⟩ ⟨1, 0⟩ ⟨2, 0⟩ [] (by unfold Locals; decide) (by refine ⟨?_, ?_, ?_⟩ <;> rfl') (by unfold Separate; decide)

private def headObservation : Control.Outcome Value Fault State → Option (Nat × Except Fault Value)
  | .jumped target _ _ state => some (target, load state (slot ⟨0, 0⟩))
  | _ => none

/-- If base and exponent alias, squaring overwrites the exponent before its
halving read. Distinct scratch lifetime identities are a substantive premise. -/
theorem aliased_slots_change_exponent :
    headObservation (head.eval semantics [] (locals.set 5 (slot ⟨0, 0⟩)) (scratch 3 0 1)) =
      some (12, .ok (number 4)) := by rfl'

end Compiler.ZigAir.MemoryExp.Tests
