/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.ControlTests
import Compiler.ZigAir.Machine

/-! Control-only regression clients. Synthetic event traces expose effects,
SSA rebinding and unwinding; these are not captured Zig loop artifacts. -/
namespace Compiler.ZigAir.MachineTests
open Control Control.Machine ControlTests

private def start (code : Code Bool Prim Ref true) : Config Bool Prim Ref Nat (List Nat) :=
  ⟨code, fun _ => none, [], []⟩

private def exec (fuel : Nat) (code : Code Bool Prim Ref true) := run semantics [] fuel (start code)

private def spin : Code Bool Prim Ref true := .loop rfl 0 (.bind 1 true (.record 7) (.repeat rfl 0))

theorem zero_fuel_suspends : exec 0 spin = .suspended (start spin) := by rfl

theorem repeated_effects_are_retained : (exec 6 spin).state = [7, 7, 7] := by rfl

theorem backedge_keeps_frame :
    exec 3 spin = .suspended ⟨.bind 1 true (.record 7) (.repeat rfl 0),
      Env.set (fun _ => none) 1 7, [7], [.loop 0 (.bind 1 true (.record 7) (.repeat rfl 0))]⟩ := by rfl

theorem repeat_unwinds_inner_frames :
    (exec 9 (.loop rfl 0 (.block 2 true
      (.bind 1 true (.record 7) (.repeat rfl 0)) (.ret (.literal 99))))).state = [7, 7, 7] := by rfl

theorem jump_exits_loop :
    exec 5 (.block 0 true (.loop rfl 1 (.bind 2 true (.record 7) (.jump 0 (.local 2))))
      (.ret (.local 0))) = .finished (.returned 7 [7]) := by rfl

theorem loop_return_skips_frames :
    exec 4 (.block 0 true (.loop rfl 1 (.bind 2 true (.record 7) (.ret (.local 2))))
      (.bind 3 true (.record 99) (.ret (.local 3)))) = .finished (.returned 7 [7]) := by rfl

theorem loop_fault_keeps_effects :
    exec 4 (.loop rfl 0 (.bind 1 true (.record 7) (.bind 2 true (.fail 9) (.repeat rfl 0)))) =
      .finished (.fault .operation [7, 9]) := by rfl

theorem missing_repeat_target_rejects :
    exec 2 (.bind 1 true (.record 7) (.repeat rfl 99)) = .finished (.fault .malformed [7]) := by rfl

theorem repeat_cannot_target_block :
    exec 3 (.block 0 true (.bind 1 true (.record 7) (.repeat rfl 0)) (.ret (.local 0))) =
      .finished (.fault .malformed [7]) := by rfl

theorem jump_cannot_target_loop :
    exec 3 (.loop rfl 0 (.bind 1 true (.record 7) (.jump 0 (.local 1)))) =
      .finished (.fault .malformed [7]) := by rfl

theorem unselected_repeat_does_not_execute :
    exec 2 (.branch (.literal 0) (.repeat rfl 99) (.ret (.literal 7))) =
      .finished (.returned 7 []) := by rfl

/-- Each record reads the accumulated event count to decide whether to repeat.
The state is deliberately observable; a back edge must not restore it. -/
private def counting : Semantics Bool Prim Ref Nat Fault (List Nat) :=
  { semantics with evalPrim := fun prim args env state => match prim with
    | .record event => (.ok (if state.length < 2 then 1 else 0), state ++ [event])
    | .fail _ => semantics.evalPrim prim args env state }

private def countLoop : Code Bool Prim Ref true :=
  .loop rfl 0 (.bind 1 true (.record 7) (.branch (.local 1) (.repeat rfl 0) (.ret (.local 1))))

theorem repeated_binding_observes_current_state :
    run counting [] 10 (start countLoop) = .finished (.returned 0 [7, 7, 7]) := by rfl

theorem resumed_loop_matches_uninterrupted :
    advance counting [] 6 (run counting [] 4 (start countLoop)) =
      .finished (.returned 0 [7, 7, 7]) := by rfl

end Compiler.ZigAir.MachineTests
