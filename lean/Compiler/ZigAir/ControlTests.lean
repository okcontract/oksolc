/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.Control

/-! Event traces expose effects that a scalar Unit state cannot observe. These
closed regressions exercise the shared interpreter; events are not a proposed
heap abstraction or a claim about Zig cleanup/allocator semantics. -/
namespace Compiler.ZigAir.ControlTests
open Control

inductive Ref where | literal (value : Nat) | local (id : Nat)
inductive Prim where | record (event : Nat) | fail (event : Nat)
inductive Fault where | malformed | operation

def semantics : Semantics Bool Prim Ref Nat Fault (List Nat) where
  hasType := fun _ allowed => allowed
  truth := fun value => if value = 0 then some false else if value = 1 then some true else none
  evalRef := fun ref env => match ref with
    | .literal value => .ok value
    | .local id => match env id with | some value => .ok value | none => .error .malformed
  evalPrim := fun prim _ _ state => match prim with
    | .record event => (.ok event, state ++ [event])
    | .fail event => (.error .operation, state ++ [event])
  malformed := .malformed

def run (code : Code Bool Prim Ref) := code.eval semantics [] (fun _ => none) []

theorem failed_primitive_keeps_effects :
    run (.bind 0 true (.record 7) (.bind 1 true (.fail 9) (.ret (.literal 0)))) =
      .fault .operation [7, 9] := by rfl

theorem type_failure_keeps_effects :
    run (.bind 0 false (.record 7) (.ret (.literal 0))) = .fault .malformed [7] := by rfl

theorem unselected_branch_has_no_effects :
    run (.branch (.literal 0) (.bind 0 true (.fail 9) (.ret (.literal 0))) (.ret (.literal 1))) =
      .returned 1 [] := by rfl

theorem outer_jump_keeps_state_and_environment :
    run (.block 0 true
      (.block 1 true (.bind 2 true (.record 1) (.jump 0 (.local 2)))
        (.bind 3 true (.record 99) (.ret (.literal 0))))
      (.bind 4 true (.record 8) (.branch (.local 2) (.ret (.local 0)) (.ret (.literal 0))))) =
      .returned 1 [1, 8] := by rfl

theorem returned_state_skips_continuation :
    run (.block 0 true (.bind 1 true (.record 7) (.ret (.local 1)))
      (.bind 2 true (.record 99) (.ret (.literal 0)))) = .returned 7 [7] := by rfl

theorem branch_reads_effectful_binding :
    run (.bind 0 true (.record 1) (.branch (.local 0)
      (.bind 1 true (.record 7) (.ret (.local 1)))
      (.bind 2 true (.fail 99) (.ret (.literal 0))))) = .returned 7 [1, 7] := by rfl

theorem invalid_block_result_keeps_effects :
    run (.block 0 false (.bind 1 true (.record 7) (.jump 0 (.local 1)))
      (.bind 2 true (.record 99) (.ret (.literal 0)))) = .fault .malformed [7] := by rfl

theorem reference_failure_keeps_prefix :
    run (.bind 0 true (.record 7) (.ret (.local 1))) = .fault .malformed [7] := by rfl

end Compiler.ZigAir.ControlTests
