/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MachineCoverage
import Compiler.ZigAir.ControlTests

namespace Compiler.ZigAir.MachineObservationTests
open Control Control.Machine ControlTests

def observed (fuel : Nat) (code : Code Bool Prim Ref true) :=
  trace semantics [] fuel (.suspended ⟨code, fun _ => none, [], []⟩)

def spin : Code Bool Prim Ref true := .loop rfl 0 (.bind 1 true (.record 7) (.repeat rfl 0))

theorem repeated_states : ((observed 6 spin).1.map (fun e => (e.site.1, e.state))) =
    [(1, []), (1, [7]), (1, [7, 7])] := rfl

theorem repeated_environments : ((observed 6 spin).1.map (fun e => e.env 1)) = [none, some 7, some 7] := rfl

theorem failed_attempt_retained :
    let result := observed 9 (.bind 0 true (.record 7) (.bind 1 true (.fail 9) (.ret (.literal 0))))
    result.1.map (fun e => (e.site.1, e.state)) = [(0, []), (1, [7])] ∧
    result.2 = .finished (.fault .operation [7, 9]) := ⟨rfl, rfl⟩

theorem bad_type_attempt_retained :
    let result := observed 9 (.bind 0 false (.record 7) (.ret (.literal 0)))
    result.1.map (fun e => (e.site.1, e.state)) = [(0, [])] ∧
    result.2 = .finished (.fault .malformed [7]) := ⟨rfl, rfl⟩

theorem unselected_branch_absent :
    (observed 9 (.branch (.literal 0) (.bind 0 true (.fail 9) (.ret (.literal 0))) (.ret (.literal 1)))).1 = [] := rfl

theorem zero_budget_empty : (observed 0 spin).1 = [] := rfl

theorem resumed_observations :
    let first := observed 3 spin
    let rest := trace semantics [] 3 first.2
    first.1 ++ rest.1 = (observed 6 spin).1 := by
  exact (congrArg Prod.fst (trace_add semantics [] 3 3 (.suspended ⟨spin, fun _ => none, [], []⟩))).symm

end Compiler.ZigAir.MachineObservationTests
