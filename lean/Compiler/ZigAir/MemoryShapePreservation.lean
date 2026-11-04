/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryAllocationShape
import Compiler.ZigAir.MemoryMachine
import Compiler.ZigAir.MachineObservations

namespace Compiler.ZigAir.MemoryAir
open Memory Control.Machine

private theorem bind_success {α β : Type} (first : Except Fault α) (next : α → Except Fault β)
    (result : β) (success : first >>= next = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp_all [bind, Except.bind]

theorem Prim.transition_retains_shape (prim : Prim) (args : List Value) (env : Env)
    (state : State) (value : Value) (after : State) (initial : state.valid = true)
    (success : prim.transition args env state = .ok (value, after)) :
    state.heap.RetainsShape after.heap := by
  cases prim with
  | alloc child => exact allocate_retains_shape state child value after initial success
  | store pointer operand =>
    rcases bind_success (pointer.eval env) _ _ success with ⟨p, _, rest⟩
    rcases bind_success (operand.eval env) _ _ rest with ⟨v, _, rest⟩
    rcases bind_success (Memory.store state p v) _ _ rest with ⟨stored, written, same⟩
    cases (Prod.mk.inj (Except.ok.inj same)).2
    exact store_retains_shape state p v after written
  | wordByteStore order pointer operand =>
    rcases bind_success (pointer.eval env) _ _ success with ⟨p, _, rest⟩
    rcases bind_success (operand.eval env) _ _ rest with ⟨v, _, rest⟩
    rcases bind_success (ByteAccess.write order state p v) _ _ rest with ⟨stored, written, same⟩
    cases (Prod.mk.inj (Except.ok.inj same)).2
    obtain ⟨wordPointer, wordValue, effect⟩ := ByteAccess.write_store order state after p v written
    exact store_retains_shape state wordPointer wordValue after effect
  | _ =>
    simp only [Prim.transition, bind, Except.bind] at success
    repeat' split at success
    all_goals first
      | contradiction
      | (cases (Prod.mk.inj (Except.ok.inj success)).2; exact Heap.RetainsShape.refl _)

/-- Includes faults, which retain the state immediately before the primitive. -/
theorem Prim.retains_shape (prim : Prim) (args : List Value) (env : Env)
    (state : State) (initial : state.valid = true) : state.heap.RetainsShape (prim.eval args env state).2.heap := by
  cases step : prim.transition args env state with
  | error fault => simpa [Prim.eval, step] using Heap.RetainsShape.refl state.heap
  | ok result =>
    rcases result with ⟨value, after⟩
    simpa [Prim.eval, step] using prim.transition_retains_shape args env state value after initial step

theorem machine_steps_retain_shape (args : List Value)
    (first last : Execution Ty Prim Ref Value Fault State)
    (path : Steps semantics args first last) (initial : first.state.valid = true) :
    first.state.heap.RetainsShape last.state.heap := by
  have result := path.preserves semantics args
    (fun state => state.valid = true ∧ first.state.heap.RetainsShape state.heap)
    (fun prim args env state h => ⟨prim.preserves_valid args env state h.1,
      h.2.trans (prim.retains_shape args env state h.1)⟩)
    ⟨initial, Heap.RetainsShape.refl _⟩
  exact result.2

theorem observed_retains_shape (args : List Value) (fuel : Nat) (config : Config Ty Prim Ref Value State)
    (initial : config.state.valid = true) (event : Observation Ty Prim Value State)
    (present : event ∈ (trace semantics args fuel (.suspended config)).1) :
    config.state.heap.RetainsShape event.state.heap := by
  obtain ⟨next, reached, recorded⟩ := trace_reachable semantics args fuel (.suspended config) event present
  have retained := machine_steps_retain_shape args _ _ reached initial
  cases code : next.code <;> simp_all [observe]
  cases recorded
  exact retained

/-- The invocation's original allocation mark also protects the caller's stack
cells on every completed or suspended path; fresh stack cells may be removed. -/
theorem machine_steps_cleanup_retain_shape (args : List Value)
    (first last : Execution Ty Prim Ref Value Fault State)
    (path : Steps semantics args first last) (initial : first.state.valid = true) :
    first.state.heap.RetainsShape (cleanup first.state.nextId last.state).heap :=
  cleanup_retains_shape first.state last.state initial (machine_steps_retain_shape args first last path initial)

end Compiler.ZigAir.MemoryAir
