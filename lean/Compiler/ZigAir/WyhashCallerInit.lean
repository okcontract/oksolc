/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.AggregateCall
import Compiler.ZigAir.WyhashInitRun
import Compiler.ZigAir.GeneratedExpressionHashInit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Compiler.ZigAir.WyhashCallerInit
open Memory AggregateAir Compiler.Extraction

/-- A cut through the caller's hasher allocation, nested initializer call and
return store. Key admission before this cut and the updates after it are open. -/
def code (seed : BitVec 64) (next : AggregateCall.Code) : AggregateCall.Code :=
  AggregateCall.allocateCallStore 4 5 6 GeneratedWyhashInit.fn_init [.constant (number seed)] next

/-- Bind the generic seed-parametric proof to the actual captured seed-zero cut. -/
theorem source_code (next : AggregateCall.Code) : code 0 next = GeneratedExpressionHashInit.fragment next := rfl

def afterEnv (env : Env) (id : Nat) (seed : BitVec 64) : Env :=
  ((env.set 4 (WyhashInit.objectPointer id)).set 5 (WyhashInit.result seed)).set 6 WyhashInit.unit

def completion (next : AggregateCall.Code) (args : List Register) (env : Env)
    (result : Except Fault Unit) (state : State) : Control.Outcome Register Fault State :=
  match result with
  | .error fault => .fault fault state
  | .ok () => next.eval AggregateCall.semantics args env state

/-- The arbitrary continuation sees the caller's initialized local. Nested
callee locals are retired on both success and exhaustion; no allocation-room
or callback-correctness premise is required. -/
theorem prefix_verified (state : State) (seed : BitVec 64) (next : AggregateCall.Code)
    (args : List Register) (env : Env) (valid : state.valid = true) :
    ∃ result after,
      (code seed next).eval AggregateCall.semantics args env state =
        completion next args (afterEnv env state.nextId seed) result after ∧
      StackFrame state after ∧
      (result = .error .outOfMemory ∨ (result = .ok () ∧ ∃ cell,
        after.heap.lookup state.nextId = some cell ∧ cell.type = WyhashInit.objectType ∧
        cell.cells = WyhashUpdate.initialCells (WyhashUpdate.seedState seed) ∧ cell.writable = true)) := by
  cases allocation : Memory.allocate state WyhashInit.objectType with
  | error fault =>
    have same := StackFrame.allocation_fault state _ ⟨104, 8⟩ fault valid WyhashInit.object_layout allocation
    subst fault
    refine ⟨.error .outOfMemory, state, ?_, StackFrame.refl state valid, Or.inl rfl⟩
    apply AggregateCall.bind_fault
    change (AggregateAir.Prim.memory (.alloc WyhashInit.objectType)).eval args env state = _
    simp only [AggregateAir.Prim.eval, AggregateAir.Prim.transition,
      MemoryAir.Prim.transition, allocation, bind, Except.bind]
  | ok pair =>
    obtain ⟨pointer, allocated⟩ := pair
    obtain ⟨layout, base, shape, pointerEq, stateEq⟩ := allocate_shape state _ pointer allocated allocation
    have layoutEq : layout = ⟨104, 8⟩ := Option.some.inj (shape.symm.trans WyhashInit.object_layout)
    subst layout
    let cell : Allocation := ⟨base, WyhashInit.objectType, [], true, true⟩
    have found : allocated.heap.lookup state.nextId = some cell := by
      simp only [stateEq, Heap.lookup_cons, ↓reduceIte, cell]
    have allocatedFrame := (StackFrame.refl state valid).allocate _ pointer allocated allocation
    let e1 := env.set 4 (WyhashInit.objectPointer state.nextId)
    have first : (code seed next).eval AggregateCall.semantics args env state =
        (Control.Code.bind 5 WyhashInit.objectType (.invoke GeneratedWyhashInit.fn_init [.constant (number seed)])
          (.bind 6 (.scalar .unit) (.primitive (.store (.local 4) (.local 5))) next) : AggregateCall.Code).eval
            AggregateCall.semantics args e1 allocated := by
      apply AggregateCall.bind_ok
      · simpa only [pointerEq] using eval_alloc _ args env _ _ _ allocation
      · exact pointer_typed _ _
    obtain ⟨value, middle, called, calleeFrame, outcome⟩ := WyhashInit.run_framed allocated seed allocatedFrame.valid
    have invoked := (AggregateCall.invoke_constant GeneratedWyhashInit.fn_init (number seed) args e1 allocated
      (number_valid seed)).trans called
    have stack := allocatedFrame.trans calleeFrame
    rcases outcome with success | failure
    · rw [success] at invoked
      let frame := CellFrame.of_valid middle state.nextId cell ⟨104, 8⟩ calleeFrame.valid
        (calleeFrame.old_lookup _ _ found) WyhashInit.object_layout (by decide) rfl
      let cells := WyhashUpdate.initialCells (WyhashUpdate.seedState seed)
      have cellsValid : cells.valid WyhashInit.objectType = true := WyhashInit.initialized_valid _
      have stored : AggregateAir.store middle (.pointer (.pointer true false WyhashInit.objectType) ⟨state.nextId, 0⟩)
          (WyhashInit.result seed) = .ok (frame.install cells) :=
        store_root frame cells WyhashInit.object_aggregate cellsValid
      have resultValid : (WyhashInit.result seed).valid = true := WyhashInit.result_valid _
      refine ⟨.ok (), frame.install cells, ?_, stack.install _ frame cells (Nat.le_refl _) cellsValid,
        Or.inr ⟨rfl, { cell with cells }, frame.lookup cells, rfl, rfl, rfl⟩⟩
      rw [first, AggregateCall.bind_ok _ _ _ _ _ _ _ _ _ invoked (WyhashInit.result_typed _)]
      change _ = next.eval AggregateCall.semantics args (afterEnv env state.nextId seed) (frame.install cells)
      apply AggregateCall.bind_ok
      · apply eval_store _ _ _ _ _ _
          (.pointer (.pointer true false WyhashInit.objectType) ⟨state.nextId, 0⟩) (WyhashInit.result seed)
        · exact value_local _ 4 _ (by simp [e1, Control.Env.set, WyhashInit.objectPointer]) rfl
        · exact ref_local _ 5 _ rfl resultValid
        · exact stored
      · rfl
    · rw [failure] at invoked
      exact ⟨.error .outOfMemory, middle,
        first.trans (AggregateCall.bind_fault _ _ _ _ _ _ _ _ _ invoked), stack, Or.inl rfl⟩

/-- Close only the fragment by returning its live local identifier. This cut is
not the source hash function's return, which remains in the unverified suffix. -/
def run (state : State) (seed : BitVec 64) : Except Fault Nat × State :=
  match (code seed (.ret (.local 4))).eval AggregateCall.semantics [] (fun _ => none) state with
  | .returned (.value (.pointer _ address)) after => (.ok address.allocation, after)
  | .fault fault after => (.error fault, after)
  | .returned _ after | .jumped _ _ _ after => (.error .malformed, after)

theorem run_verified (state : State) (seed : BitVec 64) (valid : state.valid = true) :
    ∃ result after, run state seed = (result, after) ∧ StackFrame state after ∧
      (result = .error .outOfMemory ∨ (result = .ok state.nextId ∧ ∃ cell,
        after.heap.lookup state.nextId = some cell ∧ cell.type = WyhashInit.objectType ∧
        cell.cells = WyhashUpdate.initialCells (WyhashUpdate.seedState seed) ∧ cell.writable = true)) := by
  obtain ⟨result, after, ran, frame, outcome⟩ := prefix_verified state seed (.ret (.local 4)) [] (fun _ => none) valid
  rcases outcome with failure | ⟨success, facts⟩
  · rw [failure] at ran
    exact ⟨_, _, by simp only [run, ran, completion], frame, Or.inl rfl⟩
  · rw [success] at ran
    refine ⟨_, _, ?_, frame, Or.inr ⟨rfl, facts⟩⟩
    unfold run
    rw [ran]
    simp only [completion, Control.Code.eval, AggregateCall.semantics]
    rw [ref_local _ 4 (WyhashInit.objectPointer state.nextId) (by simp [afterEnv, Control.Env.set]) rfl]
    rfl

end Compiler.ZigAir.WyhashCallerInit
