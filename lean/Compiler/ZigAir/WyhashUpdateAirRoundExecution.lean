/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirRoundLanes

set_option maxRecDepth 8192

namespace Compiler.ZigAir.WyhashUpdateAir.Round
open Memory AggregateAir Compiler.Extraction Control.Machine

def parameterBase (loop : Bool) : Nat := if loop then 345 else 88
def selfArgument (loop : Bool) : Nat := if loop then 337 else 83
def inputArgument (loop : Bool) : Nat := if loop then 343 else 86
def parameterSite (loop : Bool) : Code :=
  (if loop then loopBody else fillBody).dropBindings (if loop then 8 else 31)

def parameterEnv (env : Env) (loop : Bool) (selfSlot inputSlot : Nat) : Env :=
  AggregateCall.ReadonlyParameter.resultEnv
    (AggregateCall.ReadonlyParameter.resultEnv env (parameterBase loop) selfSlot (.pointer true false objectType))
    (parameterBase loop + 3) inputSlot (WordRead.arrayPointer 48)

theorem generated_parameters : ∀ loop,
    parameterSite loop = AggregateCall.ReadonlyParameter.code (parameterBase loop) (selfArgument loop)
      (.pointer true false objectType)
      (AggregateCall.ReadonlyParameter.code (parameterBase loop + 3) (inputArgument loop)
        (WordRead.arrayPointer 48) (lanesAt loop 0)) := by
  decide +kernel

theorem parameter_bounds : ∀ loop,
    selfArgument loop < parameterBase loop ∧ inputArgument loop < parameterBase loop := by decide +kernel

theorem parameter_registers (env : Env) (loop : Bool) (selfSlot inputSlot : Nat) :
    parameterEnv env loop selfSlot inputSlot (Lane.selfReg loop) =
      some (.value (slot false (.pointer true false objectType) selfSlot)) ∧
    parameterEnv env loop selfSlot inputSlot (Lane.inputReg loop) =
      some (.value (slot false (WordRead.arrayPointer 48) inputSlot)) := by
  cases loop <;> simp [parameterEnv, parameterBase, AggregateCall.ReadonlyParameter.resultEnv,
    Lane.selfReg, Lane.inputReg, Control.Env.set]

theorem parameter_before (env : Env) (loop : Bool) (selfSlot inputSlot query : Nat)
    (earlier : query < parameterBase loop) : parameterEnv env loop selfSlot inputSlot query = env query := by
  exact (AggregateCall.ReadonlyParameter.before _ (parameterBase loop + 3) inputSlot query _ (by omega)).trans
    (AggregateCall.ReadonlyParameter.before env (parameterBase loop) selfSlot query _ earlier)

theorem parameters_steps (loop : Bool) (frames : List (Frame Ty AggregateCall.Prim Ref))
    (state : State) (valid : state.valid = true) (id : Nat) (address : Address)
    (args : List Register) (env : Env)
    (foundSelf : env (selfArgument loop) = some (.value (selfPointer id)))
    (foundInput : env (inputArgument loop) = some (.value (.pointer (WordRead.arrayPointer 48) address))) :
    ∃ after, StackFrame state after ∧
      (Steps AggregateCall.semantics args (.suspended ⟨parameterSite loop, env, state, frames⟩)
        (.finished (.fault .outOfMemory after)) ∨
       Steps AggregateCall.semantics args (.suspended ⟨parameterSite loop, env, state, frames⟩)
        (.suspended ⟨lanesAt loop 0, parameterEnv env loop state.nextId (state.nextId + 1), after, frames⟩) ∧
       Memory.load after (slot false (.pointer true false objectType) state.nextId) = .ok (selfPointer id) ∧
       Memory.load after (slot false (WordRead.arrayPointer 48) (state.nextId + 1)) =
         .ok (.pointer (WordRead.arrayPointer 48) address) ∧
       after.nextId = state.nextId + 2 ∧ after.nextAddress < addressLimit) := by
  let next := AggregateCall.ReadonlyParameter.code (parameterBase loop + 3) (inputArgument loop)
    (WordRead.arrayPointer 48) (lanesAt loop 0)
  obtain ⟨middle, firstStack, failed | ⟨first, selfRead, _, firstCount, _⟩⟩ :=
    AggregateCall.ReadonlyParameter.steps (parameterBase loop) (selfArgument loop) (parameter_bounds loop).1
      (selfPointer id) ⟨8, 8⟩ rfl rfl (by decide) next frames state valid args env foundSelf
  · exact ⟨middle, firstStack, Or.inl (by simpa only [next, Value.type, ← generated_parameters loop] using failed)⟩
  · let eSelf := AggregateCall.ReadonlyParameter.resultEnv env (parameterBase loop) state.nextId (.pointer true false objectType)
    have inputFound := (AggregateCall.ReadonlyParameter.before env (parameterBase loop) state.nextId
      (inputArgument loop) (.pointer true false objectType) (parameter_bounds loop).2).trans foundInput
    obtain ⟨after, secondStack, failed | ⟨second, inputRead, _, secondCount, endBound⟩⟩ :=
      AggregateCall.ReadonlyParameter.steps (parameterBase loop + 3) (inputArgument loop)
        (by have := (parameter_bounds loop).2; omega) (.pointer (WordRead.arrayPointer 48) address)
        ⟨8, 8⟩ rfl rfl (by decide) (lanesAt loop 0) frames middle firstStack.valid args eSelf inputFound
    · have path := first.trans AggregateCall.semantics args failed
      exact ⟨after, firstStack.trans secondStack, Or.inl (by simpa only [next, Value.type, ← generated_parameters loop] using path)⟩
    · have path := first.trans AggregateCall.semantics args second
      refine ⟨after, firstStack.trans secondStack, Or.inr ⟨?_, ?_, ?_, by omega, endBound⟩⟩
      · simpa only [parameterEnv, eSelf, firstCount, next, Value.type, ← generated_parameters loop] using path
      · exact secondStack.old_load false false _ _ _ selfRead
      · simpa only [firstCount] using inputRead

/-- Execute both actual round parameter saves and all three captured lanes.
Success is the existing model round; OOM records exactly the completed lane
prefix. No saved-descriptor reads or successful local allocations are premises. -/
theorem steps (loop : Bool) (frames : List (Frame Ty AggregateCall.Prim Ref))
    {state : State} {id : Nat} (frame : CellFrame state id) (valid : state.valid = true)
    (typed : frame.cell.type = objectType) (input : WyhashUpdate.Input) (offset total : Nat)
    (core : WyhashUpdate.Core frame.cell.cells total) (ready : input.Ready frame.cell.cells)
    (address : Address) (bytes : Nat → BitVec 8)
    (represented : ByteSlice.Represents (input.cells frame.cell.cells) input.view bytes)
    (inside : offset + 48 ≤ input.view.length)
    (admitted : InputAdmitted state id input offset address bytes)
    (args : List Register) (env : Env)
    (foundSelf : env (selfArgument loop) = some (.value (selfPointer id)))
    (foundInput : env (inputArgument loop) = some (.value (.pointer (WordRead.arrayPointer 48) address))) :
    ∃ after,
      (∃ completed cells, completed < 3 ∧ lanePrefix input offset completed frame.cell.cells = .ok cells ∧
        WyhashUpdate.Core cells total ∧ StackFrame (frame.install cells) after ∧
        Steps AggregateCall.semantics args (.suspended ⟨parameterSite loop, env, state, frames⟩)
          (.finished (.fault .outOfMemory after))) ∨
      ∃ cells afterEnv, WyhashUpdate.round input offset frame.cell.cells = .ok cells ∧
        WyhashUpdate.Core cells total ∧ input.Ready cells ∧
        (∀ query, query < 16 ∨ 40 ≤ query → cells.lookup query = frame.cell.cells.lookup query) ∧
        StackFrame (frame.install cells) after ∧
        Steps AggregateCall.semantics args (.suspended ⟨parameterSite loop, env, state, frames⟩)
          (.suspended ⟨lanesAt loop 3, afterEnv, after, frames⟩) ∧
        ∀ query < parameterBase loop, afterEnv query = env query := by
  obtain ⟨middle, parameterStack, failed | ⟨parameters, selfRead, inputRead, _, _⟩⟩ :=
    parameters_steps loop frames state valid id address args env foundSelf foundInput
  · refine ⟨middle, Or.inl ⟨0, frame.cell.cells, by decide, rfl, core, ?_, failed⟩⟩
    simpa only [frame.install_current valid] using parameterStack
  · let current := frame.extend parameterStack
    have originalId := (valid_lookup state id frame.cell valid frame.found).1
    have registers := parameter_registers env loop state.nextId (state.nextId + 1)
    obtain ⟨after, ⟨completed, cells, bounded, ran, failedCore, stack, path⟩ |
        ⟨cells, afterEnv, ran, nextCore, nextReady, retained, stack, path, before⟩⟩ :=
      prefix_steps loop 3 (by decide) frames current parameterStack.valid typed input offset total core ready address bytes
        represented inside (InputAdmitted.extend parameterStack input offset address bytes admitted)
        (state.nextId + 1) state.nextId (by omega) (by omega) inputRead selfRead args
        (parameterEnv env loop state.nextId (state.nextId + 1)) registers.2 registers.1
    · have installed := parameterStack.install_old frame cells (typed ▸ failedCore.valid)
      exact ⟨after, Or.inl ⟨completed, cells, bounded, ran, failedCore, installed.trans stack,
        parameters.trans AggregateCall.semantics args path⟩⟩
    · have installed := parameterStack.install_old frame cells (typed ▸ nextCore.valid)
      refine ⟨after, Or.inr ⟨cells, afterEnv, (prefix_complete input offset frame.cell.cells).symm.trans ran,
        nextCore, nextReady, retained, installed.trans stack,
        parameters.trans AggregateCall.semantics args path, ?_⟩⟩
      intro query earlier
      have small : query < readBase loop 0 false := by
        cases loop <;> simp only [parameterBase, readBase, Bool.false_eq_true, ↓reduceIte] at earlier ⊢ <;> omega
      exact (before query small).trans (parameter_before env loop state.nextId (state.nextId + 1) query earlier)

end Compiler.ZigAir.WyhashUpdateAir.Round
