/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirBuffered
import Compiler.ZigAir.AggregateReadonlyParameter

set_option maxRecDepth 8192

namespace Compiler.ZigAir.WyhashUpdateAir
open Memory AggregateAir Compiler.Extraction Control.Machine

def arguments (id : Nat) (address : Address) (length : Nat) : List Register :=
  [.value (selfPointer id), .value (.slice inputType address length)]

def remaining (count : Nat) : Control.Code Ty AggregateCall.Prim Ref true :=
  GeneratedWyhashUpdate.update.body.dropBindings count

def parameterEnv (id : Nat) (address : Address) (length selfSlot inputSlot : Nat) : Env :=
  let env : Env := fun _ => none
  let env := (env.set 0 (.value (selfPointer id))).set 1 (.value (.slice inputType address length))
  let env := (env.set 2 (.value (slot true (.pointer true false objectType) selfSlot))).set 3 (.value (.scalar .unit))
  let env := env.set 4 (.value (slot false (.pointer true false objectType) selfSlot))
  let env := (env.set 5 (.value (slot true inputType inputSlot))).set 6 (.value (.scalar .unit))
  env.set 7 (.value (slot false inputType inputSlot))

theorem saved_readonly (state : State) (child : Ty) (id : Nat) (value : Value)
    (read : Memory.load state (slot true child id) = .ok value) :
    Memory.load state (slot false child id) = .ok value := read

theorem saved_cast (state : State) (child : Ty) (id reg : Nat) (value : Value)
    (read : Memory.load state (slot true child id) = .ok value)
    (args : List Register) (env : Env) (found : env reg = some (.value (slot true child id))) :
    (AggregateAir.Prim.memory (.pointerCast (.pointer false false child) (.local reg))).eval args env state =
      (.ok (.value (slot false child id)), state) :=
  AggregateCall.ReadonlyParameter.cast state child id reg value read args env found

/-- Both parameter slots are allocated and initialized by the captured prefix.
Their later native reads and the strict address bound are derived here. -/
theorem parameters_with_input (state : State) (id : Nat) (address : Address) (length : Nat)
    (valid : state.valid = true) (bound : length < addressLimit) :
    ∃ after, StackFrame state after ∧
      (Steps AggregateCall.semantics (arguments id address length)
          (.suspended ⟨GeneratedWyhashUpdate.update.body, fun _ => none, state, []⟩)
          (.finished (.fault .outOfMemory after)) ∨
       Steps AggregateCall.semantics (arguments id address length)
          (.suspended ⟨GeneratedWyhashUpdate.update.body, fun _ => none, state, []⟩)
          (.suspended ⟨remaining 8, parameterEnv id address length state.nextId (state.nextId + 1), after, []⟩) ∧
        after.nextAddress < addressLimit ∧
        Memory.load after (slot false (.pointer true false objectType) state.nextId) = .ok (selfPointer id) ∧
        Memory.load after (.pointer (.pointer false false usize) ⟨state.nextId + 1, 8⟩) =
          .ok (.scalar (.int false 64 length)) ∧
        Memory.load after (slot false inputType (state.nextId + 1)) = .ok (.slice inputType address length)) := by
  let args := arguments id address length
  let e1 : Env := Control.Env.set (fun _ => none) 0 (.value (selfPointer id))
  let e2 := e1.set 1 (.value (.slice inputType address length))
  have inputValid : (Value.slice inputType address length).valid = true := by
    simpa only [Value.valid, decide_eq_true_eq] using bound
  have inputTyped : (Register.value (.slice inputType address length)).hasType inputType = true := inputValid
  have head : Steps AggregateCall.semantics args
      (.suspended ⟨GeneratedWyhashUpdate.update.body, fun _ => none, state, []⟩)
      (.suspended ⟨remaining 2, e2, state, []⟩) := by
    apply AggregateCall.primitive_steps args
    · rfl
    · rfl
    · apply AggregateCall.primitive_steps args
      · rfl
      · exact inputTyped
      · exact .refl _
  obtain ⟨middle, firstStack, failed | ⟨first, selfRead, _, firstCount, _⟩⟩ :=
    AggregateCall.ReadonlyParameter.steps 2 0 (by decide) (selfPointer id) ⟨8, 8⟩ rfl rfl (by decide)
      (remaining 5) [] state valid args e2 (by simp [e2, e1, Control.Env.set])
  · exact ⟨middle, firstStack, Or.inl (head.trans AggregateCall.semantics args failed)⟩
  · let e4 := AggregateCall.ReadonlyParameter.resultEnv e2 2 state.nextId (.pointer true false objectType)
    have inputFound : e4 1 = some (.value (.slice inputType address length)) := by
      simp [e4, AggregateCall.ReadonlyParameter.resultEnv, e2, Control.Env.set]
    obtain ⟨after, secondStack, failed | ⟨second, inputRead, inputOwner, _, endBound⟩⟩ :=
      AggregateCall.ReadonlyParameter.steps 5 1 (by decide) (.slice inputType address length) ⟨16, 8⟩
        inputValid rfl (by decide) (remaining 8) [] middle firstStack.valid args e4 inputFound
    · exact ⟨after, firstStack.trans secondStack, Or.inl
        (head.trans AggregateCall.semantics args (first.trans AggregateCall.semantics args failed))⟩
    · have path := head.trans AggregateCall.semantics args (first.trans AggregateCall.semantics args second)
      have count := SavedValue.slice_length after middle.nextId false ByteSlice.byte address length inputRead inputOwner
      refine ⟨after, firstStack.trans secondStack, Or.inr ⟨?_, endBound, ?_, ?_, ?_⟩⟩
      · simpa only [AggregateCall.ReadonlyParameter.resultEnv, e4, e2, e1, firstCount, parameterEnv] using path
      · exact secondStack.old_load false false _ _ _ selfRead
      · simpa only [firstCount] using count
      · simpa only [firstCount] using inputRead

theorem parameters (state : State) (id : Nat) (address : Address) (length : Nat)
    (valid : state.valid = true) (bound : length < addressLimit) :
    ∃ after, StackFrame state after ∧
      (Steps AggregateCall.semantics (arguments id address length)
          (.suspended ⟨GeneratedWyhashUpdate.update.body, fun _ => none, state, []⟩)
          (.finished (.fault .outOfMemory after)) ∨
       Steps AggregateCall.semantics (arguments id address length)
          (.suspended ⟨GeneratedWyhashUpdate.update.body, fun _ => none, state, []⟩)
          (.suspended ⟨remaining 8, parameterEnv id address length state.nextId (state.nextId + 1), after, []⟩) ∧
        after.nextAddress < addressLimit ∧
        Memory.load after (slot false (.pointer true false objectType) state.nextId) = .ok (selfPointer id) ∧
        Memory.load after (.pointer (.pointer false false usize) ⟨state.nextId + 1, 8⟩) =
          .ok (.scalar (.int false 64 length))) := by
  obtain ⟨after, stack, failed | ⟨path, strict, selfRead, countRead, _⟩⟩ :=
    parameters_with_input state id address length valid bound
  · exact ⟨after, stack, Or.inl failed⟩
  · exact ⟨after, stack, Or.inr ⟨path, strict, selfRead, countRead⟩⟩

end Compiler.ZigAir.WyhashUpdateAir
