/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryExpLoop
import Compiler.ZigAir.MemoryAllocationLaws

/-! Checked allocation and initialization of the captured exp256 scratch
words. Each successful stage establishes the next stage's local invariant;
allocation and write faults retain their exact preceding effects. -/
namespace Compiler.ZigAir.MemoryExp
open Memory MemoryAir Control.Machine

inductive Preparation where
  | fault (reason : Fault) (state : State)
  | ready (baseSlot exponentSlot resultSlot : Address) (state : State)

def resultStored (baseSlot exponentSlot resultSlot : Address) (state : State) : Except Fault State → Preparation
  | .error reason => .fault reason state
  | .ok after => .ready baseSlot exponentSlot resultSlot after

def resultAllocated (baseSlot exponentSlot : Address) (state : State) : Except Fault (Value × State) → Preparation
  | .error reason => .fault reason state
  | .ok (pointer, after) => resultStored baseSlot exponentSlot ⟨state.nextId, 0⟩ after (store after pointer (number 1))

def exponentStored (baseSlot exponentSlot : Address) (state : State) : Except Fault State → Preparation
  | .error reason => .fault reason state
  | .ok after => resultAllocated baseSlot exponentSlot after (allocate after wordType)

def exponentAllocated (exponent : Word) (baseSlot : Address) (state : State) : Except Fault (Value × State) → Preparation
  | .error reason => .fault reason state
  | .ok (pointer, after) => exponentStored baseSlot ⟨state.nextId, 0⟩ after (store after pointer (number exponent))

def baseStored (exponent : Word) (baseSlot : Address) (state : State) : Except Fault State → Preparation
  | .error reason => .fault reason state
  | .ok after => exponentAllocated exponent baseSlot after (allocate after wordType)

def baseAllocated (base exponent : Word) (state : State) : Except Fault (Value × State) → Preparation
  | .error reason => .fault reason state
  | .ok (pointer, after) => baseStored exponent ⟨state.nextId, 0⟩ after (store after pointer (number base))

def prepare (base exponent : Word) (state : State) : Preparation :=
  baseAllocated base exponent state (allocate state wordType)

def preparedOutcome (base exponent : Word) : Preparation → Control.Outcome Value Fault State
  | .fault reason after => .fault reason after
  | .ready baseSlot exponentSlot resultSlot after =>
      outcome (effects baseSlot exponentSlot resultSlot base exponent 1 after)

def loopCode : Control.Code Ty Prim Ref true :=
  (GeneratedMemory.fn_exp256.body.block? 10).getD (.ret unitRef)
def resultStoreCode : Control.Code Ty Prim Ref true :=
  .bind 9 (.scalar .unit) (.store (.local 8) (.constant (number 1))) loopCode
def resultAllocateCode : Control.Code Ty Prim Ref true :=
  .bind 8 (.pointer true false wordType) (.alloc wordType) resultStoreCode
def exponentStoreCode : Control.Code Ty Prim Ref true :=
  .bind 6 (.scalar .unit) (.store (.local 5) (.local 1)) resultAllocateCode
def exponentAllocateCode : Control.Code Ty Prim Ref true :=
  .bind 5 (.pointer true false wordType) (.alloc wordType) exponentStoreCode
def baseStoreCode : Control.Code Ty Prim Ref true :=
  .bind 3 (.scalar .unit) (.store (.local 2) (.local 0)) exponentAllocateCode
def baseAllocateCode : Control.Code Ty Prim Ref true :=
  .bind 2 (.pointer true false wordType) (.alloc wordType) baseStoreCode
def prologue : Control.Code Ty Prim Ref true :=
  .bind 0 wordType (.argument 0) (.bind 1 wordType (.argument 1) baseAllocateCode)

theorem generated_prologue : GeneratedMemory.fn_exp256.body = prologue := by rfl

theorem result_store_steps (base exponent : Word) (baseSlot exponentSlot resultSlot : Address)
    (args : List Value) (env : Env) (state : State)
    (locals : Locals env baseSlot exponentSlot resultSlot)
    (readBase : load state (slot baseSlot) = .ok (number base))
    (readExponent : load state (slot exponentSlot) = .ok (number exponent))
    (separate : Separate baseSlot exponentSlot resultSlot) :
    Steps semantics args (.suspended ⟨resultStoreCode, env, state, []⟩)
      (.finished (preparedOutcome base exponent
        (resultStored baseSlot exponentSlot resultSlot state (store state (slot resultSlot) (number 1))))) := by
  have pointer := local_ref env 8 (slot resultSlot) locals.2.2 rfl
  have one := Ref.eval_constant_of_valid (number 1) env (number_valid 1)
  cases written : store state (slot resultSlot) (number 1) with
  | error reason =>
    exact Steps.bind_fault semantics args
      (Prim.eval_store_fault _ _ args env state _ _ reason pointer one written)
  | ok after =>
    apply Steps.bind_ok semantics args (Prim.eval_store_ok _ _ args env state after _ _ pointer one written) (by rfl)
    exact initialized_steps base exponent 1 args _ after baseSlot exponentSlot resultSlot []
      (by simpa [Locals, Control.Env.set] using locals)
      ⟨(slot_frame state after resultSlot baseSlot 1 written separate.2.1).trans readBase,
        (slot_frame state after resultSlot exponentSlot 1 written separate.2.2).trans readExponent,
        slot_readback state after resultSlot 1 written⟩ separate

theorem result_allocate_steps (base exponent : Word) (baseSlot exponentSlot : Address)
    (args : List Value) (env : Env) (state : State)
    (h2 : env 2 = some (slot baseSlot)) (h5 : env 5 = some (slot exponentSlot))
    (readBase : load state (slot baseSlot) = .ok (number base))
    (readExponent : load state (slot exponentSlot) = .ok (number exponent))
    (ordered : baseSlot.allocation < exponentSlot.allocation) (fresh : exponentSlot.allocation < state.nextId) :
    Steps semantics args (.suspended ⟨resultAllocateCode, env, state, []⟩)
      (.finished (preparedOutcome base exponent (resultAllocated baseSlot exponentSlot state (allocate state wordType)))) := by
  cases allocated : allocate state wordType with
  | error reason => exact Steps.bind_fault semantics args (Prim.eval_alloc_fault wordType args env state reason allocated)
  | ok pair =>
    rcases pair with ⟨pointer, after⟩
    obtain ⟨rfl, _⟩ := allocate_pointer state wordType pointer after allocated
    apply Steps.bind_ok semantics args (Prim.eval_alloc_ok wordType args env state after _ allocated) (by rfl)
    exact result_store_steps base exponent baseSlot exponentSlot ⟨state.nextId, 0⟩ args _ after
      (by simp [Locals, Control.Env.set, slot, h2, h5])
      ((load_after_allocate state wordType _ after true false wordType baseSlot allocated (by omega)).trans readBase)
      ((load_after_allocate state wordType _ after true false wordType exponentSlot allocated (by omega)).trans readExponent)
      ⟨by omega, by dsimp; omega, by dsimp; omega⟩

theorem exponent_store_steps (base exponent : Word) (baseSlot exponentSlot : Address)
    (args : List Value) (env : Env) (state : State)
    (h1 : env 1 = some (number exponent)) (h2 : env 2 = some (slot baseSlot)) (h5 : env 5 = some (slot exponentSlot))
    (readBase : load state (slot baseSlot) = .ok (number base))
    (ordered : baseSlot.allocation < exponentSlot.allocation) (fresh : exponentSlot.allocation < state.nextId) :
    Steps semantics args (.suspended ⟨exponentStoreCode, env, state, []⟩)
      (.finished (preparedOutcome base exponent
        (exponentStored baseSlot exponentSlot state (store state (slot exponentSlot) (number exponent))))) := by
  have pointer := local_ref env 5 (slot exponentSlot) h5 rfl
  have value := local_ref env 1 (number exponent) h1 (number_valid exponent)
  cases written : store state (slot exponentSlot) (number exponent) with
  | error reason =>
    exact Steps.bind_fault semantics args
      (Prim.eval_store_fault _ _ args env state _ _ reason pointer value written)
  | ok after =>
    apply Steps.bind_ok semantics args (Prim.eval_store_ok _ _ args env state after _ _ pointer value written) (by rfl)
    have counters := (store_keeps_counters state _ _ after written).1
    exact result_allocate_steps base exponent baseSlot exponentSlot args _ after
      (by simp [Control.Env.set, h2]) (by simp [Control.Env.set, h5])
      ((slot_frame state after exponentSlot baseSlot exponent written (by omega)).trans readBase)
      (slot_readback state after exponentSlot exponent written) ordered (by omega)

theorem exponent_allocate_steps (base exponent : Word) (baseSlot : Address)
    (args : List Value) (env : Env) (state : State)
    (h1 : env 1 = some (number exponent)) (h2 : env 2 = some (slot baseSlot))
    (readBase : load state (slot baseSlot) = .ok (number base)) (fresh : baseSlot.allocation < state.nextId) :
    Steps semantics args (.suspended ⟨exponentAllocateCode, env, state, []⟩)
      (.finished (preparedOutcome base exponent (exponentAllocated exponent baseSlot state (allocate state wordType)))) := by
  cases allocated : allocate state wordType with
  | error reason => exact Steps.bind_fault semantics args (Prim.eval_alloc_fault wordType args env state reason allocated)
  | ok pair =>
    rcases pair with ⟨pointer, after⟩
    obtain ⟨rfl, nextId⟩ := allocate_pointer state wordType pointer after allocated
    apply Steps.bind_ok semantics args (Prim.eval_alloc_ok wordType args env state after _ allocated) (by rfl)
    exact exponent_store_steps base exponent baseSlot ⟨state.nextId, 0⟩ args _ after
      (by simp [Control.Env.set, h1]) (by simp [Control.Env.set, h2]) (by simp [Control.Env.set, slot])
      ((load_after_allocate state wordType _ after true false wordType baseSlot allocated (by omega)).trans readBase)
      fresh (by dsimp; omega)

theorem base_store_steps (base exponent : Word) (baseSlot : Address)
    (args : List Value) (env : Env) (state : State)
    (h0 : env 0 = some (number base)) (h1 : env 1 = some (number exponent)) (h2 : env 2 = some (slot baseSlot))
    (fresh : baseSlot.allocation < state.nextId) :
    Steps semantics args (.suspended ⟨baseStoreCode, env, state, []⟩)
      (.finished (preparedOutcome base exponent
        (baseStored exponent baseSlot state (store state (slot baseSlot) (number base))))) := by
  have pointer := local_ref env 2 (slot baseSlot) h2 rfl
  have value := local_ref env 0 (number base) h0 (number_valid base)
  cases written : store state (slot baseSlot) (number base) with
  | error reason =>
    exact Steps.bind_fault semantics args
      (Prim.eval_store_fault _ _ args env state _ _ reason pointer value written)
  | ok after =>
    apply Steps.bind_ok semantics args (Prim.eval_store_ok _ _ args env state after _ _ pointer value written) (by rfl)
    have counters := (store_keeps_counters state _ _ after written).1
    exact exponent_allocate_steps base exponent baseSlot args _ after
      (by simp [Control.Env.set, h1]) (by simp [Control.Env.set, h2])
      (slot_readback state after baseSlot base written) (by omega)

theorem base_allocate_steps (base exponent : Word) (args : List Value) (env : Env) (state : State)
    (h0 : env 0 = some (number base)) (h1 : env 1 = some (number exponent)) :
    Steps semantics args (.suspended ⟨baseAllocateCode, env, state, []⟩)
      (.finished (preparedOutcome base exponent (prepare base exponent state))) := by
  cases allocated : allocate state wordType with
  | error reason =>
    simp only [prepare, allocated, baseAllocated, preparedOutcome]
    exact Steps.bind_fault semantics args (Prim.eval_alloc_fault wordType args env state reason allocated)
  | ok pair =>
    rcases pair with ⟨pointer, after⟩
    obtain ⟨rfl, nextId⟩ := allocate_pointer state wordType pointer after allocated
    simp only [prepare, allocated, baseAllocated]
    apply Steps.bind_ok semantics args (Prim.eval_alloc_ok wordType args env state after _ allocated) (by rfl)
    exact base_store_steps base exponent ⟨state.nextId, 0⟩ args _ after
      (by simp [Control.Env.set, h0]) (by simp [Control.Env.set, h1]) (by simp [Control.Env.set, slot])
      (by dsimp; omega)

def arguments (base exponent : Word) : List Value := [number base, number exponent]

/-- The complete captured body, without assumed successful allocation,
successful writes, initialized scratch slots or a termination premise. -/
theorem exp_body_steps (base exponent : Word) (state : State) :
    Steps semantics (arguments base exponent)
      (.suspended ⟨GeneratedMemory.fn_exp256.body, fun _ => none, state, []⟩)
      (.finished (preparedOutcome base exponent (prepare base exponent state))) := by
  rw [generated_prologue]
  have arg0 (env : Env) : (Prim.argument 0).eval (arguments base exponent) env state =
      (.ok (number base), state) := by rw [Prim.eval_argument]; rfl
  have arg1 (env : Env) : (Prim.argument 1).eval (arguments base exponent) env state =
      (.ok (number exponent), state) := by rw [Prim.eval_argument]; rfl
  let empty : Env := fun _ => none
  let first := empty.set 0 (number base)
  have typed (w : Word) : semantics.hasType (number w) wordType = true := by
    simpa only [semantics] using number_typed w
  apply Steps.bind_ok semantics (arguments base exponent) (prim := .argument 0) (value := number base) (type := wordType) (arg0 empty) (typed base)
  apply Steps.bind_ok semantics (arguments base exponent) (prim := .argument 1) (value := number exponent) (type := wordType) (arg1 first) (typed exponent)
  exact base_allocate_steps base exponent _ _ state (by simp [Control.Env.set]) (by simp [Control.Env.set])

end Compiler.ZigAir.MemoryExp
