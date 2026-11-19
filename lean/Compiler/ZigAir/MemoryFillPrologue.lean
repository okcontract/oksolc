/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryFillLoop
import Compiler.ZigAir.MemoryAllocationLaws

namespace Compiler.ZigAir.MemoryFill
open Memory MemoryAir Control.Machine

inductive Preparation where
  | fault (reason : Fault) (state : State)
  | ready (pointerSlot indexSlot : Address) (state : State)

def indexStored (pointerSlot indexSlot : Address) (state : State) : Except Fault State → Preparation
  | .error fault => .fault fault state
  | .ok after => .ready pointerSlot indexSlot after

def indexAllocated (pointerSlot : Address) (state : State) : Except Fault (Value × State) → Preparation
  | .error fault => .fault fault state
  | .ok (pointer, after) => indexStored pointerSlot ⟨state.nextId, 0⟩ after (store after pointer (size 0))

def pointerStored (pointerSlot : Address) (state : State) : Except Fault State → Preparation
  | .error fault => .fault fault state
  | .ok after => indexAllocated pointerSlot after (allocate after usize)

def pointerAllocated (address : Address) (state : State) : Except Fault (Value × State) → Preparation
  | .error fault => .fault fault state
  | .ok (pointer, after) => pointerStored ⟨state.nextId, 0⟩ after (store after pointer (buffer address))

/-- Checked setup effects. The readonly cast in AIR has no effect and is
justified by the successful saved-pointer write; allocations can fail. -/
def prepare (state : State) (address : Address) : Preparation :=
  pointerAllocated address state (allocate state (.pointer true true word))

def preparedOutcome (length : Nat) (value : Scalar.Value) (address : Address) :
    Preparation → Control.Outcome Value Fault State
  | .fault reason after => .fault reason after
  | .ready _ indexSlot after => outcome (effects address indexSlot value length 0 after)

def loopCode : Control.Code Ty Prim Ref true :=
  (GeneratedMemory.fn_fill.body.block? 8).getD (.ret unitRef)
def indexStoreCode : Control.Code Ty Prim Ref true :=
  .bind 7 (.scalar .unit) (.store (.local 6) (.constant (size 0))) loopCode
def indexAllocateCode : Control.Code Ty Prim Ref true :=
  .bind 6 (.pointer true false usize) (.alloc usize) indexStoreCode
def savedCastCode : Control.Code Ty Prim Ref true :=
  .bind 5 (.pointer false false (.pointer true true word))
    (.pointerCast (.pointer false false (.pointer true true word)) (.local 3)) indexAllocateCode
def pointerStoreCode : Control.Code Ty Prim Ref true :=
  .bind 4 (.scalar .unit) (.store (.local 3) (.local 0)) savedCastCode
def pointerAllocateCode : Control.Code Ty Prim Ref true :=
  .bind 3 (.pointer true false (.pointer true true word)) (.alloc (.pointer true true word)) pointerStoreCode
def prologue : Control.Code Ty Prim Ref true :=
  .bind 0 (.pointer true true word) (.argument 0)
    (.bind 1 usize (.argument 1) (.bind 2 word (.argument 2) pointerAllocateCode))

theorem generated_prologue : GeneratedMemory.fn_fill.body = prologue := by rfl

private theorem localRead (env : Env) (id : Nat) (value : Value)
    (found : env id = some value) (valid : value.valid = true) :
    (Ref.local id).eval env = .ok value := by
  simp only [Ref.eval_local, found, if_pos valid]

theorem index_store_steps (length : Nat) (value : Scalar.Value) (address pointerSlot indexSlot : Address)
    (args : List Value) (env : Env) (state : State)
    (locals : Locals env length value pointerSlot indexSlot)
    (bound : length < addressLimit) (typed : (Value.scalar value).hasType word = true)
    (readPointer : load state (saved pointerSlot) = .ok (buffer address))
    (indexApart : indexSlot.allocation ≠ address.allocation)
    (pointerApart : pointerSlot.allocation ≠ address.allocation)
    (slotsApart : pointerSlot.allocation ≠ indexSlot.allocation) :
    Steps semantics args (.suspended ⟨indexStoreCode, env, state, []⟩)
      (.finished (preparedOutcome length value address
        (indexStored pointerSlot indexSlot state (store state (counter indexSlot) (size 0))))) := by
  have refIndex := localRead env 6 (counter indexSlot) locals.2.2.2 rfl
  have refZero : (Ref.constant (size 0)).eval env = .ok (size 0) := rfl
  cases written : store state (counter indexSlot) (size 0) with
  | error reason =>
    exact Steps.bind_fault semantics args
      (Prim.eval_store_fault _ _ args env state _ _ reason refIndex refZero written)
  | ok after =>
    apply Steps.bind_ok semantics args
      (Prim.eval_store_ok _ _ args env state after _ _ refIndex refZero written) (by rfl)
    have live : Locals (env.set 7 (.scalar .unit)) length value pointerSlot indexSlot := by
      simpa [Locals, Control.Env.set] using locals
    have kept := load_other_after_store state true false usize indexSlot (size 0) after
      false false (.pointer true true word) pointerSlot written slotsApart
    exact initialized_fill_steps length args _ after value address pointerSlot indexSlot [] live bound typed
      (load_after_store state (counter indexSlot) (size 0) after written) (kept.trans readPointer)
      indexApart pointerApart slotsApart

theorem index_allocate_steps (length : Nat) (value : Scalar.Value) (address pointerSlot : Address)
    (args : List Value) (env : Env) (state : State)
    (h1 : env 1 = some (size length)) (h2 : env 2 = some (.scalar value))
    (h5 : env 5 = some (saved pointerSlot))
    (bound : length < addressLimit) (typed : (Value.scalar value).hasType word = true)
    (readPointer : load state (saved pointerSlot) = .ok (buffer address))
    (fresh : pointerSlot.allocation < state.nextId) (older : address.allocation < pointerSlot.allocation) :
    Steps semantics args (.suspended ⟨indexAllocateCode, env, state, []⟩)
      (.finished (preparedOutcome length value address (indexAllocated pointerSlot state (allocate state usize)))) := by
  cases allocated : allocate state usize with
  | error reason => exact Steps.bind_fault semantics args (Prim.eval_alloc_fault usize args env state reason allocated)
  | ok pair =>
    rcases pair with ⟨pointer, after⟩
    obtain ⟨rfl, _⟩ := allocate_pointer state usize pointer after allocated
    apply Steps.bind_ok semantics args (Prim.eval_alloc_ok usize args env state after _ allocated) (by rfl)
    have locals : Locals (env.set 6 (counter ⟨state.nextId, 0⟩)) length value pointerSlot ⟨state.nextId, 0⟩ := by
      simp [Locals, Control.Env.set, h1, h2, h5]
    have kept := load_after_allocate state usize _ after false false (.pointer true true word) pointerSlot allocated (by omega)
    exact index_store_steps length value address pointerSlot ⟨state.nextId, 0⟩ args _ after
      locals bound typed (kept.trans readPointer) (by dsimp; omega) (by omega) (by dsimp; omega)

def savedWritable (pointerSlot : Address) : Value := .pointer (.pointer true false (.pointer true true word)) pointerSlot

theorem saved_cast_steps (length : Nat) (value : Scalar.Value) (address pointerSlot : Address)
    (args : List Value) (env : Env) (state : State)
    (h1 : env 1 = some (size length)) (h2 : env 2 = some (.scalar value))
    (h3 : env 3 = some (savedWritable pointerSlot))
    (bound : length < addressLimit) (typed : (Value.scalar value).hasType word = true)
    (readPointer : load state (saved pointerSlot) = .ok (buffer address))
    (fresh : pointerSlot.allocation < state.nextId) (older : address.allocation < pointerSlot.allocation) :
    Steps semantics args (.suspended ⟨savedCastCode, env, state, []⟩)
      (.finished (preparedOutcome length value address (indexAllocated pointerSlot state (allocate state usize)))) := by
  have cast := pointerCast_readonly_of_load state true false (.pointer true true word) pointerSlot
    (buffer address) readPointer
  have evaluated : (Prim.pointerCast (.pointer false false (.pointer true true word)) (.local 3)).eval args env state =
      (.ok (saved pointerSlot), state) := by
    rw [Prim.eval_cast, localRead env 3 (savedWritable pointerSlot) h3 rfl]
    simpa only [bind, Except.bind] using congrArg (fun result => (result, state)) cast
  apply Steps.bind_ok semantics args evaluated (by rfl)
  exact index_allocate_steps length value address pointerSlot args _ state
    (by simp [Control.Env.set, h1]) (by simp [Control.Env.set, h2]) (by simp [Control.Env.set])
    bound typed readPointer fresh older

theorem pointer_store_steps (length : Nat) (value : Scalar.Value) (address pointerSlot : Address)
    (args : List Value) (env : Env) (state : State)
    (h0 : env 0 = some (buffer address)) (h1 : env 1 = some (size length))
    (h2 : env 2 = some (.scalar value)) (h3 : env 3 = some (savedWritable pointerSlot))
    (bound : length < addressLimit) (typed : (Value.scalar value).hasType word = true)
    (fresh : pointerSlot.allocation < state.nextId) (older : address.allocation < pointerSlot.allocation) :
    Steps semantics args (.suspended ⟨pointerStoreCode, env, state, []⟩)
      (.finished (preparedOutcome length value address
        (pointerStored pointerSlot state (store state (savedWritable pointerSlot) (buffer address))))) := by
  have refPointer := localRead env 3 (savedWritable pointerSlot) h3 rfl
  have refBuffer := localRead env 0 (buffer address) h0 rfl
  cases written : store state (savedWritable pointerSlot) (buffer address) with
  | error reason =>
    exact Steps.bind_fault semantics args
      (Prim.eval_store_fault _ _ args env state _ _ reason refPointer refBuffer written)
  | ok after =>
    apply Steps.bind_ok semantics args
      (Prim.eval_store_ok _ _ args env state after _ _ refPointer refBuffer written) (by rfl)
    have same := (store_keeps_counters state _ _ after written).1
    have readPointer := load_alias_after_store state true false (.pointer true true word) pointerSlot
      (buffer address) after false false written
    exact saved_cast_steps length value address pointerSlot args _ after
      (by simp [Control.Env.set, h1]) (by simp [Control.Env.set, h2]) (by simp [Control.Env.set, h3])
      bound typed readPointer (by omega) older

theorem pointer_allocate_steps (length : Nat) (value : Scalar.Value) (address : Address)
    (args : List Value) (env : Env) (state : State)
    (h0 : env 0 = some (buffer address)) (h1 : env 1 = some (size length)) (h2 : env 2 = some (.scalar value))
    (bound : length < addressLimit) (typed : (Value.scalar value).hasType word = true)
    (older : address.allocation < state.nextId) :
    Steps semantics args (.suspended ⟨pointerAllocateCode, env, state, []⟩)
      (.finished (preparedOutcome length value address (prepare state address))) := by
  cases allocated : allocate state (.pointer true true word) with
  | error reason =>
    simp only [prepare, allocated, pointerAllocated, preparedOutcome]
    exact Steps.bind_fault semantics args (Prim.eval_alloc_fault _ args env state reason allocated)
  | ok pair =>
    rcases pair with ⟨pointer, after⟩
    obtain ⟨rfl, nextId⟩ := allocate_pointer state (.pointer true true word) pointer after allocated
    simp only [prepare, allocated, pointerAllocated]
    apply Steps.bind_ok semantics args (Prim.eval_alloc_ok _ args env state after _ allocated) (by rfl)
    exact pointer_store_steps length value address ⟨state.nextId, 0⟩ args _ after
      (by simp [Control.Env.set, h0]) (by simp [Control.Env.set, h1]) (by simp [Control.Env.set, h2])
      (by simp [Control.Env.set, savedWritable]) bound typed (by dsimp; omega) older

def arguments (length : Nat) (value : Scalar.Value) (address : Address) : List Value :=
  [buffer address, size length, .scalar value]

/-- Complete captured-body execution. The buffer lifetime predates the call's
scratch allocations; it need not still be live or have enough space. -/
theorem fill_body_steps (length : Nat) (value : Scalar.Value) (address : Address) (state : State)
    (bound : length < addressLimit) (typed : (Value.scalar value).hasType word = true)
    (older : address.allocation < state.nextId) :
    Steps semantics (arguments length value address)
      (.suspended ⟨GeneratedMemory.fn_fill.body, fun _ => none, state, []⟩)
      (.finished (preparedOutcome length value address (prepare state address))) := by
  rw [generated_prologue]
  have arg0 (env : Env) : (Prim.argument 0).eval (arguments length value address) env state =
      (.ok (buffer address), state) := by rw [Prim.eval_argument]; rfl
  have arg1 (env : Env) : (Prim.argument 1).eval (arguments length value address) env state =
      (.ok (size length), state) := by rw [Prim.eval_argument]; rfl
  have arg2 (env : Env) : (Prim.argument 2).eval (arguments length value address) env state =
      (.ok (.scalar value), state) := by rw [Prim.eval_argument]; rfl
  let empty : Env := fun _ => none
  let first := empty.set 0 (buffer address)
  let second := first.set 1 (size length)
  have sizeTyped : semantics.hasType (size length) usize = true := by
    simpa only [semantics] using size_typed length bound
  apply Steps.bind_ok semantics (arguments length value address) (prim := .argument 0) (value := buffer address) (arg0 empty) (by rfl)
  apply Steps.bind_ok semantics (arguments length value address) (prim := .argument 1) (value := size length) (type := usize) (arg1 first) sizeTyped
  apply Steps.bind_ok semantics (arguments length value address) (prim := .argument 2) (value := .scalar value) (type := word) (arg2 second) typed
  exact pointer_allocate_steps length value address _ _ state
    (by simp [Control.Env.set]) (by simp [Control.Env.set]) (by simp [Control.Env.set]) bound typed older

end Compiler.ZigAir.MemoryFill
