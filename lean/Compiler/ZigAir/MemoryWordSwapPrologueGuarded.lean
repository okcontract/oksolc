/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryWordSwapLoopGuarded

namespace Compiler.ZigAir.MemoryWordSwap
open Memory MemoryAir Control.Machine
open Memory.WordArray (View Writable Represents word)
open MemoryFill (size counter)

theorem bytes_guarded (args : List Value) (env : Env) (state : State) (view : View) (index argument raw sliceId : Nat)
    (next : Control.Code Ty Prim Ref true) (left right : Nat) (slot : Address)
    (initial : state.valid = true) (cap : Writable state view) (inside : index < view.length)
    (source : env argument = some (view.pointer index)) :
    GuardedSteps semantics args (Footprint view left right slot) (.suspended ⟨bytesCode argument raw sliceId next, env, state, []⟩)
      (.suspended ⟨next, bytesEnv env raw sliceId (view.address index), state, []⟩) := by
  have cast := ByteAccess.cast_array state view index 4 true true initial cap inside (Or.inr (Or.inr rfl))
  have castEval : (Prim.wordByteCast true true 4 (.local argument)).eval args env state =
      (.ok (ByteAccess.pointer true true (view.address index)), state) := by
    simp only [Prim.eval_word_byte_cast, Ref.eval_local, source, View.pointer, Value.valid, ↓reduceIte, bind, Except.bind]
    exact congrArg (fun result => (result, state)) cast
  have slicing := ByteAccess.make_byte_slice state view index true initial cap inside
  have sliceEval : (Prim.slice (.slice true ByteAccess.byte) (.local raw) (.constant (size 4))).eval args
      (env.set raw (ByteAccess.pointer true true (view.address index))) state =
      (.ok (ByteAccess.slice true (view.address index)), state) := by
    have four : ∀ env, (Ref.constant (size 4)).natural env = .ok 4 := fun _ => rfl
    simp only [Prim.eval_slice, Ref.eval_local, Control.Env.set, ↓reduceIte,
      MemoryByteInvocation.byte_pointer_valid, four, bind, Except.bind, slicing]
  apply GuardedSteps.bind_ok semantics args (Footprint view left right slot) (by trivial) castEval (by rfl)
  apply GuardedSteps.bind_ok semantics args (Footprint view left right slot) (by trivial) sliceEval (by rfl)
  exact .refl _

theorem access_guarded (caller : State) (view : View) (left right : Nat)
    (initial : caller.valid = true) (cap : Writable caller view) (hl : left < view.length) (hr : right < view.length) :
    GuardedSteps semantics (arguments view left right) (Footprint view left right ⟨caller.nextId, 0⟩)
      (.suspended ⟨GeneratedMemory.fn_swap_u32.program.body, fun _ => none, caller, []⟩)
      (.suspended ⟨allocatedCode, accessEnv view left right, caller, []⟩) := by
  rw [generated_prologue]
  have first : (Prim.argument 0).eval (arguments view left right) (fun _ => none) caller = (.ok (view.pointer left), caller) := rfl
  apply GuardedSteps.bind_ok semantics (arguments view left right) (Footprint view left right ⟨caller.nextId, 0⟩)
    (prim := .argument 0) (env := fun _ => none) (state := caller) (value := view.pointer left) (by trivial) first (by rfl)
  have second : (Prim.argument 1).eval (arguments view left right)
      (Control.Env.set (fun _ => none) 0 (view.pointer left)) caller = (.ok (view.pointer right), caller) := rfl
  apply GuardedSteps.bind_ok semantics (arguments view left right) (Footprint view left right ⟨caller.nextId, 0⟩)
    (prim := .argument 1) (env := Control.Env.set (fun _ => none) 0 (view.pointer left)) (state := caller)
    (value := view.pointer right) (by trivial) second (by rfl)
  exact (bytes_guarded (arguments view left right) (sourceEnv view left right) caller view left 0 3 4
    (bytesCode 1 5 6 allocatedCode) left right ⟨caller.nextId, 0⟩ initial cap hl (by simp [sourceEnv, Control.Env.set])).trans semantics _ _
    (bytes_guarded _ _ caller view right 1 5 6 allocatedCode left right ⟨caller.nextId, 0⟩ initial cap hr
      (by simp [bytesEnv, sourceEnv, Control.Env.set]))

theorem stored_guarded (caller allocated : State) (view : View) (left right base : Nat)
    (written : store allocated (counter ⟨caller.nextId, 0⟩) (size 0) = .ok (withCounter base 0 caller)) :
    GuardedSteps semantics (arguments view left right) (Footprint view left right ⟨caller.nextId, 0⟩)
      (.suspended ⟨storedCode, allocatedEnv view left right caller.nextId, allocated, []⟩)
      (.suspended ⟨entry, storedEnv view left right caller.nextId, withCounter base 0 caller, []⟩) := by
  have pointer : (Ref.local 7).eval (allocatedEnv view left right caller.nextId) = .ok (counter ⟨caller.nextId, 0⟩) := rfl
  have zero : (Ref.constant (size 0)).eval (allocatedEnv view left right caller.nextId) = .ok (size 0) := rfl
  have storeEval : semantics.evalPrim (.store (.local 7) (.constant (size 0))) (arguments view left right)
      (allocatedEnv view left right caller.nextId) allocated = (.ok (.scalar .unit), withCounter base 0 caller) := by
    simpa only [semantics] using Prim.eval_store_ok _ _ _ _ _ _ _ _ pointer zero written
  have unitTyped : semantics.hasType (.scalar .unit) (.scalar .unit) = true := rfl
  apply GuardedSteps.bind_ok semantics (arguments view left right) (Footprint view left right ⟨caller.nextId, 0⟩)
    (prim := .store (.local 7) (.constant (size 0))) (env := allocatedEnv view left right caller.nextId)
    pointer storeEval unitTyped
  have leftLength : (Prim.sliceLen (.local 4)).eval (arguments view left right)
      ((allocatedEnv view left right caller.nextId).set 8 (.scalar .unit)) (withCounter base 0 caller) = (.ok (size 4), withCounter base 0 caller) := rfl
  apply GuardedSteps.bind_ok semantics (arguments view left right) (Footprint view left right ⟨caller.nextId, 0⟩)
    (prim := .sliceLen (.local 4)) (env := (allocatedEnv view left right caller.nextId).set 8 (.scalar .unit))
    (state := withCounter base 0 caller) (value := size 4) (by trivial) leftLength (by rfl)
  have rightLength : (Prim.sliceLen (.local 6)).eval (arguments view left right)
      (((allocatedEnv view left right caller.nextId).set 8 (.scalar .unit)).set 9 (size 4)) (withCounter base 0 caller) =
      (.ok (size 4), withCounter base 0 caller) := rfl
  apply GuardedSteps.bind_ok semantics (arguments view left right) (Footprint view left right ⟨caller.nextId, 0⟩)
    (prim := .sliceLen (.local 6)) (env := ((allocatedEnv view left right caller.nextId).set 8 (.scalar .unit)).set 9 (size 4))
    (state := withCounter base 0 caller) (value := size 4) (by trivial) rightLength (by rfl)
  exact .refl _

/-- A checked terminal path exists, including allocation exhaustion. No supplied
fuel, complete-run equation or successful intermediate access is assumed. -/
theorem body_guarded (caller : State) (view : View) (items : List (BitVec 32)) (left right : Nat)
    (initial : caller.valid = true) (cap : Writable caller view) (represented : Represents caller view items)
    (hl : left < items.length) (hr : right < items.length) (apart : left ≠ right) :
    ∃ outcome, GuardedSteps semantics (arguments view left right) (Footprint view left right ⟨caller.nextId, 0⟩)
      (.suspended ⟨GeneratedMemory.fn_swap_u32.program.body, fun _ => none, caller, []⟩) (.finished outcome) := by
  have first := access_guarded caller view left right initial cap
    (by simpa only [represented.1] using hl) (by simpa only [represented.1] using hr)
  cases allocation : allocate caller usize with
  | error reason =>
    have same := allocate_fault_of_layout caller usize ⟨8, 8⟩ reason initial rfl allocation
    subst reason
    refine ⟨.fault .outOfMemory caller, first.trans semantics _ _ ?_⟩
    exact GuardedSteps.bind_fault semantics _ _ ⟨rfl, rfl⟩ (Prim.eval_alloc_fault usize _ _ caller .outOfMemory allocation)
  | ok pair =>
    obtain ⟨pointer, allocated⟩ := pair
    obtain ⟨base, pointerEq, written, live⟩ := initialize_counter caller allocated pointer initial allocation
    obtain ⟨after, loop⟩ := initialized_guarded (arguments view left right) (storedEnv view left right caller.nextId) caller base
      view items left right initial live cap represented hl hr apart (stored_locals view left right caller.nextId)
    refine ⟨.returned (.scalar .unit) (withCounter base 4 after), first.trans semantics _ _ ?_⟩
    rw [pointerEq] at allocation written
    apply GuardedSteps.bind_ok semantics _ _ ⟨rfl, rfl⟩ (Prim.eval_alloc_ok usize _ _ caller allocated _ allocation) (by rfl)
    exact (stored_guarded caller allocated view left right base written).trans semantics _ _ loop

end Compiler.ZigAir.MemoryWordSwap
