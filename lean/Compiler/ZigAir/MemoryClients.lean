/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryEffects
import Compiler.ZigAir.GeneratedMemoryCells

/-! Universal clients of the heap laws, tied to regenerated captured AIR.
The store premise describes the model's checked access, not native Zig memory.
No premise assumes that the complete generated program succeeds. -/
namespace Compiler.ZigAir.MemoryClients
open Memory MemoryAir GeneratedMemory

theorem load_store_success (state after : State) (address : Address) (value : Value)
    (initial : state.valid = true) (typed : value.hasType (.scalar (.int false 32)) = true)
    (written : store state (.pointer (.pointer true false (.scalar (.int false 32))) address) value = .ok after) :
    fn_load_store.run [.pointer (.pointer true false (.scalar (.int false 32))) address, value] state =
      (.ok value, cleanup state.nextId after) := by
  have valid : value.valid = true := by
    have h := typed
    simp only [Value.hasType, Bool.and_eq_true] at h
    exact h.2
  have readback := load_after_store state _ value after written
  have pointerTyped : (Value.pointer (.pointer true false (.scalar (.int false 32))) address).hasType
      (.pointer true false (.scalar (.int false 32))) = true := rfl
  have pointerValid : (Value.pointer (.pointer true false (.scalar (.int false 32))) address).valid = true := rfl
  have unitTyped : (Value.scalar .unit).hasType (.scalar .unit) = true := rfl
  simp [fn_load_store, Program.run, Program.accepts, Program.finish, initial, typed, Control.Code.eval, semantics,
    Prim.eval, Prim.transition, Ref.eval, Control.Env.set, valid, written, readback,
    pointerTyped, pointerValid, unitTyped, bind, Except.bind]

theorem load_store_failure (state : State) (address : Address) (value : Value) (fault : Fault)
    (initial : state.valid = true) (typed : value.hasType (.scalar (.int false 32)) = true)
    (failed : store state (.pointer (.pointer true false (.scalar (.int false 32))) address) value = .error fault) :
    fn_load_store.run [.pointer (.pointer true false (.scalar (.int false 32))) address, value] state =
      (.error fault, cleanup state.nextId state) := by
  have valid : value.valid = true := by
    have h := typed
    simp only [Value.hasType, Bool.and_eq_true] at h
    exact h.2
  have pointerTyped : (Value.pointer (.pointer true false (.scalar (.int false 32))) address).hasType
      (.pointer true false (.scalar (.int false 32))) = true := rfl
  have pointerValid : (Value.pointer (.pointer true false (.scalar (.int false 32))) address).valid = true := rfl
  simp [fn_load_store, Program.run, Program.accepts, Program.finish, initial, typed, Control.Code.eval, semantics,
    Prim.eval, Prim.transition, Ref.eval, Control.Env.set, valid, failed,
    pointerTyped, pointerValid, bind, Except.bind]

/-- Complete success/failure specification on valid, typed invocation inputs. -/
theorem load_store_run (state : State) (address : Address) (value : Value)
    (initial : state.valid = true) (typed : value.hasType (.scalar (.int false 32)) = true) :
    fn_load_store.run [.pointer (.pointer true false (.scalar (.int false 32))) address, value] state =
      match store state (.pointer (.pointer true false (.scalar (.int false 32))) address) value with
      | .ok after => (.ok value, cleanup state.nextId after)
      | .error fault => (.error fault, cleanup state.nextId state) := by
  cases written : store state (.pointer (.pointer true false (.scalar (.int false 32))) address) value with
  | ok after => exact load_store_success state after address value initial typed written
  | error fault => exact load_store_failure state address value fault initial typed written

end Compiler.ZigAir.MemoryClients
