/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.AggregateExecutionProofs
import Compiler.ZigAir.ControlProjection

namespace Compiler.ZigAir.AggregateCall.ReadonlyParameter
open Memory AggregateAir Control.Machine

abbrev Code := Control.Code Ty AggregateCall.Prim Ref true
abbrev slot (writable : Bool) (type : Ty) (id : Nat) : Value :=
  .pointer (.pointer writable false type) ⟨id, 0⟩

def code (base source : Nat) (type : Ty) (next : Code) : Code :=
  .bind base (.pointer true false type) (.primitive (.memory (.alloc type))) $
  .bind (base + 1) (.scalar .unit) (.primitive (.store (.local base) (.local source))) $
  .bind (base + 2) (.pointer false false type)
    (.primitive (.memory (.pointerCast (.pointer false false type) (.local base)))) next

def resultEnv (env : Env) (base id : Nat) (type : Ty) : Env :=
  let env := env.set base (.value (slot true type id))
  let env := env.set (base + 1) (.value (.scalar .unit))
  env.set (base + 2) (.value (slot false type id))

theorem before (env : Env) (base id query : Nat) (type : Ty) (earlier : query < base) :
    resultEnv env base id type query = env query := by
  simp (disch := omega) only [resultEnv, Control.Env.set, if_neg]

theorem cast (state : State) (type : Ty) (id reg : Nat) (value : Value)
    (read : Memory.load state (slot true type id) = .ok value)
    (args : List Register) (env : Env) (found : env reg = some (.value (slot true type id))) :
    (AggregateAir.Prim.memory (.pointerCast (.pointer false false type) (.local reg))).eval args env state =
      (.ok (.value (slot false type id)), state) := by
  apply eval_memory
  have data : (MemoryAir.Ref.local reg).eval (values env) = .ok (slot true type id) := by
    rw [MemoryAir.Ref.eval_local]
    simp only [values, found, Value.valid, ↓reduceIte]
  have changed := pointerCast_readonly_of_load state true false type ⟨id, 0⟩ value read
  simp only [MemoryAir.Prim.eval, MemoryAir.Prim.transition, data, changed, bind, Except.bind]

/-- A native save and read-only borrow, with actual allocation failure and
readback. Both update entry parameters and round parameters use this sequence. -/
theorem steps (base source : Nat) (earlier : source < base) (value : Value) (layout : Layout)
    (validValue : value.valid = true) (shaped : value.type.layout = some layout) (positive : 0 < layout.bytes)
    (next : Code) (frames : List (Frame Ty AggregateCall.Prim Ref))
    (state : State) (valid : state.valid = true) (args : List Register) (env : Env)
    (found : env source = some (.value value)) :
    ∃ after, StackFrame state after ∧
      (Steps AggregateCall.semantics args (.suspended ⟨code base source value.type next, env, state, frames⟩)
        (.finished (.fault .outOfMemory after)) ∨
       Steps AggregateCall.semantics args (.suspended ⟨code base source value.type next, env, state, frames⟩)
        (.suspended ⟨next, resultEnv env base state.nextId value.type, after, frames⟩) ∧
       Memory.load after (slot false value.type state.nextId) = .ok value ∧
       (after.heap.lookup state.nextId).map Allocation.type = some value.type ∧
       after.nextId = state.nextId + 1 ∧ after.nextAddress < addressLimit) := by
  let tail := (code base source value.type next).dropBindings 2
  have head := AggregateCall.save_steps value (.local source) base (base + 1) tail frames args env state
    (ref_local _ _ _ (by simpa [Control.Env.set, show source ≠ base by omega] using found) validValue)
  obtain ⟨result, after, ran, stack, failed | ⟨success, read, owner⟩⟩ :=
    SavedValue.verified state value layout valid validValue shaped positive
  · rw [failed] at ran
    rw [ran] at head
    exact ⟨after, stack, Or.inl head⟩
  · rw [success] at ran
    rw [ran] at head
    let savedEnv := (env.set base (.value (slot true value.type state.nextId))).set (base + 1) (.value (.scalar .unit))
    have changed := cast after value.type state.nextId base value read args savedEnv
      (by simp [savedEnv, Control.Env.set])
    have last : Steps AggregateCall.semantics args (.suspended ⟨tail, savedEnv, after, frames⟩)
        (.suspended ⟨next, resultEnv env base state.nextId value.type, after, frames⟩) :=
      AggregateCall.primitive_steps args changed (by
        simp [Register.hasType, Register.type, Register.valid, Value.type, Value.valid]) (.refl _)
    have cursors := SavedValue.success_cursors state after value ran
    exact ⟨after, stack, Or.inr ⟨head.trans AggregateCall.semantics args last, read, owner, cursors⟩⟩

end Compiler.ZigAir.AggregateCall.ReadonlyParameter
