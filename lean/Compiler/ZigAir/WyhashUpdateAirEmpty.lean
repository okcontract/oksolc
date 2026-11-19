/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirComplete

namespace Compiler.ZigAir.WyhashUpdateAir
open Memory AggregateAir Compiler.Extraction Control.Machine

def emptyArguments (id : Nat) : List Register := [.value (selfPointer id), .emptyBytes]

/-- The current aggregate adapter cannot store its anonymous empty byte literal
in a native slice slot. Expose that rejection, including possible earlier OOM
and exact cleanup; do not replace the literal with an invented pointer. -/
theorem empty_literal (state : State) (id : Nat) (valid : state.valid = true) :
    ∃ fuel result after, GeneratedWyhashUpdate.update.runFuel fuel (emptyArguments id) state = .finished result after ∧
      after.valid = true ∧ after.heap = state.heap ∧ StackFrame state after ∧
      (result = .error .outOfMemory ∨ result = .error .unsupported) := by
  let args := emptyArguments id
  let e0 : Env := Control.Env.set (fun _ => none) 0 (.value (selfPointer id))
  let e1 := e0.set 1 .emptyBytes
  have checked : (state.valid && decide (args.length = GeneratedWyhashUpdate.update.parameters.length) &&
      (args.zip GeneratedWyhashUpdate.update.parameters).all (fun (value, type) => value.hasType type)) = true := by
    change (state.valid && true && (true && (true && true))) = true
    simp only [valid, Bool.and_self]
  have head : Steps AggregateCall.semantics args
      (.suspended ⟨GeneratedWyhashUpdate.update.body, fun _ => none, state, []⟩)
      (.suspended ⟨remaining 2, e1, state, []⟩) := by
    apply AggregateCall.primitive_steps args
    · rfl
    · rfl
    · apply AggregateCall.primitive_steps args
      · rfl
      · rfl
      · exact .refl _
  obtain ⟨middle, firstStack, failed | ⟨saved, _, _, _, _⟩⟩ :=
    AggregateCall.ReadonlyParameter.steps 2 0 (by decide) (selfPointer id) ⟨8, 8⟩ rfl rfl (by decide)
      (remaining 5) [] state valid args e1 (by simp [e1, e0, Control.Env.set])
  · obtain ⟨fuel, ran⟩ := GeneratedWyhashUpdate.update.run_of_steps args state (.fault .outOfMemory middle) checked
      (head.trans AggregateCall.semantics args failed)
    exact ⟨fuel, .error .outOfMemory, cleanup state.nextId middle, ran, firstStack.cleanup_valid,
      firstStack.cleanup_heap, firstStack.cleaned, Or.inl rfl⟩
  · let e4 := AggregateCall.ReadonlyParameter.resultEnv e1 2 state.nextId (.pointer true false objectType)
    have emptyFound : e4 1 = some .emptyBytes := by simp [e4, AggregateCall.ReadonlyParameter.resultEnv, e1, Control.Env.set]
    cases allocated : Memory.allocate middle inputType with
    | error fault =>
      have faultEq := StackFrame.allocation_fault middle inputType ⟨16, 8⟩ fault firstStack.valid rfl allocated
      subst fault
      have p5 : (AggregateCall.Prim.primitive (.memory (.alloc inputType))).eval args e4 middle =
          (.error .outOfMemory, middle) := by
        simp only [AggregateCall.Prim.eval, AggregateAir.Prim.eval, AggregateAir.Prim.transition,
          MemoryAir.Prim.transition, allocated, bind, Except.bind]
      have failure : Steps AggregateCall.semantics args (.suspended ⟨remaining 5, e4, middle, []⟩)
          (.finished (.fault .outOfMemory middle)) := Steps.bind_fault AggregateCall.semantics args p5
      obtain ⟨fuel, ran⟩ := GeneratedWyhashUpdate.update.run_of_steps args state (.fault .outOfMemory middle) checked
        (head.trans AggregateCall.semantics args (saved.trans AggregateCall.semantics args failure))
      exact ⟨fuel, .error .outOfMemory, cleanup state.nextId middle, ran, firstStack.cleanup_valid,
        firstStack.cleanup_heap, firstStack.cleaned, Or.inl rfl⟩
    | ok pair =>
      obtain ⟨pointer, after⟩ := pair
      have pointerEq := (allocate_pointer middle inputType pointer after allocated).1
      rw [pointerEq] at allocated
      let e5 := e4.set 5 (.value (slot true inputType middle.nextId))
      have p5 := eval_alloc inputType args e4 middle after _ allocated
      have pointerRead := value_local e5 5 (slot true inputType middle.nextId) (by simp [e5, Control.Env.set]) rfl
      have emptyRead := ref_local e5 1 .emptyBytes (by simp [e5, Control.Env.set, emptyFound]) rfl
      have p6 : (AggregateCall.Prim.primitive (.store (.local 5) (.local 1))).eval args e5 after =
          (.error .unsupported, after) := by
        simp only [AggregateCall.Prim.eval, AggregateAir.Prim.eval, AggregateAir.Prim.transition,
          pointerRead, emptyRead, AggregateAir.store, bind, Except.bind]
      have failure : Steps AggregateCall.semantics args (.suspended ⟨remaining 5, e4, middle, []⟩)
          (.finished (.fault .unsupported after)) :=
        AggregateCall.primitive_steps args p5 (pointer_typed _ _)
          (Steps.bind_fault AggregateCall.semantics args p6)
      have frame := firstStack.allocate inputType _ after allocated
      obtain ⟨fuel, ran⟩ := GeneratedWyhashUpdate.update.run_of_steps args state (.fault .unsupported after) checked
        (head.trans AggregateCall.semantics args (saved.trans AggregateCall.semantics args failure))
      exact ⟨fuel, .error .unsupported, cleanup state.nextId after, ran, frame.cleanup_valid, frame.cleanup_heap, frame.cleaned, Or.inr rfl⟩

end Compiler.ZigAir.WyhashUpdateAir
