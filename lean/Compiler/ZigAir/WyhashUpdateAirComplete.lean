/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirCompleteSteps

namespace Compiler.ZigAir.WyhashUpdateAir
open Memory AggregateAir Compiler.Extraction Control.Machine

/-- Parameter allocation can fail before the counter changes. All later
allocation failures retain the counter and the reached long-update writes. -/
def Interrupted (source : Cells) (view : ByteSlice.View) (total length : Nat) (cells failed : Cells) : Prop :=
  failed = cells ∨ Long.Interrupted source view length
    (cells.set 40 (WyhashLocal.word (BitVec.ofNat 64 (total + view.length)))) failed

/-- Complete captured native update for every admitted input. Success consumes
the existing update invariant; OOM retains its actual write prefix. Invocation
cleanup retires only the locals, preserving both the hasher and caller storage. -/
theorem invocation {state : State} {id : Nat} (frame : CellFrame state id)
    (valid : state.valid = true) (typed : frame.cell.type = objectType)
    (address : Address) (source : Cells) (view : ByteSlice.View) (bytes : Nat → BitVec 8)
    (geometry : ByteSlice.Geometry view) (represented : ByteSlice.Represents source view bytes)
    (reads : ByteRange.Reads state address view.length bytes) (apart : address.allocation ≠ id)
    (total length : Nat) (invariant : WyhashUpdate.Invariant frame.cell.cells total length)
    (sumBound : total + view.length < addressLimit) (budget : view.length + 48 < addressLimit) :
    ∃ fuel result after,
      GeneratedWyhashUpdate.update.runFuel fuel (arguments id address view.length) state = .finished result after ∧
      after.valid = true ∧
      ((result = .error .outOfMemory ∧ ∃ failedCells, Interrupted source view total length frame.cell.cells failedCells ∧
        after.heap = (frame.install failedCells).heap ∧ failedCells.valid objectType = true ∧
        StackFrame (frame.install failedCells) after) ∨
       ∃ cells buffered, result = .ok (.value (.scalar .unit)) ∧ after.heap = (frame.install cells).heap ∧
        WyhashUpdate.update source view frame.cell.cells = .ok cells ∧
        WyhashUpdate.Invariant cells (total + view.length) buffered ∧ StackFrame (frame.install cells) after) := by
  by_cases fits : view.length ≤ 48 - length
  · obtain ⟨fuel, result, after, ran, afterValid, ⟨failed, heap, failedStack⟩ | succeeded⟩ :=
      buffered_invocation_framed frame valid typed address source view bytes geometry represented reads apart total length invariant fits sumBound
    · exact ⟨fuel, result, after, ran, afterValid, Or.inl ⟨failed, frame.cell.cells, Or.inl rfl,
        by simpa only [frame.install_current valid] using heap, invariant.core.valid,
        by simpa only [frame.install_current valid] using failedStack⟩⟩
    · exact ⟨fuel, result, after, ran, afterValid, Or.inr succeeded⟩
  · have countBound : view.length < addressLimit := by omega
    have checked : (state.valid && decide ((arguments id address view.length).length =
        GeneratedWyhashUpdate.update.parameters.length) &&
        ((arguments id address view.length).zip GeneratedWyhashUpdate.update.parameters).all
          (fun (value, type) => value.hasType type)) = true := by
      have sliceTyped : (Register.value (.slice inputType address view.length)).hasType inputType = true := by
        change decide (view.length < addressLimit) = true
        exact decide_eq_true countBound
      change (state.valid && true && (true &&
        ((Register.value (.slice inputType address view.length)).hasType inputType && true))) = true
      simp only [valid, sliceTyped, Bool.and_self]
    obtain ⟨prepared, stack, failed | ⟨entry, strict, selfRead, countRead, inputRead⟩⟩ :=
      parameters_with_input state id address view.length valid countBound
    · obtain ⟨fuel, ran⟩ := GeneratedWyhashUpdate.update.run_of_steps (arguments id address view.length) state
        (.fault .outOfMemory prepared) checked failed
      exact ⟨fuel, .error .outOfMemory, cleanup state.nextId prepared, ran, stack.cleanup_valid,
        Or.inl ⟨rfl, frame.cell.cells, Or.inl rfl,
          by simpa only [frame.install_current valid] using stack.cleanup_heap, invariant.core.valid,
          by simpa only [frame.install_current valid] using stack.cleaned⟩⟩
    · let borrowed := frame.extend stack
      have old : id < state.nextId := (valid_lookup state id frame.cell valid frame.found).1
      have bound := end_bound borrowed stack.valid typed strict
      obtain ⟨reached, ⟨failedCells, failure, failedCore, failedStack, failedPath⟩ |
          ⟨cells, buffered, model, preserved, finalStack, finalPath⟩⟩ :=
        long_steps borrowed stack.valid typed bound address source frame.cell.cells view bytes geometry represented
          (reads.extend stack) apart total length state.nextId (state.nextId + 1) invariant (by omega) sumBound budget
          (by omega) (by omega) selfRead inputRead countRead (arguments id address view.length)
          (parameterEnv id address view.length state.nextId (state.nextId + 1)) []
          (by simp [parameterEnv, Control.Env.set]) (by simp [parameterEnv, Control.Env.set])
      · have combined := (stack.install_old frame failedCells (typed ▸ failedCore.valid)).trans failedStack
        have same : borrowed.install frame.cell.cells = prepared := borrowed.install_current stack.valid
        rw [same] at failedPath
        obtain ⟨fuel, ran⟩ := GeneratedWyhashUpdate.update.run_of_steps (arguments id address view.length) state
          (.fault .outOfMemory reached) checked (entry.trans AggregateCall.semantics (arguments id address view.length) failedPath)
        exact ⟨fuel, .error .outOfMemory, cleanup state.nextId reached, ran, combined.cleanup_valid,
          Or.inl ⟨rfl, failedCells, Or.inr failure, combined.cleanup_heap, failedCore.valid, combined.cleaned⟩⟩
      · have combined := (stack.install_old frame cells (typed ▸ preserved.core.valid)).trans finalStack
        have same : borrowed.install frame.cell.cells = prepared := borrowed.install_current stack.valid
        rw [same] at finalPath
        obtain ⟨fuel, ran⟩ := GeneratedWyhashUpdate.update.run_of_steps (arguments id address view.length) state
          (.returned (.value (.scalar .unit)) reached) checked
          (entry.trans AggregateCall.semantics (arguments id address view.length) finalPath)
        exact ⟨fuel, .ok (.value (.scalar .unit)), cleanup state.nextId reached, ran, combined.cleanup_valid,
          Or.inr ⟨cells, buffered, rfl, combined.cleanup_heap, model, preserved, combined.cleaned⟩⟩

end Compiler.ZigAir.WyhashUpdateAir
