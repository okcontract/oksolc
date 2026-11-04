/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirPrefix

set_option maxRecDepth 8192

namespace Compiler.ZigAir.WyhashUpdateAir
open Memory AggregateAir Compiler.Extraction Control.Machine

/-- General refinement of the captured prefix and buffered branch. The same
cell invariant used for full-block updates and finalization is consumed here. -/
theorem buffered_steps {state : State} {id : Nat} (frame : CellFrame state id)
    (valid : state.valid = true) (typed : frame.cell.type = objectType)
    (endBound : frame.cell.base + 104 < addressLimit)
    (address : Address) (source cells : Cells) (view : ByteSlice.View) (bytes : Nat → BitVec 8)
    (geometry : ByteSlice.Geometry view) (represented : ByteSlice.Represents source view bytes)
    (reads : ByteRange.Reads state address view.length bytes) (apart : address.allocation ≠ id)
    (total length selfSlot inputSlot : Nat) (invariant : WyhashUpdate.Invariant cells total length)
    (fits : view.length ≤ 48 - length) (sumBound : total + view.length < addressLimit)
    (selfApart : selfSlot ≠ id) (inputApart : inputSlot ≠ id)
    (selfRead : Memory.load state (slot false (.pointer true false objectType) selfSlot) = .ok (selfPointer id))
    (countRead : Memory.load state (.pointer (.pointer false false usize) ⟨inputSlot, 8⟩) =
      .ok (.scalar (.int false 64 view.length)))
    (args : List Register) (env : Env) (frames : List (Frame Ty AggregateCall.Prim Ref))
    (h1 : env 1 = some (.value (.slice inputType address view.length)))
    (h4 : env 4 = some (.value (slot false (.pointer true false objectType) selfSlot)))
    (h7 : env 7 = some (.value (slot false inputType inputSlot))) :
    ∃ after buffered, Steps AggregateCall.semantics args
        (.suspended ⟨remaining 8, env, frame.install cells, frames⟩)
        (.finished (.returned (.value (.scalar .unit)) (frame.install after))) ∧
      WyhashUpdate.update source view cells = .ok after ∧
      WyhashUpdate.Invariant after (total + view.length) buffered := by
  have limit : 96 < addressLimit := by decide
  have sumWord : total + view.length < 2 ^ 64 := sumBound
  let counted := cells.set 40 (WyhashLocal.word (BitVec.ofNat 64 (total + view.length)))
  let countedEnv := counterEnv env id inputSlot total view.length
  let loaded := guardEnv countedEnv id inputSlot length view.length
  let chosen := chosenEnv loaded length view.length
  let inner := Frame.block 15 (.scalar .unit) longBody :: frames
  have countPath := counter_steps frame cells typed total view.length selfSlot inputSlot sumBound
    invariant.core.count selfApart inputApart selfRead countRead args env frames h4 h7
  have countCore : WyhashUpdate.Core counted (total + view.length) := by
    simpa only [↓reduceIte, BitVec.toNat_ofNat, Nat.mod_eq_of_lt sumWord] using
      invariant.core.store_word 40 (BitVec.ofNat 64 (total + view.length)) (by decide)
  have lengthField : counted.lookup 48 = some (WyhashLocal.word (BitVec.ofNat 64 length)) := by
    simpa only [counted, Cells.lookup_set_other _ _ _ _ (by decide : 48 ≠ 40)] using invariant.lengthField
  have loadPath := guard_loads frame counted typed length view.length selfSlot inputSlot
    (by have := invariant.bounded; omega) (by omega) lengthField selfApart inputApart selfRead countRead
    args countedEnv inner (by simp [countedEnv, counterEnv, Control.Env.set, h4])
    (by simp [countedEnv, counterEnv, Control.Env.set, h7])
  have choice := guard_choose (frame.install counted) length view.length invariant.bounded fits args loaded inner
    (by simp [loaded, guardEnv, Control.Env.set]) (by simp [loaded, guardEnv, Control.Env.set])
  obtain ⟨after, bodyRun, bodyModel⟩ := buffered_body frame valid typed endBound address source counted view bytes
    geometry represented reads apart (total + view.length) length selfSlot inputSlot countCore invariant.bounded
    fits lengthField selfApart inputApart selfRead countRead args chosen
    (by simp [chosen, chosenEnv, loaded, guardEnv, countedEnv, counterEnv, Control.Env.set, h1])
    (by simp [chosen, chosenEnv, loaded, guardEnv, countedEnv, counterEnv, Control.Env.set, h4])
    (by simp [chosen, chosenEnv, loaded, guardEnv, countedEnv, counterEnv, Control.Env.set, h7])
  have bodyPath := finite_steps AggregateCall.semantics args bufferedBody chosen (frame.install counted) inner
  rw [bodyRun] at bodyPath
  have entered : Steps AggregateCall.semantics args
      (.suspended ⟨remaining 15, countedEnv, frame.install counted, frames⟩)
      (.finished (.returned (.value (.scalar .unit)) (frame.install after))) := by
    rw [generated_guard]
    apply Steps.step
    exact loadPath.trans AggregateCall.semantics args (choice.trans AggregateCall.semantics args bodyPath)
  have model := WyhashUpdate.update_from_body source cells view total length invariant sumBound after bodyModel
  obtain ⟨expected, buffered, logical, preserved⟩ := WyhashUpdate.update_verified source cells view bytes
    geometry represented total length invariant sumBound (by omega)
  have same := Except.ok.inj (model.symm.trans logical)
  subst expected
  exact ⟨after, buffered, countPath.trans AggregateCall.semantics args entered, model, preserved⟩

/-- Complete captured invocation for updates that fit the current buffer.
Allocation failures are explicit; successful execution preserves the existing
update invariant and cleans only invocation-local allocations. -/
theorem buffered_invocation_framed {state : State} {id : Nat} (frame : CellFrame state id)
    (valid : state.valid = true) (typed : frame.cell.type = objectType)
    (address : Address) (source : Cells) (view : ByteSlice.View) (bytes : Nat → BitVec 8)
    (geometry : ByteSlice.Geometry view) (represented : ByteSlice.Represents source view bytes)
    (reads : ByteRange.Reads state address view.length bytes) (apart : address.allocation ≠ id)
    (total length : Nat) (invariant : WyhashUpdate.Invariant frame.cell.cells total length)
    (fits : view.length ≤ 48 - length) (sumBound : total + view.length < addressLimit) :
    ∃ fuel result after,
      GeneratedWyhashUpdate.update.runFuel fuel (arguments id address view.length) state =
        .finished result after ∧ after.valid = true ∧
      ((result = .error .outOfMemory ∧ after.heap = state.heap ∧ StackFrame state after) ∨
        ∃ cells buffered, result = .ok (.value (.scalar .unit)) ∧ after.heap = (frame.install cells).heap ∧
          WyhashUpdate.update source view frame.cell.cells = .ok cells ∧
          WyhashUpdate.Invariant cells (total + view.length) buffered ∧ StackFrame (frame.install cells) after) := by
  have countBound : view.length < addressLimit := by omega
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
  obtain ⟨prepared, stack, failed | ⟨entry, strict, selfRead, countRead⟩⟩ :=
    parameters state id address view.length valid countBound
  · obtain ⟨fuel, ran⟩ := GeneratedWyhashUpdate.update.run_of_steps (arguments id address view.length) state
      (.fault .outOfMemory prepared) checked failed
    exact ⟨fuel, .error .outOfMemory, cleanup state.nextId prepared, ran, stack.cleanup_valid,
      Or.inl ⟨rfl, stack.cleanup_heap, stack.cleaned⟩⟩
  · let borrowed := frame.extend stack
    have old : id < state.nextId := (valid_lookup state id frame.cell valid frame.found).1
    have extent := valid_lookup prepared id frame.cell stack.valid borrowed.found
    have shaped : frame.cell.type.layout = some ⟨104, 8⟩ := by rw [typed]; rfl
    have endBound : borrowed.cell.base + 104 < addressLimit := by
      obtain ⟨_, _, layout, shape, _, inside, _⟩ := extent
      rw [shaped] at shape
      cases Option.some.inj shape
      change frame.cell.base + 104 < addressLimit
      dsimp at inside
      omega
    obtain ⟨cells, buffered, path, model, preserved⟩ := buffered_steps borrowed stack.valid typed endBound
      address source frame.cell.cells view bytes geometry represented (reads.extend stack) apart
      total length state.nextId (state.nextId + 1) invariant fits sumBound (by omega) (by omega)
      selfRead countRead (arguments id address view.length)
      (parameterEnv id address view.length state.nextId (state.nextId + 1)) []
      (by simp [parameterEnv, Control.Env.set]) (by simp [parameterEnv, Control.Env.set])
      (by simp [parameterEnv, Control.Env.set])
    have current : borrowed.install frame.cell.cells = prepared := borrowed.install_current stack.valid
    rw [current] at path
    have complete := entry.trans AggregateCall.semantics (arguments id address view.length) path
    obtain ⟨fuel, ran⟩ := GeneratedWyhashUpdate.update.run_of_steps (arguments id address view.length) state
      (.returned (.value (.scalar .unit)) (borrowed.install cells)) checked complete
    have cellValid : cells.valid frame.cell.type = true := typed ▸ preserved.core.valid
    have clean := stack.cleanup_install frame cells cellValid
    exact ⟨fuel, .ok (.value (.scalar .unit)), cleanup state.nextId (borrowed.install cells), ran, clean.1,
      Or.inr ⟨cells, buffered, rfl, clean.2, model, preserved, (stack.install_old frame cells cellValid).cleaned⟩⟩

theorem buffered_invocation {state : State} {id : Nat} (frame : CellFrame state id)
    (valid : state.valid = true) (typed : frame.cell.type = objectType)
    (address : Address) (source : Cells) (view : ByteSlice.View) (bytes : Nat → BitVec 8)
    (geometry : ByteSlice.Geometry view) (represented : ByteSlice.Represents source view bytes)
    (reads : ByteRange.Reads state address view.length bytes) (apart : address.allocation ≠ id)
    (total length : Nat) (invariant : WyhashUpdate.Invariant frame.cell.cells total length)
    (fits : view.length ≤ 48 - length) (sumBound : total + view.length < addressLimit) :
    ∃ fuel result after,
      GeneratedWyhashUpdate.update.runFuel fuel (arguments id address view.length) state =
        .finished result after ∧ after.valid = true ∧
      ((result = .error .outOfMemory ∧ after.heap = state.heap) ∨
        ∃ cells buffered, result = .ok (.value (.scalar .unit)) ∧ after.heap = (frame.install cells).heap ∧
          WyhashUpdate.update source view frame.cell.cells = .ok cells ∧
          WyhashUpdate.Invariant cells (total + view.length) buffered) := by
  obtain ⟨fuel, result, after, ran, afterValid, ⟨failed, heap, _⟩ | ⟨cells, buffered, returned, heap, model, preserved, _⟩⟩ :=
    buffered_invocation_framed frame valid typed address source view bytes geometry represented reads apart
      total length invariant fits sumBound
  · exact ⟨fuel, result, after, ran, afterValid, Or.inl ⟨failed, heap⟩⟩
  · exact ⟨fuel, result, after, ran, afterValid, Or.inr ⟨cells, buffered, returned, heap, model, preserved⟩⟩

end Compiler.ZigAir.WyhashUpdateAir
