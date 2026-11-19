/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirLong
import Compiler.ZigAir.WyhashUpdateAirExecution

set_option maxRecDepth 8192

namespace Compiler.ZigAir.WyhashUpdateAir
open Memory AggregateAir Compiler.Extraction Control.Machine

/-- The long branch uses the same native counter and branch preparation as the
buffered case, then derives every index, fill, loop and tail obligation. -/
theorem long_steps {state : State} {id : Nat} (frame : CellFrame state id)
    (valid : state.valid = true) (typed : frame.cell.type = objectType)
    (endBound : frame.cell.base + 104 < addressLimit)
    (address : Address) (source cells : Cells) (view : ByteSlice.View) (bytes : Nat → BitVec 8)
    (geometry : ByteSlice.Geometry view) (represented : ByteSlice.Represents source view bytes)
    (reads : ByteRange.Reads state address view.length bytes) (apart : address.allocation ≠ id)
    (total length selfSlot inputSlot : Nat) (invariant : WyhashUpdate.Invariant cells total length)
    (more : 48 - length < view.length) (sumBound : total + view.length < addressLimit)
    (budget : view.length + 48 < addressLimit) (selfApart : selfSlot ≠ id) (inputApart : inputSlot ≠ id)
    (selfRead : Memory.load state (slot false (.pointer true false objectType) selfSlot) = .ok (selfPointer id))
    (inputRead : Memory.load state (slot false inputType inputSlot) = .ok (.slice inputType address view.length))
    (countRead : Memory.load state (.pointer (.pointer false false usize) ⟨inputSlot, 8⟩) = .ok (.scalar (.int false 64 view.length)))
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (foundSelf : env 4 = some (.value (slot false (.pointer true false objectType) selfSlot)))
    (foundInput : env 7 = some (.value (slot false inputType inputSlot))) :
    ∃ after,
      (∃ failedCells,
        Long.Interrupted source view length (cells.set 40 (WyhashLocal.word (BitVec.ofNat 64 (total + view.length)))) failedCells ∧
        WyhashUpdate.Core failedCells (total + view.length) ∧ StackFrame (frame.install failedCells) after ∧
        Steps AggregateCall.semantics args (.suspended ⟨remaining 8, env, frame.install cells, outer⟩)
          (.finished (.fault .outOfMemory after))) ∨
      ∃ finalCells buffered, WyhashUpdate.update source view cells = .ok finalCells ∧
        WyhashUpdate.Invariant finalCells (total + view.length) buffered ∧ StackFrame (frame.install finalCells) after ∧
        Steps AggregateCall.semantics args (.suspended ⟨remaining 8, env, frame.install cells, outer⟩)
          (.finished (.returned (.value (.scalar .unit)) after)) := by
  have sumWord : total + view.length < 2 ^ 64 := sumBound
  have limit : 48 < addressLimit := by decide
  let counted := cells.set 40 (WyhashLocal.word (BitVec.ofNat 64 (total + view.length)))
  have countedCore : WyhashUpdate.Core counted (total + view.length) := by
    simpa only [↓reduceIte, BitVec.toNat_ofNat, Nat.mod_eq_of_lt sumWord] using
      invariant.core.store_word 40 (BitVec.ofNat 64 (total + view.length)) (by decide)
  have lengthField : counted.lookup 48 = some (WyhashLocal.word (BitVec.ofNat 64 length)) := by
    simpa only [counted, Cells.lookup_set_other _ _ _ _ (by decide : 48 ≠ 40)] using invariant.lengthField
  have head : ∀ i < length, WyhashUpdate.ByteAt counted (56 + i) := by
    intro i inside
    simpa only [WyhashUpdate.ByteAt, counted, Cells.lookup_set_other _ _ _ _ (by omega : 56 + i ≠ 40)] using invariant.head i inside
  let countedEnv := counterEnv env id inputSlot total view.length
  let loaded := guardEnv countedEnv id inputSlot length view.length
  let chosen := (decisionEnv loaded length view.length).set 15 (.value (.scalar .unit))
  let inner := Frame.block 15 (.scalar .unit) longBody :: outer
  have countPath := counter_steps frame cells typed total view.length selfSlot inputSlot sumBound invariant.core.count
    selfApart inputApart selfRead countRead args env outer foundSelf foundInput
  have loadPath := guard_loads frame counted typed length view.length selfSlot inputSlot
    (by have := invariant.bounded; omega) (by omega) lengthField
    selfApart inputApart selfRead countRead args countedEnv inner
    (by simp [countedEnv, counterEnv, Control.Env.set, foundSelf]) (by simp [countedEnv, counterEnv, Control.Env.set, foundInput])
  have choice := guard_select (frame.install counted) length view.length invariant.bounded (by omega) args loaded inner
    (by simp [loaded, guardEnv, Control.Env.set]) (by simp [loaded, guardEnv, Control.Env.set])
  rw [if_neg (by omega : ¬view.length ≤ 48 - length)] at choice
  have jump : Steps AggregateCall.semantics args
      (.suspended ⟨.jump 15 (.constant (.value (.scalar .unit))), decisionEnv loaded length view.length, frame.install counted, inner⟩)
      (.suspended ⟨longBody, chosen, frame.install counted, outer⟩) := .step _ (.refl _)
  have entered : Steps AggregateCall.semantics args
      (.suspended ⟨remaining 15, countedEnv, frame.install counted, outer⟩)
      (.suspended ⟨longBody, chosen, frame.install counted, outer⟩) := by
    rw [generated_guard]
    apply Steps.step
    exact loadPath.trans AggregateCall.semantics args (choice.trans AggregateCall.semantics args jump)
  let ctx : Loop.Context (frame.install counted) id := {
    frame := frame.replaced counted
    valid := frame.valid counted valid (typed ▸ countedCore.valid)
    typed := typed
    source := source, view := view, address := address, bytes := bytes
    geometry := geometry, represented := represented
    reads := reads.install frame counted _ _ _ apart
    apart := apart, selfSlot := selfSlot, inputSlot := inputSlot, indexSlot := state.nextId
    selfApart := selfApart, inputApart := inputApart
    selfRead := load_saved frame counted selfSlot (.pointer true false objectType) 0 _ selfApart selfRead
    inputRead := load_saved frame counted inputSlot inputType 0 _ inputApart inputRead
    countRead := load_saved frame counted inputSlot usize 8 _ inputApart countRead
    indexFresh := Nat.le_refl _, budget := budget, total := total + view.length }
  obtain ⟨after, ⟨failedCells, failure, failedCore, failedStack, failedPath⟩ |
      ⟨finalCells, bodyRun, _, finalStack, finalPath⟩⟩ :=
    Long.execute ctx rfl countedCore endBound length invariant.bounded more lengthField head args chosen outer
      (by simp [ctx, chosen, decisionEnv, loaded, guardEnv, countedEnv, counterEnv, Control.Env.set, foundSelf])
      (by simp [ctx, chosen, decisionEnv, loaded, guardEnv, countedEnv, counterEnv, Control.Env.set, foundInput])
  · change StackFrame ((frame.replaced counted).install failedCells) after at failedStack
    rw [frame.replaced_install] at failedStack
    exact ⟨after, Or.inl ⟨failedCells, failure, failedCore, failedStack,
      countPath.trans AggregateCall.semantics args (entered.trans AggregateCall.semantics args failedPath)⟩⟩
  · have model := WyhashUpdate.update_from_body source cells view total length invariant sumBound finalCells bodyRun
    obtain ⟨expected, buffered, logical, preserved⟩ := WyhashUpdate.update_verified source cells view bytes
      geometry represented total length invariant sumBound budget
    have equal := Except.ok.inj (model.symm.trans logical)
    subst expected
    change StackFrame ((frame.replaced counted).install finalCells) after at finalStack
    rw [frame.replaced_install] at finalStack
    exact ⟨after, Or.inr ⟨finalCells, buffered, model, preserved, finalStack,
      countPath.trans AggregateCall.semantics args (entered.trans AggregateCall.semantics args finalPath)⟩⟩

end Compiler.ZigAir.WyhashUpdateAir
