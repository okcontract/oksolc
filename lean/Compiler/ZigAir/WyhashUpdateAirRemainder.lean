/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirFinish

set_option maxRecDepth 8192

namespace Compiler.ZigAir.WyhashUpdateAir.Remainder
open Memory AggregateAir Compiler.Extraction Control.Machine
abbrev Code := Round.Code

def suffix : Code :=
  (GeneratedWyhashUpdate.update.body.blockBody? 595).getD (.ret (.constant (.value (.scalar .unit))))

def continuation : Code := .block 595 (.scalar .unit) suffix Finish.body

def parameter : Code := AggregateCall.ReadonlyParameter.code 592 591 inputType continuation

def preparation : Code :=
  .bind 585 usize (.primitive (.load (.local 50))) $
  .bind 586 inputType (.primitive (.load (.local 7))) $
  .bind 587 (.pointer false true ByteSlice.byte) (.primitive (.memory (.slicePtr (.local 586)))) $
  .bind 588 (.pointer false true ByteSlice.byte)
    (.primitive (.memory (.offsetPointer false (.local 587) (.local 585)))) $
  .bind 589 usize (.primitive (.memory (.sliceLen (.local 586)))) $
  .bind 590 usize (.primitive (.memory (.scalar (.arithmetic .sub .unchecked (.local 589) (.local 585))))) $
  .bind 680 (.scalar .unit) (.primitive (.memory (.checkBounds (.local 585) (.local 589) (.slice (.local 586))))) $
  .bind 591 inputType (.primitive (.memory (.slice inputType (.local 588) (.local 590)))) parameter

theorem generated_preparation : Loop.continuation = preparation := by decide +kernel

def headEnv (env : Env) (address : Address) (index count : Nat) : Env :=
  let e585 := env.set 585 (size index)
  let e586 := e585.set 586 (.value (.slice inputType address count))
  let e587 := e586.set 587 (.value (.pointer (.pointer false true ByteSlice.byte) address))
  let e588 := e587.set 588 (.value (.pointer (.pointer false true ByteSlice.byte)
    ⟨address.allocation, address.offset + index⟩))
  let e589 := e588.set 589 (size count)
  let e590 := e589.set 590 (size (count - index))
  e590

def preparedEnv (env : Env) (address : Address) (index count : Nat) : Env :=
  let env := (headEnv env address index count).set 680 (.value (.scalar .unit))
  env.set 591 (.value (.slice inputType ⟨address.allocation, address.offset + index⟩ (count - index)))

theorem prepared_before (env : Env) (address : Address) (index count query : Nat) (earlier : query < 585) :
    preparedEnv env address index count query = env query := by
  simp (disch := omega) only [preparedEnv, headEnv, Control.Env.set, if_neg]

theorem head_steps (state : State) (address : Address) (index count inputSlot indexSlot : Nat)
    (bytes : Nat → BitVec 8) (reads : ByteRange.Reads state address count bytes)
    (inside : index < count) (bound : count < addressLimit)
    (inputRead : Memory.load state (slot false inputType inputSlot) = .ok (.slice inputType address count))
    (indexRead : Memory.load state (slot true usize indexSlot) = .ok (.scalar (.int false 64 index)))
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (foundInput : env 7 = some (.value (slot false inputType inputSlot)))
    (foundIndex : env 50 = some (.value (slot true usize indexSlot))) :
    Steps AggregateCall.semantics args (.suspended ⟨Loop.continuation, env, state, outer⟩)
      (.suspended ⟨preparation.dropBindings 6, headEnv env address index count, state, outer⟩) := by
  let e585 := env.set 585 (size index)
  let e586 := e585.set 586 (.value (.slice inputType address count))
  let e587 := e586.set 587 (.value (.pointer (.pointer false true ByteSlice.byte) address))
  let e588 := e587.set 588 (.value (.pointer (.pointer false true ByteSlice.byte)
    ⟨address.allocation, address.offset + index⟩))
  let e589 := e588.set 589 (size count)
  let e590 := e589.set 590 (size (count - index))
  have p585 := eval_load (.local 50) args env state _ _ (value_local _ _ _ foundIndex rfl)
    (congrArg (Except.map Register.value) indexRead)
  have p586 := eval_load (.local 7) args e585 state (slot false inputType inputSlot) _
    (value_local _ _ _ (by simp [e585, Control.Env.set, foundInput]) rfl)
    (congrArg (Except.map Register.value) inputRead)
  have p587 := slice_pointer state args e586 586 false address count bound (by simp [e586, Control.Env.set])
  have p588 : (AggregateAir.Prim.memory (.offsetPointer false (.local 587) (.local 585))).eval args e587 state =
      (.ok (.value (.pointer (.pointer false true ByteSlice.byte) ⟨address.allocation, address.offset + index⟩)), state) := by
    have data := SliceBytesAir.memory_local e587 587 (.pointer (.pointer false true ByteSlice.byte) address)
      (by simp [e587, Control.Env.set]) rfl
    have offset := SliceBytesAir.natural_size e587 585 index (by omega)
      (by simp [e587, e586, e585, Control.Env.set])
    exact eval_offset _ _ args e587 state _ _ _ data offset
      (by simpa only [Nat.add_zero, Nat.zero_add] using reads.offset_pointer 0 index (by omega) (by omega))
  have p589 := slice_length state args e588 586 false address count bound (by simp [e588, e587, e586, Control.Env.set])
  have p590 := size_sub state args e589 (.local 589) (.local 585) count index bound (by omega)
    (SliceBytesAir.scalar_size e589 589 count bound (by simp [e589, Control.Env.set]))
    (SliceBytesAir.scalar_size e589 585 index (by omega) (by simp [e589, e588, e587, e586, e585, Control.Env.set]))
  rw [generated_preparation, preparation]
  exact AggregateCall.primitive_steps args p585 (SliceBytesAir.size_typed index (by omega)) <|
    AggregateCall.primitive_steps args p586 (by exact slice_valid false address count bound) <|
    AggregateCall.primitive_steps args p587 rfl <|
    AggregateCall.primitive_steps args p588 rfl <|
    AggregateCall.primitive_steps args p589 (SliceBytesAir.size_typed count bound) <|
    AggregateCall.primitive_steps args p590 (SliceBytesAir.size_typed (count - index) (by omega)) (.refl _)

theorem construct_steps (state : State) (address : Address) (index count : Nat)
    (bytes : Nat → BitVec 8) (reads : ByteRange.Reads state address count bytes)
    (inside : index < count) (bound : count < addressLimit)
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (h585 : env 585 = some (size index))
    (h586 : env 586 = some (.value (.slice inputType address count)))
    (h588 : env 588 = some (.value (.pointer (.pointer false true ByteSlice.byte)
      ⟨address.allocation, address.offset + index⟩)))
    (h589 : env 589 = some (size count)) (h590 : env 590 = some (size (count - index))) :
    Steps AggregateCall.semantics args (.suspended ⟨preparation.dropBindings 6, env, state, outer⟩)
      (.suspended ⟨parameter, (env.set 680 (.value (.scalar .unit))).set 591
        (.value (.slice inputType ⟨address.allocation, address.offset + index⟩ (count - index))), state, outer⟩) := by
  let e680 := env.set 680 (.value (.scalar .unit))
  have p680 : (AggregateAir.Prim.memory (.checkBounds (.local 585) (.local 589) (.slice (.local 586)))).eval args env state =
      (.ok (.value (.scalar .unit)), state) := by
    have first := SliceBytesAir.natural_size env 585 index (by omega)
      h585
    have last := SliceBytesAir.natural_size env 589 count bound h589
    have data := SliceBytesAir.memory_local env 586 (.slice inputType address count)
      h586 (slice_valid false address count bound)
    apply eval_bounds _ _ _ args env state index count (some count) first last
    · simp only [MemoryAir.Bound.eval, data, bind, Except.bind]
    · simp [checkSliceBounds, Nat.le_of_lt inside]
  have p591 := slice_construct state args e680 (.local 588) (.local 590) false
    ⟨address.allocation, address.offset + index⟩ (count - index)
    (SliceBytesAir.memory_local e680 588
      (.pointer (.pointer false true ByteSlice.byte) ⟨address.allocation, address.offset + index⟩)
      (by simp [e680, Control.Env.set, h588]) rfl)
    (SliceBytesAir.natural_size e680 590 (count - index) (by omega) (by simp [e680, Control.Env.set, h590]))
    (reads.make_slice index (count - index) inside (by omega) (by omega))
  simp only [preparation, Control.Code.dropBindings]
  exact AggregateCall.primitive_steps args p680 rfl <|
    AggregateCall.primitive_steps args p591
      (by exact slice_valid false ⟨address.allocation, address.offset + index⟩ (count - index) (by omega)) (.refl _)

theorem prepare_steps (state : State) (address : Address) (index count inputSlot indexSlot : Nat)
    (bytes : Nat → BitVec 8) (reads : ByteRange.Reads state address count bytes)
    (inside : index < count) (bound : count < addressLimit)
    (inputRead : Memory.load state (slot false inputType inputSlot) = .ok (.slice inputType address count))
    (indexRead : Memory.load state (slot true usize indexSlot) = .ok (.scalar (.int false 64 index)))
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (foundInput : env 7 = some (.value (slot false inputType inputSlot)))
    (foundIndex : env 50 = some (.value (slot true usize indexSlot))) :
    Steps AggregateCall.semantics args (.suspended ⟨Loop.continuation, env, state, outer⟩)
      (.suspended ⟨parameter, preparedEnv env address index count, state, outer⟩) := by
  have head := head_steps state address index count inputSlot indexSlot bytes reads inside bound
    inputRead indexRead args env outer foundInput foundIndex
  have tail := construct_steps state address index count bytes reads inside bound args
    (headEnv env address index count) outer
    (by simp [headEnv, Control.Env.set]) (by simp [headEnv, Control.Env.set])
    (by simp [headEnv, Control.Env.set]) (by simp [headEnv, Control.Env.set])
    (by simp [headEnv, Control.Env.set])
  exact head.trans AggregateCall.semantics args tail

/-- The remaining slice is created from original input reads and then saved by
the same native allocation/store/borrow proof used by entry and round parameters. -/
theorem save_steps (state : State) (valid : state.valid = true)
    (address : Address) (index count inputSlot indexSlot : Nat)
    (bytes : Nat → BitVec 8) (reads : ByteRange.Reads state address count bytes)
    (inside : index < count) (bound : count < addressLimit)
    (inputRead : Memory.load state (slot false inputType inputSlot) = .ok (.slice inputType address count))
    (indexRead : Memory.load state (slot true usize indexSlot) = .ok (.scalar (.int false 64 index)))
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (foundInput : env 7 = some (.value (slot false inputType inputSlot)))
    (foundIndex : env 50 = some (.value (slot true usize indexSlot))) :
    ∃ after, StackFrame state after ∧
      (Steps AggregateCall.semantics args (.suspended ⟨Loop.continuation, env, state, outer⟩)
        (.finished (.fault .outOfMemory after)) ∨
       ∃ nextEnv, Steps AggregateCall.semantics args (.suspended ⟨Loop.continuation, env, state, outer⟩)
          (.suspended ⟨continuation, nextEnv, after, outer⟩) ∧
        Memory.load after (.pointer (.pointer false false usize) ⟨state.nextId, 8⟩) =
          .ok (.scalar (.int false 64 (count - index : Nat))) ∧
        after.nextAddress < addressLimit ∧
        nextEnv 594 = some (.value (slot false inputType state.nextId)) ∧
        nextEnv 591 = some (.value (.slice inputType ⟨address.allocation, address.offset + index⟩ (count - index))) ∧
        ∀ query < 585, nextEnv query = env query) := by
  have head := prepare_steps state address index count inputSlot indexSlot bytes reads inside bound
    inputRead indexRead args env outer foundInput foundIndex
  let prepared := preparedEnv env address index count
  obtain ⟨after, stack, failed | ⟨path, read, owner, _, strict⟩⟩ :=
    AggregateCall.ReadonlyParameter.steps 592 591 (by decide)
      (.slice inputType ⟨address.allocation, address.offset + index⟩ (count - index)) ⟨16, 8⟩
      (slice_valid false _ _ (by omega)) rfl (by decide) continuation outer state valid args prepared
      (by simp [prepared, preparedEnv, Control.Env.set])
  · exact ⟨after, stack, Or.inl (head.trans AggregateCall.semantics args failed)⟩
  · refine ⟨after, stack, Or.inr ⟨_, head.trans AggregateCall.semantics args path,
      SavedValue.slice_length after state.nextId false ByteSlice.byte _ _ read owner, strict, ?_, ?_, ?_⟩⟩
    · simp [AggregateCall.ReadonlyParameter.resultEnv, Control.Env.set, Value.type]
    · simp [AggregateCall.ReadonlyParameter.resultEnv, prepared, preparedEnv, Control.Env.set]
    · intro query earlier
      rw [AggregateCall.ReadonlyParameter.before _ _ _ query _ (by omega)]
      exact prepared_before env address index count query earlier

end Compiler.ZigAir.WyhashUpdateAir.Remainder
