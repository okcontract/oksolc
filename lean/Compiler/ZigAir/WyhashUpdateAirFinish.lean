/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirSlices

set_option maxRecDepth 8192

namespace Compiler.ZigAir.WyhashUpdateAir.Finish
open Memory AggregateAir Compiler.Extraction Control.Machine
abbrev Code := Round.Code

def returned : Code :=
  .bind 646 (.pointer true false objectType) (.primitive (.load (.local 4))) $
  .bind 647 (.pointer true false usize) (.primitive (.fieldPointer (.local 646) 48)) $
  .bind 648 (.pointer false false usize) (.primitive (.memory (.pointerField true (.local 594)))) $
  .bind 649 usize (.primitive (.load (.local 648))) $
  .bind 650 (.scalar .unit) (.primitive (.store (.local 647) (.local 649))) $
  .ret (.constant (.value (.scalar .unit)))

def body : Code :=
  .bind 634 (.pointer true false objectType) (.primitive (.load (.local 4))) $
  .bind 635 (.pointer true false (.array 48 ByteSlice.byte)) (.primitive (.fieldPointer (.local 634) 56)) $
  .bind 636 (.pointer false false usize) (.primitive (.memory (.pointerField true (.local 594)))) $
  .bind 637 usize (.primitive (.load (.local 636))) $
  .bind 638 (.pointer true true ByteSlice.byte)
    (.primitive (.memory (.pointerCast (.pointer true true ByteSlice.byte) (.local 635)))) $
  .bind 639 (.pointer true true ByteSlice.byte)
    (.primitive (.memory (.offsetPointer false (.local 638) (.constant (.scalar (.int false 64 0)))))) $
  .bind 640 usize (.primitive (.memory (.scalar (.arithmetic .sub .unchecked (.local 637) (.constant (.int false 64 0)))))) $
  .bind 683 (.scalar .unit) (.primitive (.memory (.checkBounds (.constant (.scalar (.int false 64 0))) (.local 637) (.array 48)))) $
  .bind 641 (.slice true ByteSlice.byte) (.primitive (.memory (.slice (.slice true ByteSlice.byte) (.local 639) (.local 640)))) $
  .bind 642 usize (.primitive (.memory (.sliceLen (.local 641)))) $
  .bind 643 usize (.primitive (.memory (.sliceLen (.local 591)))) $
  .bind 644 (.pointer false true ByteSlice.byte) (.primitive (.memory (.slicePtr (.local 591)))) $
  .bind 645 (.scalar .unit) (.copyBytes (.local 641) (.local 644)) returned

theorem generated_body : (do
    let .block _ _ _ next ← GeneratedWyhashUpdate.update.body.block? 595 | none
    pure next) = some body := by decide +kernel

theorem return_steps {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (typed : frame.cell.type = objectType) (length selfSlot restSlot : Nat) (bound : length < addressLimit)
    (selfApart : selfSlot ≠ id) (restApart : restSlot ≠ id)
    (selfRead : Memory.load state (slot false (.pointer true false objectType) selfSlot) = .ok (selfPointer id))
    (countRead : Memory.load state (.pointer (.pointer false false usize) ⟨restSlot, 8⟩) =
      .ok (.scalar (.int false 64 length)))
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (foundSelf : env 4 = some (.value (slot false (.pointer true false objectType) selfSlot)))
    (foundRest : env 594 = some (.value (slot false inputType restSlot))) :
    Steps AggregateCall.semantics args (.suspended ⟨returned, env, frame.install cells, outer⟩)
      (.finished (.returned (.value (.scalar .unit))
        (frame.install (cells.set 48 (WyhashLocal.word (BitVec.ofNat 64 length)))))) := by
  let e646 := env.set 646 (.value (selfPointer id))
  let e647 := e646.set 647 (.value (.pointer (.pointer true false usize) ⟨id, 48⟩))
  let e648 := e647.set 648 (.value (.pointer (.pointer false false usize) ⟨restSlot, 8⟩))
  let e649 := e648.set 649 (size length)
  have self := load_saved frame cells selfSlot (.pointer true false objectType) 0 _ selfApart selfRead
  have count := load_saved frame cells restSlot usize 8 _ restApart countRead
  have p646 := eval_load (.local 4) args env (frame.install cells) _ _
    (value_local _ _ _ foundSelf rfl) (congrArg (Except.map Register.value) self)
  have p647 := eval_field (.local 646) 48 args e646 (frame.install cells) _ _
    (value_local _ _ _ (by simp [e646, Control.Env.set]) rfl)
    (field_pointer frame cells typed 48 usize (by decide))
  have p648 := count_pointer (frame.install cells) args e647 restSlot 594
    (by simp [e647, e646, Control.Env.set, foundRest])
  have p649 := eval_load (.local 648) args e648 (frame.install cells)
    (.pointer (.pointer false false usize) ⟨restSlot, 8⟩) _
    (value_local _ _ _ (by simp [e648, Control.Env.set]) rfl) (congrArg (Except.map Register.value) count)
  have written := WyhashInit.object_word_store frame cells typed 48 (by decide) (BitVec.ofNat 64 length)
  have wordBound : length < 2 ^ 64 := bound
  simp only [WyhashLocal.word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt wordBound] at written
  have p650 := eval_store (.local 647) (.local 649) args e649 (frame.install cells) _
    (.pointer (.pointer true false usize) ⟨id, 48⟩) (size length)
    (value_local _ _ _ (by simp [e649, e648, e647, Control.Env.set]) rfl)
    (ref_local _ _ _ (by simp [e649, Control.Env.set]) (SliceBytesAir.size_valid length bound)) written
  rw [returned]
  apply AggregateCall.primitive_steps args p646 rfl
  apply AggregateCall.primitive_steps args p647 rfl
  apply AggregateCall.primitive_steps args p648 rfl
  apply AggregateCall.primitive_steps args p649 (SliceBytesAir.size_typed length bound)
  apply AggregateCall.primitive_steps args p650 rfl
  simp only [WyhashLocal.word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt wordBound]
  exact .step _ (.refl _)

def preparedEnv (env : Env) (id restSlot count : Nat) : Env :=
  let e634 := env.set 634 (.value (selfPointer id))
  let e635 := e634.set 635 (.value (.pointer (.pointer true false (.array 48 ByteSlice.byte)) ⟨id, 56⟩))
  let e636 := e635.set 636 (.value (.pointer (.pointer false false usize) ⟨restSlot, 8⟩))
  let e637 := e636.set 637 (size count)
  let e638 := e637.set 638 (.value (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56⟩))
  let e639 := e638.set 639 (.value (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56⟩))
  let e640 := e639.set 640 (size count)
  let e683 := e640.set 683 (.value (.scalar .unit))
  e683

theorem prepare_steps {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (valid : state.valid = true) (typed : frame.cell.type = objectType)
    (endBound : frame.cell.base + 104 < addressLimit) (count selfSlot restSlot : Nat) (bounded : count ≤ 48)
    (selfApart : selfSlot ≠ id) (restApart : restSlot ≠ id)
    (selfRead : Memory.load state (slot false (.pointer true false objectType) selfSlot) = .ok (selfPointer id))
    (countRead : Memory.load state (.pointer (.pointer false false usize) ⟨restSlot, 8⟩) =
      .ok (.scalar (.int false 64 count)))
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (foundSelf : env 4 = some (.value (slot false (.pointer true false objectType) selfSlot)))
    (foundRest : env 594 = some (.value (slot false inputType restSlot))) :
    Steps AggregateCall.semantics args (.suspended ⟨body, env, frame.install cells, outer⟩)
      (.suspended ⟨body.dropBindings 8, preparedEnv env id restSlot count, frame.install cells, outer⟩) := by
  have limit : 48 < addressLimit := by decide
  have countBound : count < addressLimit := by omega
  let e634 := env.set 634 (.value (selfPointer id))
  let e635 := e634.set 635 (.value (.pointer (.pointer true false (.array 48 ByteSlice.byte)) ⟨id, 56⟩))
  let e636 := e635.set 636 (.value (.pointer (.pointer false false usize) ⟨restSlot, 8⟩))
  let e637 := e636.set 637 (size count)
  let e638 := e637.set 638 (.value (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56⟩))
  let e639 := e638.set 639 (.value (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56⟩))
  let e640 := e639.set 640 (size count)
  let e683 := e640.set 683 (.value (.scalar .unit))
  have self := load_saved frame cells selfSlot (.pointer true false objectType) 0 _ selfApart selfRead
  have countRead' := load_saved frame cells restSlot usize 8 _ restApart countRead
  have p634 := eval_load (.local 4) args env (frame.install cells) _ _
    (value_local _ _ _ foundSelf rfl) (congrArg (Except.map Register.value) self)
  have p635 := eval_field (.local 634) 56 args e634 (frame.install cells) _ _
    (value_local _ _ _ (by simp [e634, Control.Env.set]) rfl)
    (field_pointer frame cells typed 56 (.array 48 ByteSlice.byte) (by decide))
  have p636 := count_pointer (frame.install cells) args e635 restSlot 594
    (by simp [e635, e634, Control.Env.set, foundRest])
  have p637 := eval_load (.local 636) args e636 (frame.install cells)
    (.pointer (.pointer false false usize) ⟨restSlot, 8⟩) _
    (value_local _ _ _ (by simp [e636, Control.Env.set]) rfl)
    (congrArg (Except.map Register.value) countRead')
  have p638 : (AggregateAir.Prim.memory (.pointerCast (.pointer true true ByteSlice.byte) (.local 635))).eval
      args e637 (frame.install cells) =
      (.ok (.value (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56⟩)), frame.install cells) := by
    apply eval_memory
    have data := SliceBytesAir.memory_local e637 635
      (.pointer (.pointer true false (.array 48 ByteSlice.byte)) ⟨id, 56⟩)
      (by simp [e637, e636, e635, Control.Env.set]) rfl
    simp only [MemoryAir.Prim.eval, MemoryAir.Prim.transition, data,
      buffer_cast frame cells valid typed endBound, bind, Except.bind]
  have p639 : (AggregateAir.Prim.memory (.offsetPointer false (.local 638)
      (.constant (.scalar (.int false 64 0))))).eval args e638 (frame.install cells) =
      (.ok (.value (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56⟩)), frame.install cells) := by
    have data := SliceBytesAir.memory_local e638 638 (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56⟩)
      (by simp [e638, Control.Env.set]) rfl
    exact eval_offset _ _ args e638 (frame.install cells) _ _ 0 data rfl
      (by simpa only [Nat.add_zero] using buffer_offset frame cells valid typed endBound 0 (by decide))
  have p640 := size_sub (frame.install cells) args e639 (.local 637) (.constant (.int false 64 0)) count 0
    countBound (by omega)
    (SliceBytesAir.scalar_size e639 637 count countBound (by simp [e639, e638, e637, Control.Env.set])) rfl
  simp only [Nat.sub_zero] at p640
  have p683 : (AggregateAir.Prim.memory (.checkBounds (.constant (.scalar (.int false 64 0)))
      (.local 637) (.array 48))).eval args e640 (frame.install cells) =
      (.ok (.value (.scalar .unit)), frame.install cells) := by
    apply eval_bounds _ _ _ args e640 (frame.install cells) 0 count (some 48) rfl
      (SliceBytesAir.natural_size e640 637 count countBound (by simp [e640, e639, e638, e637, Control.Env.set])) rfl
    simp [checkSliceBounds, bounded]
  rw [body]
  exact AggregateCall.primitive_steps args p634 rfl <|
    AggregateCall.primitive_steps args p635 rfl <|
    AggregateCall.primitive_steps args p636 rfl <|
    AggregateCall.primitive_steps args p637 (SliceBytesAir.size_typed _ countBound) <|
    AggregateCall.primitive_steps args p638 rfl <|
    AggregateCall.primitive_steps args p639 rfl <|
    AggregateCall.primitive_steps args p640 (SliceBytesAir.size_typed _ countBound) <|
    AggregateCall.primitive_steps args p683 rfl (.refl _)

/-- Copy the remaining admitted bytes and return from the original update.
The saved remaining-slice descriptor is read again for the final length store. -/
theorem copy_return_steps {state : State} {id : Nat} (frame : CellFrame state id)
    (valid : state.valid = true) (typed : frame.cell.type = objectType)
    (endBound : frame.cell.base + 104 < addressLimit)
    (address : Address) (source cells : Cells) (view : ByteSlice.View) (bytes : Nat → BitVec 8)
    (geometry : ByteSlice.Geometry view) (represented : ByteSlice.Represents source view bytes)
    (reads : ByteRange.Reads state address view.length bytes) (apart : address.allocation ≠ id)
    (total index count selfSlot restSlot : Nat) (core : WyhashUpdate.Core cells total)
    (inside : index + count ≤ view.length) (bounded : count ≤ 48)
    (selfApart : selfSlot ≠ id) (restApart : restSlot ≠ id)
    (selfRead : Memory.load state (slot false (.pointer true false objectType) selfSlot) = .ok (selfPointer id))
    (countRead : Memory.load state (.pointer (.pointer false false usize) ⟨restSlot, 8⟩) =
      .ok (.scalar (.int false 64 count)))
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (foundSelf : env 4 = some (.value (slot false (.pointer true false objectType) selfSlot)))
    (foundRest : env 594 = some (.value (slot false inputType restSlot)))
    (foundSlice : env 591 = some (.value (.slice inputType
      ⟨address.allocation, address.offset + index⟩ count)))
    (foundTarget : env 639 = some (.value (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56⟩)))
    (foundCount : env 640 = some (size count)) :
    ∃ copied, Steps AggregateCall.semantics args (.suspended ⟨body.dropBindings 8, env, frame.install cells, outer⟩)
        (.finished (.returned (.value (.scalar .unit))
          (frame.install (copied.set 48 (WyhashLocal.word (BitVec.ofNat 64 count)))))) ∧
      ByteSlice.copy source view (WyhashBuffer.buffer 0 48) index 0 count cells = .ok copied ∧
      WyhashUpdate.Core copied total ∧
      (∀ i < count, WyhashUpdate.ByteAt copied (56 + i)) ∧
      (∀ offset, offset < 56 ∨ 56 + count ≤ offset → copied.lookup offset = cells.lookup offset) := by
  have limit : 48 < addressLimit := by decide
  have countBound : count < addressLimit := by omega
  let target := Value.slice (.slice true ByteSlice.byte) ⟨id, 56⟩ count
  let inputAddress : Address := ⟨address.allocation, address.offset + index⟩
  let e641 := env.set 641 (.value target)
  let e642 := e641.set 642 (size count)
  let e643 := e642.set 643 (size count)
  let e644 := e643.set 644 (.value (.pointer (.pointer false true ByteSlice.byte) inputAddress))
  let e645 := e644.set 645 (.value (.scalar .unit))
  have p641 := slice_construct (frame.install cells) args env (.local 639) (.local 640) true ⟨id, 56⟩ count
    (SliceBytesAir.memory_local env 639 (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56⟩) foundTarget rfl)
    (SliceBytesAir.natural_size env 640 count countBound foundCount)
    (by simpa only [Nat.add_zero] using buffer_slice frame cells valid typed endBound 0 count (by omega))
  have p642 := slice_length (frame.install cells) args e641 641 true ⟨id, 56⟩ count countBound
    (by simp [e641, target, Control.Env.set])
  have p643 := slice_length (frame.install cells) args e642 591 false inputAddress count countBound
    (by simp [e642, e641, Control.Env.set, foundSlice, inputAddress])
  have p644 := slice_pointer (frame.install cells) args e643 591 false inputAddress count countBound
    (by simp [e643, e642, e641, Control.Env.set, foundSlice, inputAddress])
  obtain ⟨copied, p645, copiedRun, copiedCore, head, outside⟩ := copy_bytes frame typed address source cells view bytes
    geometry represented reads apart total index 0 count core inside (by omega) args e644 641 644
    (by simp [e644, e643, e642, e641, Control.Env.set, target]) (by simp [e644, Control.Env.set, inputAddress])
  have tail := return_steps frame copied typed count selfSlot restSlot countBound selfApart restApart selfRead countRead
    args e645 outer
    (by simp [e645, e644, e643, e642, e641, Control.Env.set, foundSelf])
    (by simp [e645, e644, e643, e642, e641, Control.Env.set, foundRest])
  refine ⟨copied, ?_, copiedRun, copiedCore, ?_, ?_⟩
  · simp only [body, Control.Code.dropBindings]
    apply AggregateCall.primitive_steps args p641 (by exact slice_valid true ⟨id, 56⟩ count countBound)
    apply AggregateCall.primitive_steps args p642 (SliceBytesAir.size_typed _ countBound)
    apply AggregateCall.primitive_steps args p643 (SliceBytesAir.size_typed _ countBound)
    apply AggregateCall.primitive_steps args p644 rfl
    exact Steps.bind_ok AggregateCall.semantics args p645 rfl tail
  · simpa only [Nat.zero_add] using head
  · simpa only [Nat.add_zero] using outside

/-- Copy the remaining admitted bytes and return from the original update.
The saved remaining-slice descriptor is read again for the final length store. -/
theorem body_steps {state : State} {id : Nat} (frame : CellFrame state id)
    (valid : state.valid = true) (typed : frame.cell.type = objectType)
    (endBound : frame.cell.base + 104 < addressLimit)
    (address : Address) (source cells : Cells) (view : ByteSlice.View) (bytes : Nat → BitVec 8)
    (geometry : ByteSlice.Geometry view) (represented : ByteSlice.Represents source view bytes)
    (reads : ByteRange.Reads state address view.length bytes) (apart : address.allocation ≠ id)
    (total index count selfSlot restSlot : Nat) (core : WyhashUpdate.Core cells total)
    (inside : index + count ≤ view.length) (bounded : count ≤ 48)
    (selfApart : selfSlot ≠ id) (restApart : restSlot ≠ id)
    (selfRead : Memory.load state (slot false (.pointer true false objectType) selfSlot) = .ok (selfPointer id))
    (countRead : Memory.load state (.pointer (.pointer false false usize) ⟨restSlot, 8⟩) =
      .ok (.scalar (.int false 64 count)))
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (foundSelf : env 4 = some (.value (slot false (.pointer true false objectType) selfSlot)))
    (foundRest : env 594 = some (.value (slot false inputType restSlot)))
    (foundSlice : env 591 = some (.value (.slice inputType
      ⟨address.allocation, address.offset + index⟩ count))) :
    ∃ copied, Steps AggregateCall.semantics args (.suspended ⟨body, env, frame.install cells, outer⟩)
        (.finished (.returned (.value (.scalar .unit))
          (frame.install (copied.set 48 (WyhashLocal.word (BitVec.ofNat 64 count)))))) ∧
      ByteSlice.copy source view (WyhashBuffer.buffer 0 48) index 0 count cells = .ok copied ∧
      WyhashUpdate.Core copied total ∧
      (∀ i < count, WyhashUpdate.ByteAt copied (56 + i)) ∧
      (∀ offset, offset < 56 ∨ 56 + count ≤ offset → copied.lookup offset = cells.lookup offset) := by
  have head := prepare_steps frame cells valid typed endBound count selfSlot restSlot bounded
    selfApart restApart selfRead countRead args env outer foundSelf foundRest
  obtain ⟨copied, tail, model, nextCore, bytes, outside⟩ := copy_return_steps frame valid typed endBound
    address source cells view bytes geometry represented reads apart total index count selfSlot restSlot core
    inside bounded selfApart restApart selfRead countRead args (preparedEnv env id restSlot count) outer
    (by simp [preparedEnv, Control.Env.set, foundSelf])
    (by simp [preparedEnv, Control.Env.set, foundRest])
    (by simp [preparedEnv, Control.Env.set, foundSlice])
    (by simp [preparedEnv, Control.Env.set]) (by simp [preparedEnv, Control.Env.set])
  exact ⟨copied, head.trans AggregateCall.semantics args tail, model, nextCore, bytes, outside⟩

end Compiler.ZigAir.WyhashUpdateAir.Finish
