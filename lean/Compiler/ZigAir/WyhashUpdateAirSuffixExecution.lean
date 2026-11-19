/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirSuffixSource

set_option maxRecDepth 8192

namespace Compiler.ZigAir.WyhashUpdateAir.Suffix
open Memory AggregateAir Compiler.Extraction Control.Machine

def copyEnd : Code :=
  .bind 627 usize (.primitive (.memory (.sliceLen (.local 618)))) $
  .bind 628 usize (.primitive (.memory (.sliceLen (.local 626)))) $
  .bind 629 (.pointer false true ByteSlice.byte) (.primitive (.memory (.slicePtr (.local 626)))) $
  .bind 630 (.scalar .unit) (.copyBytes (.local 618) (.local 629)) skip

theorem generated_copy_end : copyAt 22 = copyEnd := by decide +kernel

theorem copy_end_steps {state : State} {id : Nat} (frame : CellFrame state id)
    (typed : frame.cell.type = objectType) (address : Address) (source cells : Cells)
    (view : ByteSlice.View) (bytes : Nat → BitVec 8) (geometry : ByteSlice.Geometry view)
    (represented : ByteSlice.Represents source view bytes)
    (reads : ByteRange.Reads state address view.length bytes) (apart : address.allocation ≠ id)
    (total src dst count : Nat) (core : WyhashUpdate.Core cells total)
    (sourceBound : src + count ≤ view.length) (targetBound : dst + count ≤ 48)
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (targetFound : env 618 = some (.value (.slice (.slice true ByteSlice.byte) ⟨id, 56 + dst⟩ count)))
    (sourceFound : env 626 = some (.value (.slice inputType ⟨address.allocation, address.offset + src⟩ count))) :
    ∃ copied nextEnv, Steps AggregateCall.semantics args (.suspended ⟨copyAt 22, env, frame.install cells, outer⟩)
        (.suspended ⟨skip, nextEnv, frame.install copied, outer⟩) ∧
      ByteSlice.copy source view (WyhashBuffer.buffer 0 48) src dst count cells = .ok copied ∧
      WyhashUpdate.Core copied total ∧ (∀ query < 627, nextEnv query = env query) := by
  have limit : 48 < addressLimit := by decide
  have bound : count < addressLimit := by omega
  let e627 := env.set 627 (size count)
  let e628 := e627.set 628 (size count)
  let e629 := e628.set 629 (.value (.pointer (.pointer false true ByteSlice.byte)
    ⟨address.allocation, address.offset + src⟩))
  let next := e629.set 630 (.value (.scalar .unit))
  have p627 := slice_length (frame.install cells) args env 618 true ⟨id, 56 + dst⟩ count bound targetFound
  have p628 := slice_length (frame.install cells) args e627 626 false ⟨address.allocation, address.offset + src⟩ count bound
    (by simp [e627, Control.Env.set, sourceFound])
  have p629 := slice_pointer (frame.install cells) args e628 626 false ⟨address.allocation, address.offset + src⟩ count bound
    (by simp [e628, e627, Control.Env.set, sourceFound])
  obtain ⟨copied, p630, model, nextCore, _, _⟩ := copy_bytes frame typed address source cells view bytes geometry represented
    reads apart total src dst count core sourceBound targetBound args e629 618 629
    (by simp [e629, e628, e627, Control.Env.set, targetFound]) (by simp [e629, Control.Env.set])
  refine ⟨copied, next, ?_, model, nextCore, ?_⟩
  · rw [generated_copy_end, copyEnd]
    exact AggregateCall.primitive_steps args p627 (SliceBytesAir.size_typed _ bound) <|
      AggregateCall.primitive_steps args p628 (SliceBytesAir.size_typed _ bound) <|
      AggregateCall.primitive_steps args p629 rfl <|
      Steps.bind_ok AggregateCall.semantics args p630 rfl (.refl _)
  · intro query earlier
    simp (disch := omega) only [next, e629, e628, e627, Control.Env.set, if_neg]

/-- The retained suffix is read from the original caller input. All pointer
arithmetic, source/destination bounds and byte writes execute in captured order. -/
theorem copy_steps {state : State} {id : Nat} (frame : CellFrame state id)
    (valid : state.valid = true) (typed : frame.cell.type = objectType)
    (endBound : frame.cell.base + 104 < addressLimit)
    (address : Address) (source cells : Cells) (view : ByteSlice.View) (bytes : Nat → BitVec 8)
    (geometry : ByteSlice.Geometry view) (represented : ByteSlice.Represents source view bytes)
    (reads : ByteRange.Reads state address view.length bytes) (apart : address.allocation ≠ id)
    (total index count selfSlot inputSlot indexSlot restSlot : Nat) (core : WyhashUpdate.Core cells total)
    (inside : index < view.length) (short : count < 16) (advanced : 48 ≤ index) (budget : view.length < addressLimit)
    (selfApart : selfSlot ≠ id) (inputApart : inputSlot ≠ id) (indexApart : indexSlot ≠ id) (restApart : restSlot ≠ id)
    (selfRead : Memory.load state (slot false (.pointer true false objectType) selfSlot) = .ok (selfPointer id))
    (inputRead : Memory.load state (slot false inputType inputSlot) = .ok (.slice inputType address view.length))
    (indexRead : Memory.load state (slot true usize indexSlot) = .ok (.scalar (.int false 64 index)))
    (countRead : Memory.load state (.pointer (.pointer false false usize) ⟨restSlot, 8⟩) = .ok (.scalar (.int false 64 count)))
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (foundSelf : env 4 = some (.value (slot false (.pointer true false objectType) selfSlot)))
    (foundInput : env 7 = some (.value (slot false inputType inputSlot)))
    (foundIndex : env 50 = some (.value (slot true usize indexSlot)))
    (foundRest : env 594 = some (.value (slot false inputType restSlot))) :
    ∃ copied nextEnv, Steps AggregateCall.semantics args (.suspended ⟨copy, env, frame.install cells, outer⟩)
        (.suspended ⟨skip, nextEnv, frame.install copied, outer⟩) ∧
      ByteSlice.copy source view (WyhashBuffer.buffer 0 48) (index - (16 - count)) (48 - (16 - count)) (16 - count) cells = .ok copied ∧
      WyhashUpdate.Core copied total ∧ (∀ query < 607, nextEnv query = env query) := by
  obtain ⟨targetEnv, targetPath, missing, target, targetBefore⟩ := target_steps frame cells valid typed endBound count
    selfSlot restSlot short selfApart restApart selfRead countRead args env outer foundSelf foundRest
  obtain ⟨sourceEnv, sourcePath, input, sourceBefore⟩ := source_steps (frame.install cells) address index view.length
    (16 - count) inputSlot indexSlot bytes (reads.install frame cells _ _ _ apart) inside (by omega) budget
    (load_saved frame cells inputSlot inputType 0 _ inputApart inputRead)
    ((frame.load_outside cells ⟨indexSlot, 0⟩ indexApart true false usize).trans indexRead)
    args targetEnv outer (by rw [targetBefore 7 (by decide)]; exact foundInput)
    (by rw [targetBefore 50 (by decide)]; exact foundIndex) missing
  obtain ⟨copied, nextEnv, copiedPath, copiedRun, nextCore, copyBefore⟩ := copy_end_steps frame typed address source cells view bytes
    geometry represented reads apart total (index - (16 - count)) (48 - (16 - count)) (16 - count) core
    (by omega) (by omega) args sourceEnv outer (by rw [sourceBefore 618 (by decide)]; exact target) input
  refine ⟨copied, nextEnv, targetPath.trans AggregateCall.semantics args
    (sourcePath.trans AggregateCall.semantics args copiedPath), copiedRun, nextCore, ?_⟩
  intro query earlier
  rw [copyBefore query (by omega), sourceBefore query (by omega), targetBefore query earlier]

/-- Both branches of the original suffix block rejoin the final copy. The
resulting cells equal the existing conditional copy in `updateBody`. -/
theorem execute {state : State} {id : Nat} (frame : CellFrame state id)
    (valid : state.valid = true) (typed : frame.cell.type = objectType)
    (endBound : frame.cell.base + 104 < addressLimit)
    (address : Address) (source cells : Cells) (view : ByteSlice.View) (bytes : Nat → BitVec 8)
    (geometry : ByteSlice.Geometry view) (represented : ByteSlice.Represents source view bytes)
    (reads : ByteRange.Reads state address view.length bytes) (apart : address.allocation ≠ id)
    (total index count selfSlot inputSlot indexSlot restSlot : Nat) (core : WyhashUpdate.Core cells total)
    (inside : index < view.length) (countBound : count < addressLimit) (budget : view.length < addressLimit)
    (selfApart : selfSlot ≠ id) (inputApart : inputSlot ≠ id) (indexApart : indexSlot ≠ id) (restApart : restSlot ≠ id)
    (selfRead : Memory.load state (slot false (.pointer true false objectType) selfSlot) = .ok (selfPointer id))
    (inputRead : Memory.load state (slot false inputType inputSlot) = .ok (.slice inputType address view.length))
    (indexRead : Memory.load state (slot true usize indexSlot) = .ok (.scalar (.int false 64 index)))
    (countRead : Memory.load state (.pointer (.pointer false false usize) ⟨restSlot, 8⟩) = .ok (.scalar (.int false 64 count)))
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (foundSelf : env 4 = some (.value (slot false (.pointer true false objectType) selfSlot)))
    (foundInput : env 7 = some (.value (slot false inputType inputSlot)))
    (foundIndex : env 50 = some (.value (slot true usize indexSlot)))
    (foundRest : env 594 = some (.value (slot false inputType restSlot))) :
    ∃ after nextEnv, Steps AggregateCall.semantics args (.suspended ⟨Remainder.continuation, env, frame.install cells, outer⟩)
        (.suspended ⟨Finish.body, nextEnv, frame.install after, outer⟩) ∧
      (if count < 16 ∧ 48 ≤ index then
        ByteSlice.copy source view (WyhashBuffer.buffer 0 48) (index - (16 - count)) (48 - (16 - count)) (16 - count) cells
       else .ok cells) = .ok after ∧
      WyhashUpdate.Core after total ∧ (∀ query < 595, nextEnv query = env query) := by
  let inner := Frame.block 595 (.scalar .unit) Finish.body :: outer
  have head : Steps AggregateCall.semantics args
      (.suspended ⟨Remainder.continuation, env, frame.install cells, outer⟩)
      (.suspended ⟨Remainder.suffix, env, frame.install cells, inner⟩) := .step _ (.refl _)
  obtain ⟨chosenEnv, chosen, before⟩ := guard_steps (frame.install cells) index count restSlot indexSlot (by omega) countBound
    ((frame.load_outside cells ⟨indexSlot, 0⟩ indexApart true false usize).trans indexRead)
    (load_saved frame cells restSlot usize 8 _ restApart countRead) args env inner foundIndex foundRest
  by_cases selected : count < 16 ∧ 48 ≤ index
  · rw [if_pos selected] at chosen
    obtain ⟨copied, copiedEnv, copiedPath, copiedRun, nextCore, copiedBefore⟩ := copy_steps frame valid typed endBound address source cells
      view bytes geometry represented reads apart total index count selfSlot inputSlot indexSlot restSlot core
      inside selected.1 selected.2 budget selfApart inputApart indexApart restApart selfRead inputRead indexRead countRead
      args chosenEnv inner (by rw [before 4 (by decide)]; exact foundSelf)
      (by rw [before 7 (by decide)]; exact foundInput) (by rw [before 50 (by decide)]; exact foundIndex)
      (by rw [before 594 (by decide)]; exact foundRest)
    have jump : Steps AggregateCall.semantics args (.suspended ⟨skip, copiedEnv, frame.install copied, inner⟩)
        (.suspended ⟨Finish.body, copiedEnv.set 595 (.value (.scalar .unit)), frame.install copied, outer⟩) := .step _ (.refl _)
    refine ⟨copied, _, head.trans AggregateCall.semantics args (chosen.trans AggregateCall.semantics args
      (copiedPath.trans AggregateCall.semantics args jump)), by rw [if_pos selected]; exact copiedRun, nextCore, ?_⟩
    intro query earlier
    rw [Control.Env.set, if_neg (by omega : query ≠ 595), copiedBefore query (by omega), before query (by omega)]
  · rw [if_neg selected] at chosen
    have jump : Steps AggregateCall.semantics args (.suspended ⟨skip, chosenEnv, frame.install cells, inner⟩)
        (.suspended ⟨Finish.body, chosenEnv.set 595 (.value (.scalar .unit)), frame.install cells, outer⟩) := .step _ (.refl _)
    refine ⟨cells, _, head.trans AggregateCall.semantics args (chosen.trans AggregateCall.semantics args jump),
      by rw [if_neg selected], core, ?_⟩
    intro query earlier
    rw [Control.Env.set, if_neg (by omega : query ≠ 595), before query (by omega)]

end Compiler.ZigAir.WyhashUpdateAir.Suffix
