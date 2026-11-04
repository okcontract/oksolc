/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirFillTarget

set_option maxRecDepth 8192

namespace Compiler.ZigAir.WyhashUpdateAir.Fill
open Memory AggregateAir Compiler.Extraction Control.Machine

def sourceCode : Code :=
  .bind 73 usize (.primitive (.load (.local 50))) $
  .bind 74 inputType (.primitive (.load (.local 7))) $
  .bind 75 (.pointer false true ByteSlice.byte) (.primitive (.memory (.slicePtr (.local 74)))) $
  .bind 76 (.pointer false true ByteSlice.byte)
    (.primitive (.memory (.offsetPointer false (.local 75) (.constant (.scalar (.int false 64 0)))))) $
  .bind 77 usize (.primitive (.memory (.scalar (.arithmetic .sub .unchecked (.local 73) (.constant (.int false 64 0)))))) $
  .bind 654 (.scalar .unit) (.primitive (.memory (.checkBounds (.constant (.scalar (.int false 64 0))) (.local 73) (.slice (.local 74))))) $
  .bind 78 inputType (.primitive (.memory (.slice inputType (.local 76) (.local 77)))) (copy.dropBindings 18)

theorem generated_source : copy.dropBindings 11 = sourceCode := by decide +kernel

def sourceEnv (env : Env) (address : Address) (length count : Nat) : Env :=
  let env := env.set 73 (size count)
  let env := env.set 74 (.value (.slice inputType address length))
  let env := env.set 75 (.value (.pointer (.pointer false true ByteSlice.byte) address))
  let env := env.set 76 (.value (.pointer (.pointer false true ByteSlice.byte) address))
  let env := env.set 77 (size count)
  let env := env.set 654 (.value (.scalar .unit))
  env.set 78 (.value (.slice inputType address count))

theorem source_steps (state : State) (address : Address) (length count inputSlot indexSlot : Nat)
    (bytes : Nat → BitVec 8) (reads : ByteRange.Reads state address length bytes)
    (nonempty : 0 < length) (inside : count ≤ length) (bound : length < addressLimit)
    (inputRead : Memory.load state (slot false inputType inputSlot) = .ok (.slice inputType address length))
    (indexRead : Memory.load state (slot true usize indexSlot) = .ok (.scalar (.int false 64 count)))
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (foundInput : env 7 = some (.value (slot false inputType inputSlot)))
    (foundIndex : env 50 = some (.value (slot true usize indexSlot))) :
    Steps AggregateCall.semantics args (.suspended ⟨copy.dropBindings 11, env, state, outer⟩)
      (.suspended ⟨copy.dropBindings 18, sourceEnv env address length count, state, outer⟩) := by
  let e73 := env.set 73 (size count)
  let e74 := e73.set 74 (.value (.slice inputType address length))
  let e75 := e74.set 75 (.value (.pointer (.pointer false true ByteSlice.byte) address))
  let e76 := e75.set 76 (.value (.pointer (.pointer false true ByteSlice.byte) address))
  let e77 := e76.set 77 (size count)
  let e654 := e77.set 654 (.value (.scalar .unit))
  have p73 := eval_load (.local 50) args env state _ _ (value_local _ _ _ foundIndex rfl)
    (congrArg (Except.map Register.value) indexRead)
  have p74 := eval_load (.local 7) args e73 state (slot false inputType inputSlot) _
    (value_local _ _ _ (by simp [e73, Control.Env.set, foundInput]) rfl)
    (congrArg (Except.map Register.value) inputRead)
  have p75 := slice_pointer state args e74 74 false address length bound (by simp [e74, Control.Env.set])
  have offset : offsetPointer state false (.pointer (.pointer false true ByteSlice.byte) address) 0 =
      .ok (.pointer (.pointer false true ByteSlice.byte) address) := by
    simpa only [Nat.add_zero, Nat.zero_add] using reads.offset_pointer 0 0 nonempty nonempty
  have p76 := eval_offset (.local 75) (.constant (.scalar (.int false 64 0))) args e75 state _ _ 0
    (SliceBytesAir.memory_local e75 75 (.pointer (.pointer false true ByteSlice.byte) address)
      (by simp [e75, Control.Env.set]) rfl) rfl offset
  have p77 := size_sub state args e76 (.local 73) (.constant (.int false 64 0)) count 0 (by omega) (by omega)
    (SliceBytesAir.scalar_size e76 73 count (by omega) (by simp [e76, e75, e74, e73, Control.Env.set])) rfl
  simp only [Nat.sub_zero] at p77
  have p654 : (AggregateAir.Prim.memory (.checkBounds (.constant (.scalar (.int false 64 0))) (.local 73) (.slice (.local 74)))).eval
      args e77 state = (.ok (.value (.scalar .unit)), state) := by
    have number := SliceBytesAir.natural_size e77 73 count (by omega) (by simp [e77, e76, e75, e74, e73, Control.Env.set])
    have data := SliceBytesAir.memory_local e77 74 (.slice inputType address length)
      (by simp [e77, e76, e75, e74, Control.Env.set]) (slice_valid false address length bound)
    apply eval_bounds _ _ _ args e77 state 0 count (some length) rfl number
    · simp only [MemoryAir.Bound.eval, data, bind, Except.bind]
    · simp [checkSliceBounds, inside]
  have p78 := slice_construct state args e654 (.local 76) (.local 77) false address count
    (SliceBytesAir.memory_local e654 76 (.pointer (.pointer false true ByteSlice.byte) address)
      (by simp [e654, e77, e76, Control.Env.set]) rfl)
    (SliceBytesAir.natural_size e654 77 count (by omega) (by simp [e654, e77, Control.Env.set]))
    (by simpa only [Nat.add_zero] using reads.make_slice 0 count nonempty (by omega) (by omega))
  rw [generated_source, sourceCode]
  exact AggregateCall.primitive_steps args p73 (SliceBytesAir.size_typed _ (by omega)) <|
    AggregateCall.primitive_steps args p74 (by exact slice_valid false address length bound) <|
    AggregateCall.primitive_steps args p75 rfl <|
    AggregateCall.primitive_steps args p76 rfl <|
    AggregateCall.primitive_steps args p77 (SliceBytesAir.size_typed _ (by omega)) <|
    AggregateCall.primitive_steps args p654 rfl <|
    AggregateCall.primitive_steps args p78 (by exact slice_valid false address count (by omega)) (.refl _)

theorem source_before (env : Env) (address : Address) (length count query : Nat) (earlier : query < 73) :
    sourceEnv env address length count query = env query := by
  simp (disch := omega) only [sourceEnv, Control.Env.set, if_neg]

def copyEnd : Code :=
  .bind 79 usize (.primitive (.memory (.sliceLen (.local 72)))) $
  .bind 80 usize (.primitive (.memory (.sliceLen (.local 78)))) $
  .bind 81 (.pointer false true ByteSlice.byte) (.primitive (.memory (.slicePtr (.local 78)))) $
  .bind 82 (.scalar .unit) (.copyBytes (.local 72) (.local 81)) Round.bufferSite

theorem generated_copy_end : copy.dropBindings 18 = copyEnd := by decide +kernel

theorem copy_end_steps {state : State} {id : Nat} (frame : CellFrame state id)
    (typed : frame.cell.type = objectType) (address : Address) (source cells : Cells)
    (view : ByteSlice.View) (bytes : Nat → BitVec 8) (geometry : ByteSlice.Geometry view)
    (represented : ByteSlice.Represents source view bytes)
    (reads : ByteRange.Reads state address view.length bytes) (apart : address.allocation ≠ id)
    (total length count : Nat) (core : WyhashUpdate.Core cells total)
    (sourceBound : count ≤ view.length) (targetBound : length + count ≤ 48)
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (targetFound : env 72 = some (.value (.slice (.slice true ByteSlice.byte) ⟨id, 56 + length⟩ count)))
    (sourceFound : env 78 = some (.value (.slice inputType address count))) :
    ∃ copied nextEnv, Steps AggregateCall.semantics args (.suspended ⟨copy.dropBindings 18, env, frame.install cells, outer⟩)
        (.suspended ⟨Round.bufferSite, nextEnv, frame.install copied, outer⟩) ∧
      ByteSlice.copy source view (WyhashBuffer.buffer 0 48) 0 length count cells = .ok copied ∧
      WyhashUpdate.Core copied total ∧ (∀ i < count, WyhashUpdate.ByteAt copied (56 + (length + i))) ∧
      (∀ offset, offset < 56 + length ∨ 56 + length + count ≤ offset → copied.lookup offset = cells.lookup offset) ∧
      (∀ query < 79, nextEnv query = env query) := by
  have limit : 48 < addressLimit := by decide
  have bound : count < addressLimit := by omega
  let e79 := env.set 79 (size count)
  let e80 := e79.set 80 (size count)
  let e81 := e80.set 81 (.value (.pointer (.pointer false true ByteSlice.byte) address))
  let next := e81.set 82 (.value (.scalar .unit))
  have p79 := slice_length (frame.install cells) args env 72 true ⟨id, 56 + length⟩ count bound targetFound
  have p80 := slice_length (frame.install cells) args e79 78 false address count bound
    (by simp [e79, Control.Env.set, sourceFound])
  have p81 := slice_pointer (frame.install cells) args e80 78 false address count bound
    (by simp [e80, e79, Control.Env.set, sourceFound])
  obtain ⟨copied, p82, model, nextCore, head, outside⟩ := copy_bytes frame typed address source cells view bytes geometry represented
    reads apart total 0 length count core (by omega) targetBound args e81 72 81
    (by simp [e81, e80, e79, Control.Env.set, targetFound]) (by simp [e81, Control.Env.set])
  refine ⟨copied, next, ?_, model, nextCore, head, outside, ?_⟩
  · rw [generated_copy_end, copyEnd]
    exact AggregateCall.primitive_steps args p79 (SliceBytesAir.size_typed _ bound) <|
      AggregateCall.primitive_steps args p80 (SliceBytesAir.size_typed _ bound) <|
      AggregateCall.primitive_steps args p81 rfl <|
      Steps.bind_ok AggregateCall.semantics args p82 rfl (.refl _)
  · intro query earlier
    simp (disch := omega) only [next, e81, e80, e79, Control.Env.set, if_neg]

end Compiler.ZigAir.WyhashUpdateAir.Fill
