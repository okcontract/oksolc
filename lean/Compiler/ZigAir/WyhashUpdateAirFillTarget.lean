/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirFillIndex

set_option maxRecDepth 8192

namespace Compiler.ZigAir.WyhashUpdateAir.Fill
open Memory AggregateAir Compiler.Extraction Control.Machine

def targetTail : Code :=
  .bind 69 (.pointer true true ByteSlice.byte) (.primitive (.memory (.pointerCast (.pointer true true ByteSlice.byte) (.local 64)))) $
  .bind 70 (.pointer true true ByteSlice.byte) (.primitive (.memory (.offsetPointer false (.local 69) (.local 67)))) $
  .bind 71 usize (.primitive (.memory (.scalar (.arithmetic .add .unchecked (.local 67) (.local 68))))) $
  .bind 653 (.scalar .unit) (.primitive (.memory (.checkBounds (.local 67) (.local 71) (.array 48)))) $
  .bind 72 (.slice true ByteSlice.byte) (.primitive (.memory (.slice (.slice true ByteSlice.byte) (.local 70) (.local 68)))) (copy.dropBindings 11)

def targetHead : Code :=
  .bind 63 (.pointer true false objectType) (.primitive (.load (.local 4))) $
  .bind 64 (.pointer true false (.array 48 ByteSlice.byte)) (.primitive (.fieldPointer (.local 63) 56)) $
  lengthCode 65 (.bind 68 usize (.primitive (.load (.local 50))) targetTail)

theorem generated_target : copy = targetHead := by decide +kernel

def targetHeadEnv (env : Env) (id length count : Nat) : Env :=
  let env := env.set 63 (.value (selfPointer id))
  let env := env.set 64 (.value (.pointer (.pointer true false (.array 48 ByteSlice.byte)) ⟨id, 56⟩))
  (lengthEnv env 65 id length).set 68 (size count)

theorem target_head_steps {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (typed : frame.cell.type = objectType) (length count selfSlot indexSlot : Nat)
    (lengthBound : length < addressLimit) (countBound : count < addressLimit)
    (lengthField : cells.lookup 48 = some (WyhashLocal.word (BitVec.ofNat 64 length)))
    (selfApart : selfSlot ≠ id) (indexApart : indexSlot ≠ id)
    (selfRead : Memory.load state (slot false (.pointer true false objectType) selfSlot) = .ok (selfPointer id))
    (indexRead : Memory.load state (slot true usize indexSlot) = .ok (.scalar (.int false 64 count)))
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (foundSelf : env 4 = some (.value (slot false (.pointer true false objectType) selfSlot)))
    (foundIndex : env 50 = some (.value (slot true usize indexSlot))) :
    Steps AggregateCall.semantics args (.suspended ⟨copy, env, frame.install cells, outer⟩)
      (.suspended ⟨targetTail, targetHeadEnv env id length count, frame.install cells, outer⟩) := by
  let e63 := env.set 63 (.value (selfPointer id))
  let e64 := e63.set 64 (.value (.pointer (.pointer true false (.array 48 ByteSlice.byte)) ⟨id, 56⟩))
  let e67 := lengthEnv e64 65 id length
  have self := load_saved frame cells selfSlot (.pointer true false objectType) 0 _ selfApart selfRead
  have p63 := eval_load (.local 4) args env (frame.install cells) _ _
    (value_local _ _ _ foundSelf rfl) (congrArg (Except.map Register.value) self)
  have p64 := eval_field (.local 63) 56 args e63 (frame.install cells) _ _
    (value_local _ _ _ (by simp [e63, Control.Env.set]) rfl)
    (field_pointer frame cells typed 56 (.array 48 ByteSlice.byte) (by decide))
  have lengths := length_steps frame cells typed length selfSlot 65 lengthBound lengthField selfApart selfRead
    args e64 outer (.bind 68 usize (.primitive (.load (.local 50))) targetTail)
    (by simp [e64, e63, Control.Env.set, foundSelf])
  have index := (frame.load_outside cells ⟨indexSlot, 0⟩ indexApart true false usize).trans indexRead
  have p68 := eval_load (.local 50) args e67 (frame.install cells) (slot true usize indexSlot) (size count)
    (value_local _ _ _ (by simp [e67, lengthEnv, e64, e63, Control.Env.set, foundIndex]) rfl)
    (congrArg (Except.map Register.value) index)
  rw [generated_target, targetHead]
  apply AggregateCall.primitive_steps args p63 rfl
  apply AggregateCall.primitive_steps args p64 rfl
  exact lengths.trans AggregateCall.semantics args (AggregateCall.primitive_steps args p68
    (SliceBytesAir.size_typed _ countBound) (.refl _))

def targetTailEnv (env : Env) (id length count : Nat) : Env :=
  let env := env.set 69 (.value (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56⟩))
  let env := env.set 70 (.value (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56 + length⟩))
  let env := env.set 71 (size (length + count))
  let env := env.set 653 (.value (.scalar .unit))
  env.set 72 (.value (.slice (.slice true ByteSlice.byte) ⟨id, 56 + length⟩ count))

theorem target_tail_steps {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (valid : state.valid = true) (typed : frame.cell.type = objectType) (endBound : frame.cell.base + 104 < addressLimit)
    (length count : Nat) (bounded : length + count ≤ 48)
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (foundBuffer : env 64 = some (.value (.pointer (.pointer true false (.array 48 ByteSlice.byte)) ⟨id, 56⟩)))
    (foundLength : env 67 = some (size length)) (foundCount : env 68 = some (size count)) :
    Steps AggregateCall.semantics args (.suspended ⟨targetTail, env, frame.install cells, outer⟩)
      (.suspended ⟨copy.dropBindings 11, targetTailEnv env id length count, frame.install cells, outer⟩) := by
  have limit : 48 < addressLimit := by decide
  let e69 := env.set 69 (.value (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56⟩))
  let e70 := e69.set 70 (.value (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56 + length⟩))
  let e71 := e70.set 71 (size (length + count))
  let e653 := e71.set 653 (.value (.scalar .unit))
  have p69 : (AggregateAir.Prim.memory (.pointerCast (.pointer true true ByteSlice.byte) (.local 64))).eval
      args env (frame.install cells) = (.ok (.value (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56⟩)), frame.install cells) := by
    apply eval_memory
    have data := SliceBytesAir.memory_local env 64 _ foundBuffer rfl
    simp only [MemoryAir.Prim.eval, MemoryAir.Prim.transition, data,
      buffer_cast frame cells valid typed endBound, bind, Except.bind]
  have p70 := eval_offset (.local 69) (.local 67) args e69 (frame.install cells) _ _ length
    (SliceBytesAir.memory_local e69 69 (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56⟩)
      (by simp [e69, Control.Env.set]) rfl)
    (SliceBytesAir.natural_size e69 67 length (by omega) (by simp [e69, Control.Env.set, foundLength]))
    (buffer_offset frame cells valid typed endBound length (by omega))
  have p71 := size_add (frame.install cells) length count 67 68 args e70 (by omega)
    (by simp [e70, e69, Control.Env.set, foundLength])
    (by simp [e70, e69, Control.Env.set, foundCount])
  have p653 : (AggregateAir.Prim.memory (.checkBounds (.local 67) (.local 71) (.array 48))).eval args e71 (frame.install cells) =
      (.ok (.value (.scalar .unit)), frame.install cells) := by
    apply eval_bounds _ _ _ args e71 (frame.install cells) length (length + count) (some 48)
      (SliceBytesAir.natural_size e71 67 length (by omega) (by simp [e71, e70, e69, Control.Env.set, foundLength]))
      (SliceBytesAir.natural_size e71 71 (length + count) (by omega) (by simp [e71, Control.Env.set])) rfl
    simp [checkSliceBounds, bounded]
  have p72 := slice_construct (frame.install cells) args e653 (.local 70) (.local 68) true ⟨id, 56 + length⟩ count
    (SliceBytesAir.memory_local e653 70 (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56 + length⟩)
      (by simp [e653, e71, e70, Control.Env.set]) rfl)
    (SliceBytesAir.natural_size e653 68 count (by omega) (by simp [e653, e71, e70, e69, Control.Env.set, foundCount]))
    (buffer_slice frame cells valid typed endBound length count bounded)
  exact AggregateCall.primitive_steps args p69 rfl <|
    AggregateCall.primitive_steps args p70 rfl <|
    AggregateCall.primitive_steps args p71 (SliceBytesAir.size_typed _ (by omega)) <|
    AggregateCall.primitive_steps args p653 rfl <|
    AggregateCall.primitive_steps args p72 (by exact slice_valid true ⟨id, 56 + length⟩ count (by omega)) (.refl _)

theorem target_steps {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (valid : state.valid = true) (typed : frame.cell.type = objectType) (endBound : frame.cell.base + 104 < addressLimit)
    (length count selfSlot indexSlot : Nat) (bounded : length + count ≤ 48)
    (lengthField : cells.lookup 48 = some (WyhashLocal.word (BitVec.ofNat 64 length)))
    (selfApart : selfSlot ≠ id) (indexApart : indexSlot ≠ id)
    (selfRead : Memory.load state (slot false (.pointer true false objectType) selfSlot) = .ok (selfPointer id))
    (indexRead : Memory.load state (slot true usize indexSlot) = .ok (.scalar (.int false 64 count)))
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (foundSelf : env 4 = some (.value (slot false (.pointer true false objectType) selfSlot)))
    (foundIndex : env 50 = some (.value (slot true usize indexSlot))) :
    ∃ nextEnv, Steps AggregateCall.semantics args (.suspended ⟨copy, env, frame.install cells, outer⟩)
      (.suspended ⟨copy.dropBindings 11, nextEnv, frame.install cells, outer⟩) ∧
      nextEnv 72 = some (.value (.slice (.slice true ByteSlice.byte) ⟨id, 56 + length⟩ count)) ∧
      ∀ query < 63, nextEnv query = env query := by
  have limit : 48 < addressLimit := by decide
  have head := target_head_steps frame cells typed length count selfSlot indexSlot (by omega) (by omega)
    lengthField selfApart indexApart selfRead indexRead args env outer foundSelf foundIndex
  have tail := target_tail_steps frame cells valid typed endBound length count bounded args
    (targetHeadEnv env id length count) outer (by simp [targetHeadEnv, lengthEnv, Control.Env.set])
    (by simp [targetHeadEnv, lengthEnv, Control.Env.set]) (by simp [targetHeadEnv, Control.Env.set])
  refine ⟨_, head.trans AggregateCall.semantics args tail, ?_, ?_⟩
  · simp [targetTailEnv, Control.Env.set]
  · intro query earlier
    simp (disch := omega) only [targetTailEnv, targetHeadEnv, lengthEnv, Control.Env.set, if_neg]

end Compiler.ZigAir.WyhashUpdateAir.Fill
