/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirSuffixGuard

set_option maxRecDepth 8192

namespace Compiler.ZigAir.WyhashUpdateAir.Suffix
open Memory AggregateAir Compiler.Extraction Control.Machine

def copyAt (count : Nat) : Code := copy.dropBindings count

def targetHead : Code :=
  .bind 607 (.pointer false false usize) (.primitive (.memory (.pointerField true (.local 594)))) $
  .bind 608 usize (.primitive (.load (.local 607))) $
  .bind 609 usize (.primitive (.memory (.scalar (.arithmetic .sub .unchecked (.constant (.int false 64 16)) (.local 608))))) $
  .bind 610 (.pointer true false objectType) (.primitive (.load (.local 4))) $
  .bind 611 (.pointer true false (.array 48 ByteSlice.byte)) (.primitive (.fieldPointer (.local 610) 56)) $
  .bind 612 (.pointer true false objectType) (.primitive (.load (.local 4))) $
  .bind 613 (.pointer true false (.array 48 ByteSlice.byte)) (.primitive (.fieldPointer (.local 612) 56)) $
  .bind 614 usize (.primitive (.memory (.scalar (.arithmetic .sub .unchecked (.constant (.int false 64 48)) (.local 609))))) (copyAt 8)

theorem generated_target_head : copy = targetHead := by decide +kernel

def targetEnv (env : Env) (id restSlot count : Nat) : Env :=
  let env := env.set 607 (.value (.pointer (.pointer false false usize) ⟨restSlot, 8⟩))
  let env := env.set 608 (size count)
  let env := env.set 609 (size (16 - count))
  let env := env.set 610 (.value (selfPointer id))
  let env := env.set 611 (.value (.pointer (.pointer true false (.array 48 ByteSlice.byte)) ⟨id, 56⟩))
  let env := env.set 612 (.value (selfPointer id))
  let env := env.set 613 (.value (.pointer (.pointer true false (.array 48 ByteSlice.byte)) ⟨id, 56⟩))
  env.set 614 (size (48 - (16 - count)))

theorem target_head_steps {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (typed : frame.cell.type = objectType) (count selfSlot restSlot : Nat) (short : count < 16)
    (selfApart : selfSlot ≠ id) (restApart : restSlot ≠ id)
    (selfRead : Memory.load state (slot false (.pointer true false objectType) selfSlot) = .ok (selfPointer id))
    (countRead : Memory.load state (.pointer (.pointer false false usize) ⟨restSlot, 8⟩) = .ok (.scalar (.int false 64 count)))
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (foundSelf : env 4 = some (.value (slot false (.pointer true false objectType) selfSlot)))
    (foundRest : env 594 = some (.value (slot false inputType restSlot))) :
    Steps AggregateCall.semantics args (.suspended ⟨copy, env, frame.install cells, outer⟩)
      (.suspended ⟨copyAt 8, targetEnv env id restSlot count, frame.install cells, outer⟩) := by
  have limit : 48 < addressLimit := by decide
  let e607 := env.set 607 (.value (.pointer (.pointer false false usize) ⟨restSlot, 8⟩))
  let e608 := e607.set 608 (size count)
  let e609 := e608.set 609 (size (16 - count))
  let e610 := e609.set 610 (.value (selfPointer id))
  let e611 := e610.set 611 (.value (.pointer (.pointer true false (.array 48 ByteSlice.byte)) ⟨id, 56⟩))
  let e612 := e611.set 612 (.value (selfPointer id))
  let e613 := e612.set 613 (.value (.pointer (.pointer true false (.array 48 ByteSlice.byte)) ⟨id, 56⟩))
  have self := load_saved frame cells selfSlot (.pointer true false objectType) 0 _ selfApart selfRead
  have countRead' := load_saved frame cells restSlot usize 8 _ restApart countRead
  have p607 := count_pointer (frame.install cells) args env restSlot 594 foundRest
  have p608 := eval_load (.local 607) args e607 (frame.install cells)
    (.pointer (.pointer false false usize) ⟨restSlot, 8⟩) _
    (value_local _ _ _ (by simp [e607, Control.Env.set]) rfl) (congrArg (Except.map Register.value) countRead')
  have p609 := size_sub (frame.install cells) args e608 (.constant (.int false 64 16)) (.local 608) 16 count
    (by omega) (by omega) rfl (SliceBytesAir.scalar_size e608 608 count (by omega) (by simp [e608, Control.Env.set]))
  have p610 := eval_load (.local 4) args e609 (frame.install cells) (slot false (.pointer true false objectType) selfSlot) _
    (value_local _ _ _ (by simp [e609, e608, e607, Control.Env.set, foundSelf]) rfl)
    (congrArg (Except.map Register.value) self)
  have p611 := eval_field (.local 610) 56 args e610 (frame.install cells) _ _
    (value_local _ _ _ (by simp [e610, Control.Env.set]) rfl)
    (field_pointer frame cells typed 56 (.array 48 ByteSlice.byte) (by decide))
  have p612 := eval_load (.local 4) args e611 (frame.install cells) (slot false (.pointer true false objectType) selfSlot) _
    (value_local _ _ _ (by simp [e611, e610, e609, e608, e607, Control.Env.set, foundSelf]) rfl)
    (congrArg (Except.map Register.value) self)
  have p613 := eval_field (.local 612) 56 args e612 (frame.install cells) _ _
    (value_local _ _ _ (by simp [e612, Control.Env.set]) rfl)
    (field_pointer frame cells typed 56 (.array 48 ByteSlice.byte) (by decide))
  have p614 := size_sub (frame.install cells) args e613 (.constant (.int false 64 48)) (.local 609) 48 (16 - count)
    limit (by omega) rfl
    (SliceBytesAir.scalar_size e613 609 (16 - count) (by omega)
      (by simp [e613, e612, e611, e610, e609, Control.Env.set]))
  rw [generated_target_head, targetHead]
  exact AggregateCall.primitive_steps args p607 rfl <|
    AggregateCall.primitive_steps args p608 (SliceBytesAir.size_typed _ (by omega)) <|
    AggregateCall.primitive_steps args p609 (SliceBytesAir.size_typed _ (by omega)) <|
    AggregateCall.primitive_steps args p610 rfl <|
    AggregateCall.primitive_steps args p611 rfl <|
    AggregateCall.primitive_steps args p612 rfl <|
    AggregateCall.primitive_steps args p613 rfl <|
    AggregateCall.primitive_steps args p614 (SliceBytesAir.size_typed _ (by omega)) (.refl _)

def targetTail : Code :=
  .bind 615 (.pointer true true ByteSlice.byte)
    (.primitive (.memory (.pointerCast (.pointer true true ByteSlice.byte) (.local 611)))) $
  .bind 616 (.pointer true true ByteSlice.byte) (.primitive (.memory (.offsetPointer false (.local 615) (.local 614)))) $
  .bind 617 usize (.primitive (.memory (.scalar (.arithmetic .sub .unchecked (.constant (.int false 64 48)) (.local 614))))) $
  .bind 681 (.scalar .unit) (.primitive (.memory (.checkBounds (.local 614) (.constant (.scalar (.int false 64 48))) (.array 48)))) $
  .bind 618 (.slice true ByteSlice.byte) (.primitive (.memory (.slice (.slice true ByteSlice.byte) (.local 616) (.local 617)))) (copyAt 13)

theorem generated_target_tail : copyAt 8 = targetTail := by decide +kernel

def targetTailEnv (env : Env) (id count : Nat) : Env :=
  let env := env.set 615 (.value (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56⟩))
  let env := env.set 616 (.value (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56 + (48 - (16 - count))⟩))
  let env := env.set 617 (size (16 - count))
  let env := env.set 681 (.value (.scalar .unit))
  env.set 618 (.value (.slice (.slice true ByteSlice.byte) ⟨id, 56 + (48 - (16 - count))⟩ (16 - count)))

theorem target_tail_steps {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (valid : state.valid = true) (typed : frame.cell.type = objectType)
    (endBound : frame.cell.base + 104 < addressLimit) (count : Nat) (short : count < 16)
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (foundBuffer : env 611 = some (.value (.pointer (.pointer true false (.array 48 ByteSlice.byte)) ⟨id, 56⟩)))
    (foundOffset : env 614 = some (size (48 - (16 - count)))) :
    Steps AggregateCall.semantics args (.suspended ⟨copyAt 8, env, frame.install cells, outer⟩)
      (.suspended ⟨copyAt 13, targetTailEnv env id count, frame.install cells, outer⟩) := by
  have limit : 48 < addressLimit := by decide
  let e615 := env.set 615 (.value (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56⟩))
  let e616 := e615.set 616 (.value (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56 + (48 - (16 - count))⟩))
  let e617 := e616.set 617 (size (16 - count))
  let e681 := e617.set 681 (.value (.scalar .unit))
  have p615 : (AggregateAir.Prim.memory (.pointerCast (.pointer true true ByteSlice.byte) (.local 611))).eval
      args env (frame.install cells) =
      (.ok (.value (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56⟩)), frame.install cells) := by
    apply eval_memory
    have data := SliceBytesAir.memory_local env 611 _ foundBuffer rfl
    simp only [MemoryAir.Prim.eval, MemoryAir.Prim.transition, data,
      buffer_cast frame cells valid typed endBound, bind, Except.bind]
  have p616 := eval_offset (.local 615) (.local 614) args e615 (frame.install cells) _ _ (48 - (16 - count))
    (SliceBytesAir.memory_local e615 615 (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56⟩)
      (by simp [e615, Control.Env.set]) rfl)
    (SliceBytesAir.natural_size e615 614 (48 - (16 - count)) (by omega) (by simp [e615, Control.Env.set, foundOffset]))
    (buffer_offset frame cells valid typed endBound _ (by omega))
  have p617 := size_sub (frame.install cells) args e616 (.constant (.int false 64 48)) (.local 614)
    48 (48 - (16 - count)) limit (by omega) rfl
    (SliceBytesAir.scalar_size e616 614 _ (by omega) (by simp [e616, e615, Control.Env.set, foundOffset]))
  have distance : 48 - (48 - (16 - count)) = 16 - count := by omega
  rw [distance] at p617
  have p681 : (AggregateAir.Prim.memory (.checkBounds (.local 614) (.constant (.scalar (.int false 64 48))) (.array 48))).eval
      args e617 (frame.install cells) = (.ok (.value (.scalar .unit)), frame.install cells) := by
    apply eval_bounds _ _ _ args e617 (frame.install cells) (48 - (16 - count)) 48 (some 48)
      (SliceBytesAir.natural_size e617 614 _ (by omega) (by simp [e617, e616, e615, Control.Env.set, foundOffset])) rfl rfl
    simp [checkSliceBounds]
  have p618 := slice_construct (frame.install cells) args e681 (.local 616) (.local 617) true
    ⟨id, 56 + (48 - (16 - count))⟩ (16 - count)
    (SliceBytesAir.memory_local e681 616
      (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56 + (48 - (16 - count))⟩)
      (by simp [e681, e617, e616, Control.Env.set]) rfl)
    (SliceBytesAir.natural_size e681 617 (16 - count) (by omega) (by simp [e681, e617, Control.Env.set]))
    (buffer_slice frame cells valid typed endBound (48 - (16 - count)) (16 - count) (by omega))
  rw [generated_target_tail, targetTail]
  exact AggregateCall.primitive_steps args p615 rfl <|
    AggregateCall.primitive_steps args p616 rfl <|
    AggregateCall.primitive_steps args p617 (SliceBytesAir.size_typed _ (by omega)) <|
    AggregateCall.primitive_steps args p681 rfl <|
    AggregateCall.primitive_steps args p618
      (by exact slice_valid true ⟨id, 56 + (48 - (16 - count))⟩ (16 - count) (by omega)) (.refl _)

theorem target_steps {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (valid : state.valid = true) (typed : frame.cell.type = objectType)
    (endBound : frame.cell.base + 104 < addressLimit) (count selfSlot restSlot : Nat) (short : count < 16)
    (selfApart : selfSlot ≠ id) (restApart : restSlot ≠ id)
    (selfRead : Memory.load state (slot false (.pointer true false objectType) selfSlot) = .ok (selfPointer id))
    (countRead : Memory.load state (.pointer (.pointer false false usize) ⟨restSlot, 8⟩) = .ok (.scalar (.int false 64 count)))
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (foundSelf : env 4 = some (.value (slot false (.pointer true false objectType) selfSlot)))
    (foundRest : env 594 = some (.value (slot false inputType restSlot))) :
    ∃ nextEnv, Steps AggregateCall.semantics args (.suspended ⟨copy, env, frame.install cells, outer⟩)
        (.suspended ⟨copyAt 13, nextEnv, frame.install cells, outer⟩) ∧
      nextEnv 609 = some (size (16 - count)) ∧
      nextEnv 618 = some (.value (.slice (.slice true ByteSlice.byte) ⟨id, 56 + (48 - (16 - count))⟩ (16 - count))) ∧
      ∀ query < 607, nextEnv query = env query := by
  have head := target_head_steps frame cells typed count selfSlot restSlot short selfApart restApart
    selfRead countRead args env outer foundSelf foundRest
  have tail := target_tail_steps frame cells valid typed endBound count short args (targetEnv env id restSlot count) outer
    (by simp [targetEnv, Control.Env.set]) (by simp [targetEnv, Control.Env.set])
  refine ⟨_, head.trans AggregateCall.semantics args tail, ?_, ?_, ?_⟩
  · simp [targetTailEnv, targetEnv, Control.Env.set]
  · simp [targetTailEnv, Control.Env.set]
  · intro query earlier
    simp (disch := omega) only [targetTailEnv, targetEnv, Control.Env.set, if_neg]

end Compiler.ZigAir.WyhashUpdateAir.Suffix
