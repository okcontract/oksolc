/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirSuffixTarget

set_option maxRecDepth 8192

namespace Compiler.ZigAir.WyhashUpdateAir.Suffix
open Memory AggregateAir Compiler.Extraction Control.Machine

def sourceHead : Code :=
  .bind 619 usize (.primitive (.load (.local 50))) $
  .bind 620 usize (.primitive (.memory (.scalar (.arithmetic .sub .unchecked (.local 619) (.local 609))))) $
  .bind 621 usize (.primitive (.load (.local 50))) $
  .bind 622 inputType (.primitive (.load (.local 7))) $
  .bind 623 (.pointer false true ByteSlice.byte) (.primitive (.memory (.slicePtr (.local 622)))) $
  .bind 624 (.pointer false true ByteSlice.byte)
    (.primitive (.memory (.offsetPointer false (.local 623) (.local 620)))) (copyAt 19)

theorem generated_source_head : copyAt 13 = sourceHead := by decide +kernel

def sourceEnv (env : Env) (address : Address) (index count missing : Nat) : Env :=
  let env := env.set 619 (size index)
  let env := env.set 620 (size (index - missing))
  let env := env.set 621 (size index)
  let env := env.set 622 (.value (.slice inputType address count))
  let env := env.set 623 (.value (.pointer (.pointer false true ByteSlice.byte) address))
  env.set 624 (.value (.pointer (.pointer false true ByteSlice.byte)
    ⟨address.allocation, address.offset + (index - missing)⟩))

theorem source_head_steps (state : State) (address : Address) (index count missing inputSlot indexSlot : Nat)
    (bytes : Nat → BitVec 8) (reads : ByteRange.Reads state address count bytes)
    (inside : index < count) (bounded : missing ≤ index) (bound : count < addressLimit)
    (inputRead : Memory.load state (slot false inputType inputSlot) = .ok (.slice inputType address count))
    (indexRead : Memory.load state (slot true usize indexSlot) = .ok (.scalar (.int false 64 index)))
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (foundInput : env 7 = some (.value (slot false inputType inputSlot)))
    (foundIndex : env 50 = some (.value (slot true usize indexSlot)))
    (foundMissing : env 609 = some (size missing)) :
    Steps AggregateCall.semantics args (.suspended ⟨copyAt 13, env, state, outer⟩)
      (.suspended ⟨copyAt 19, sourceEnv env address index count missing, state, outer⟩) := by
  let e619 := env.set 619 (size index)
  let e620 := e619.set 620 (size (index - missing))
  let e621 := e620.set 621 (size index)
  let e622 := e621.set 622 (.value (.slice inputType address count))
  let e623 := e622.set 623 (.value (.pointer (.pointer false true ByteSlice.byte) address))
  have p619 := eval_load (.local 50) args env state _ _ (value_local _ _ _ foundIndex rfl)
    (congrArg (Except.map Register.value) indexRead)
  have p620 := size_sub state args e619 (.local 619) (.local 609) index missing (by omega) bounded
    (SliceBytesAir.scalar_size e619 619 index (by omega) (by simp [e619, Control.Env.set]))
    (SliceBytesAir.scalar_size e619 609 missing (by omega) (by simp [e619, Control.Env.set, foundMissing]))
  have p621 := eval_load (.local 50) args e620 state (slot true usize indexSlot) _
    (value_local _ _ _ (by simp [e620, e619, Control.Env.set, foundIndex]) rfl)
    (congrArg (Except.map Register.value) indexRead)
  have p622 := eval_load (.local 7) args e621 state (slot false inputType inputSlot) _
    (value_local _ _ _ (by simp [e621, e620, e619, Control.Env.set, foundInput]) rfl)
    (congrArg (Except.map Register.value) inputRead)
  have p623 := slice_pointer state args e622 622 false address count bound (by simp [e622, Control.Env.set])
  have p624 := eval_offset (.local 623) (.local 620) args e623 state _ _ (index - missing)
    (SliceBytesAir.memory_local e623 623 (.pointer (.pointer false true ByteSlice.byte) address)
      (by simp [e623, Control.Env.set]) rfl)
    (SliceBytesAir.natural_size e623 620 _ (by omega) (by simp [e623, e622, e621, e620, Control.Env.set]))
    (by simpa only [Nat.add_zero, Nat.zero_add] using reads.offset_pointer 0 (index - missing) (by omega) (by omega))
  rw [generated_source_head, sourceHead]
  exact AggregateCall.primitive_steps args p619 (SliceBytesAir.size_typed _ (by omega)) <|
    AggregateCall.primitive_steps args p620 (SliceBytesAir.size_typed _ (by omega)) <|
    AggregateCall.primitive_steps args p621 (SliceBytesAir.size_typed _ (by omega)) <|
    AggregateCall.primitive_steps args p622 (by exact slice_valid false address count bound) <|
    AggregateCall.primitive_steps args p623 rfl <|
    AggregateCall.primitive_steps args p624 rfl (.refl _)

def sourceTail : Code :=
  .bind 625 usize (.primitive (.memory (.scalar (.arithmetic .sub .unchecked (.local 621) (.local 620))))) $
  .bind 682 (.scalar .unit) (.primitive (.memory (.checkBounds (.local 620) (.local 621) (.slice (.local 622))))) $
  .bind 626 inputType (.primitive (.memory (.slice inputType (.local 624) (.local 625)))) (copyAt 22)

theorem generated_source_tail : copyAt 19 = sourceTail := by decide +kernel

def sourceTailEnv (env : Env) (address : Address) (index missing : Nat) : Env :=
  let env := env.set 625 (size missing)
  let env := env.set 682 (.value (.scalar .unit))
  env.set 626 (.value (.slice inputType ⟨address.allocation, address.offset + (index - missing)⟩ missing))

theorem source_tail_steps (state : State) (address : Address) (index count missing : Nat)
    (bytes : Nat → BitVec 8) (reads : ByteRange.Reads state address count bytes)
    (inside : index < count) (bounded : missing ≤ index) (bound : count < addressLimit)
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (h620 : env 620 = some (size (index - missing))) (h621 : env 621 = some (size index))
    (h622 : env 622 = some (.value (.slice inputType address count)))
    (h624 : env 624 = some (.value (.pointer (.pointer false true ByteSlice.byte)
      ⟨address.allocation, address.offset + (index - missing)⟩))) :
    Steps AggregateCall.semantics args (.suspended ⟨copyAt 19, env, state, outer⟩)
      (.suspended ⟨copyAt 22, sourceTailEnv env address index missing, state, outer⟩) := by
  let e625 := env.set 625 (size missing)
  let e682 := e625.set 682 (.value (.scalar .unit))
  have p625 := size_sub state args env (.local 621) (.local 620) index (index - missing) (by omega) (by omega)
    (SliceBytesAir.scalar_size env 621 index (by omega) h621)
    (SliceBytesAir.scalar_size env 620 _ (by omega) h620)
  have distance : index - (index - missing) = missing := by omega
  rw [distance] at p625
  have p682 : (AggregateAir.Prim.memory (.checkBounds (.local 620) (.local 621) (.slice (.local 622)))).eval args e625 state =
      (.ok (.value (.scalar .unit)), state) := by
    have first := SliceBytesAir.natural_size e625 620 (index - missing) (by omega) (by simp [e625, Control.Env.set, h620])
    have last := SliceBytesAir.natural_size e625 621 index (by omega) (by simp [e625, Control.Env.set, h621])
    have data := SliceBytesAir.memory_local e625 622 (.slice inputType address count)
      (by simp [e625, Control.Env.set, h622]) (slice_valid false address count bound)
    apply eval_bounds _ _ _ args e625 state (index - missing) index (some count) first last
    · simp only [MemoryAir.Bound.eval, data, bind, Except.bind]
    · simp [checkSliceBounds, Nat.le_of_lt inside]
  have p626 := slice_construct state args e682 (.local 624) (.local 625) false
    ⟨address.allocation, address.offset + (index - missing)⟩ missing
    (SliceBytesAir.memory_local e682 624
      (.pointer (.pointer false true ByteSlice.byte) ⟨address.allocation, address.offset + (index - missing)⟩)
      (by simp [e682, e625, Control.Env.set, h624]) rfl)
    (SliceBytesAir.natural_size e682 625 missing (by omega) (by simp [e682, e625, Control.Env.set]))
    (reads.make_slice (index - missing) missing (by omega) (by omega) (by omega))
  rw [generated_source_tail, sourceTail]
  exact AggregateCall.primitive_steps args p625 (SliceBytesAir.size_typed _ (by omega)) <|
    AggregateCall.primitive_steps args p682 rfl <|
    AggregateCall.primitive_steps args p626
      (by exact slice_valid false ⟨address.allocation, address.offset + (index - missing)⟩ missing (by omega)) (.refl _)

theorem source_steps (state : State) (address : Address) (index count missing inputSlot indexSlot : Nat)
    (bytes : Nat → BitVec 8) (reads : ByteRange.Reads state address count bytes)
    (inside : index < count) (bounded : missing ≤ index) (bound : count < addressLimit)
    (inputRead : Memory.load state (slot false inputType inputSlot) = .ok (.slice inputType address count))
    (indexRead : Memory.load state (slot true usize indexSlot) = .ok (.scalar (.int false 64 index)))
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (foundInput : env 7 = some (.value (slot false inputType inputSlot)))
    (foundIndex : env 50 = some (.value (slot true usize indexSlot)))
    (foundMissing : env 609 = some (size missing)) :
    ∃ nextEnv, Steps AggregateCall.semantics args (.suspended ⟨copyAt 13, env, state, outer⟩)
        (.suspended ⟨copyAt 22, nextEnv, state, outer⟩) ∧
      nextEnv 626 = some (.value (.slice inputType ⟨address.allocation, address.offset + (index - missing)⟩ missing)) ∧
      ∀ query < 619, nextEnv query = env query := by
  have head := source_head_steps state address index count missing inputSlot indexSlot bytes reads inside bounded bound
    inputRead indexRead args env outer foundInput foundIndex foundMissing
  have tail := source_tail_steps state address index count missing bytes reads inside bounded bound args
    (sourceEnv env address index count missing) outer
    (by simp [sourceEnv, Control.Env.set]) (by simp [sourceEnv, Control.Env.set])
    (by simp [sourceEnv, Control.Env.set]) (by simp [sourceEnv, Control.Env.set])
  refine ⟨_, head.trans AggregateCall.semantics args tail, ?_, ?_⟩
  · simp [sourceTailEnv, Control.Env.set]
  · intro query earlier
    simp (disch := omega) only [sourceTailEnv, sourceEnv, Control.Env.set, if_neg]

end Compiler.ZigAir.WyhashUpdateAir.Suffix
