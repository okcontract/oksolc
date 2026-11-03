/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirIndex

namespace Compiler.ZigAir.WyhashUpdateAir.Fill
open Memory AggregateAir Compiler.Extraction Control.Machine
abbrev Code := Round.Code

/-- The guard and fill preparation repeat this actual self/field/load sequence. -/
def lengthCode (base : Nat) (next : Code) : Code :=
  .bind base (.pointer true false objectType) (.primitive (.load (.local 4))) $
  .bind (base + 1) (.pointer true false usize) (.primitive (.fieldPointer (.local base) 48)) $
  .bind (base + 2) usize (.primitive (.load (.local (base + 1)))) next

def lengthEnv (env : Env) (base id length : Nat) : Env :=
  ((env.set base (.value (selfPointer id))).set (base + 1)
    (.value (.pointer (.pointer true false usize) ⟨id, 48⟩))).set (base + 2) (size length)

theorem length_steps {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (typed : frame.cell.type = objectType) (length selfSlot base : Nat) (bound : length < addressLimit)
    (lengthField : cells.lookup 48 = some (WyhashLocal.word (BitVec.ofNat 64 length)))
    (selfApart : selfSlot ≠ id)
    (selfRead : Memory.load state (slot false (.pointer true false objectType) selfSlot) = .ok (selfPointer id))
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref)) (next : Code)
    (foundSelf : env 4 = some (.value (slot false (.pointer true false objectType) selfSlot))) :
    Steps AggregateCall.semantics args (.suspended ⟨lengthCode base next, env, frame.install cells, outer⟩)
      (.suspended ⟨next, lengthEnv env base id length, frame.install cells, outer⟩) := by
  let first := env.set base (.value (selfPointer id))
  let second := first.set (base + 1) (.value (.pointer (.pointer true false usize) ⟨id, 48⟩))
  have loaded := load_saved frame cells selfSlot (.pointer true false objectType) 0 _ selfApart selfRead
  have pSelf := eval_load (.local 4) args env (frame.install cells) _ _
    (value_local _ _ _ foundSelf rfl) (congrArg (Except.map Register.value) loaded)
  have pField := eval_field (.local base) 48 args first (frame.install cells) _ _
    (value_local _ _ _ (by simp [first, Control.Env.set]) rfl)
    (field_pointer frame cells typed 48 usize (by decide))
  have read := WyhashInit.object_word_read frame cells typed 48 (by decide) (BitVec.ofNat 64 length) lengthField
  have wordBound : length < 2 ^ 64 := bound
  simp only [WyhashLocal.word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt wordBound] at read
  have pLength := eval_load (.local (base + 1)) args second (frame.install cells)
    (.pointer (.pointer true false usize) ⟨id, 48⟩) (size length)
    (value_local _ _ _ (by simp [second, Control.Env.set]) rfl) (congrArg (Except.map Register.value) read)
  exact AggregateCall.primitive_steps args pSelf rfl <|
    AggregateCall.primitive_steps args pField rfl <|
    AggregateCall.primitive_steps args pLength (SliceBytesAir.size_typed _ bound) (.refl _)

theorem length_before (env : Env) (base id length query : Nat) (earlier : query < base) :
    lengthEnv env base id length query = env query := by
  simp (disch := omega) only [lengthEnv, Control.Env.set, if_neg]

def skip : Code := .jump 52 (.constant (.value (.scalar .unit)))

def decision : Code :=
  .bind 56 usize (.primitive (.memory (.scalar (.cast .bitcast (.int false 64) (.local 55))))) $
  .bind 57 (.scalar .bool) (.primitive (.memory (.scalar (.comparison .gt (.local 56) (.constant (.int false 64 0)))))) $
  .branch (.local 57) Round.fillBody skip

theorem generated_guard : Index.guard = lengthCode 53 decision := by decide +kernel

def guardEnv (env : Env) (id length : Nat) : Env :=
  ((lengthEnv env 53 id length).set 56 (size length)).set 57 (.value (.scalar (.bool (decide (0 < length)))))

theorem guard_steps {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (typed : frame.cell.type = objectType) (length selfSlot : Nat) (bound : length < addressLimit)
    (lengthField : cells.lookup 48 = some (WyhashLocal.word (BitVec.ofNat 64 length)))
    (selfApart : selfSlot ≠ id)
    (selfRead : Memory.load state (slot false (.pointer true false objectType) selfSlot) = .ok (selfPointer id))
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (foundSelf : env 4 = some (.value (slot false (.pointer true false objectType) selfSlot))) :
    Steps AggregateCall.semantics args (.suspended ⟨Index.guard, env, frame.install cells, outer⟩)
      (.suspended ⟨if 0 < length then Round.fillBody else skip, guardEnv env id length, frame.install cells, outer⟩) := by
  have head := length_steps frame cells typed length selfSlot 53 bound lengthField selfApart selfRead
    args env outer decision foundSelf
  rw [← generated_guard] at head
  let loaded := lengthEnv env 53 id length
  let casted := loaded.set 56 (size length)
  have p56 := size_bitcast (frame.install cells) args loaded 55 length bound (by simp [loaded, lengthEnv, Control.Env.set])
  have p57 := size_comparison (frame.install cells) args casted .gt (.local 56) (.constant (.int false 64 0)) length 0
    (SliceBytesAir.scalar_size casted 56 length bound (by simp [casted, Control.Env.set])) rfl
  simp only [Scalar.Comparison.eval, Int.ofNat_lt] at p57
  have selected := Loop.branch_steps Round.fillBody skip (frame.install cells) args (guardEnv env id length) outer
    57 (decide (0 < length)) (by simp [guardEnv, Control.Env.set])
  have tail : Steps AggregateCall.semantics args (.suspended ⟨decision, loaded, frame.install cells, outer⟩)
      (.suspended ⟨if 0 < length then Round.fillBody else skip, guardEnv env id length, frame.install cells, outer⟩) :=
    AggregateCall.primitive_steps args p56 (SliceBytesAir.size_typed _ bound) <|
      AggregateCall.primitive_steps args p57 rfl (by simpa only [decide_eq_true_eq] using selected)
  exact head.trans AggregateCall.semantics args tail

theorem guard_before (env : Env) (id length query : Nat) (earlier : query < 53) :
    guardEnv env id length query = env query := by
  simp (disch := omega) only [guardEnv, lengthEnv, Control.Env.set, if_neg]

end Compiler.ZigAir.WyhashUpdateAir.Fill
