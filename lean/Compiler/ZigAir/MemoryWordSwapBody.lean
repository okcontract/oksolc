/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.GeneratedWordSwap
import Compiler.ZigAir.MemoryByteInvocation
import Compiler.ZigAir.MemoryByteExchange

/-! Functional refinement of the finite conditional in the captured u32 swap
loop. The projection is checked against the generated body; it cannot erase a
backedge. The surrounding counter loop and invocation are proved separately. -/
namespace Compiler.ZigAir.MemoryWordSwap
open Memory MemoryAir GeneratedMemory
open Memory.WordArray (View Writable Represents Frame word)
open MemoryFill (size size_valid size_typed scalar_read_size cast_size_eval less_size_eval unitRef counter)
open MemoryByteInvocation (pointer_valid pointer_typed byte_pointer_valid byte_pointer_typed byte_slice_valid)

def lane : Code :=
  .bind 18 (.pointer true false ByteAccess.byte) (.sliceElementPointer (.local 4) (.local 13))
    (.bind 19 (.pointer true false ByteAccess.byte) (.sliceElementPointer (.local 6) (.local 13))
      (.bind 20 ByteAccess.byte (.wordByteLoad .little (.local 18))
        (.bind 21 ByteAccess.byte (.wordByteLoad .little (.local 19))
          (.bind 22 (.scalar .unit) (.wordByteStore .little (.local 18) (.local 21))
            (.bind 23 (.scalar .unit) (.wordByteStore .little (.local 19) (.local 20)) (.jump 14 unitRef))))))

def condition (yes no : Code) : Code :=
  .bind 15 usize (.scalar (.cast .bitcast (.int false 64) (.local 13)))
    (.bind 16 usize (.scalar (.cast .bitcast (.int false 64) (.local 9)))
      (.bind 17 (.scalar .bool) (.scalar (.comparison .lt (.local 15) (.local 16)))
        (.branch (.local 17) yes no)))

def head : Code := condition lane (.jump 11 unitRef)

def conditionEnv (env : Env) (index : Nat) : Env :=
  ((env.set 15 (size index)).set 16 (size 4)).set 17 (.scalar (.bool (decide (index < 4))))

theorem generated_head : fn_swap_u32.program.body.blockBody? 14 = some head.enableLoops := rfl
theorem head_shape : head = condition lane (.jump 11 unitRef) := rfl

theorem condition_eval (yes no : Code) (args : List Value) (env : Env) (state : State) (index : Nat)
    (h13 : env 13 = some (size index)) (h9 : env 9 = some (size 4)) (bound : index < addressLimit) :
    (condition yes no).eval semantics args env state =
      (if index < 4 then yes else no).eval semantics args (conditionEnv env index) state := by
  have four : 4 < addressLimit := by decide
  have castIndex := cast_size_eval (.local 13) args env state index bound
    (scalar_read_size env 13 index bound h13)
  have castFour := cast_size_eval (.local 9) args (env.set 15 (size index)) state 4 four
    (scalar_read_size _ 9 4 four (by simpa [Control.Env.set] using h9))
  have compare := less_size_eval (.local 15) (.local 16) args
    ((env.set 15 (size index)).set 16 (size 4)) state index 4
    (scalar_read_size _ 15 index bound (by simp [Control.Env.set]))
    (scalar_read_size _ 16 4 four (by simp [Control.Env.set]))
  have boolTyped (flag : Bool) : (Value.scalar (.bool flag)).hasType (.scalar .bool) = true := rfl
  unfold condition
  rw [Code.eval_bind_ok castIndex (size_typed index bound), Code.eval_bind_ok castFour (size_typed 4 four),
    Code.eval_bind_ok compare (boolTyped _)]
  have readFlag : (Ref.local 17).eval (conditionEnv env index) =
      .ok (.scalar (.bool (decide (index < 4)))) := by rfl
  change (Control.Code.branch (.local 17) yes no).eval semantics args (conditionEnv env index) state = _
  rw [Code.eval_branch_bool readFlag]
  simp only [decide_eq_true_eq]

def Locals (env : Env) (view : View) (left right : Nat) (slot : Address) : Prop :=
  env 4 = some (ByteAccess.slice true (view.address left)) ∧
  env 6 = some (ByteAccess.slice true (view.address right)) ∧
  env 7 = some (counter slot) ∧ env 9 = some (size 4)

theorem condition_locals (env : Env) (view : View) (left right index : Nat) (slot : Address)
    (locals : Locals env view left right slot) : Locals (conditionEnv env index) view left right slot := by
  simpa [Locals, conditionEnv, Control.Env.set] using locals

def laneEnv (env : Env) (view : View) (left right : Nat) (index : Fin 4) (a b : BitVec 8) : Env :=
  (((((env.set 18 (ByteAccess.pointer true false (ByteAccess.atByte (view.address left) index))).set
    19 (ByteAccess.pointer true false (ByteAccess.atByte (view.address right) index))).set
    20 (ByteAccess.number a)).set 21 (ByteAccess.number b)).set 22 (.scalar .unit)).set 23 (.scalar .unit)

theorem lane_locals (env : Env) (view : View) (left right : Nat) (slot : Address) (index : Fin 4) (a b : BitVec 8)
    (locals : Locals env view left right slot) : Locals (laneEnv env view left right index a b) view left right slot := by
  simpa [Locals, laneEnv, Control.Env.set] using locals

/-- The exact two reads and ordered writes in the generated lane implement the
existing byte-exchange effect, including its intermediate state. -/
theorem lane_of_effects (args : List Value) (env : Env) (state middle after : State) (view : View)
    (left right : Nat) (index : Fin 4) (a b : BitVec 8)
    (initial : state.valid = true) (cap : Writable state view) (hl : left < view.length) (hr : right < view.length)
    (h4 : env 4 = some (ByteAccess.slice true (view.address left)))
    (h6 : env 6 = some (ByteAccess.slice true (view.address right))) (h13 : env 13 = some (size index.val))
    (readLeft : WordByteView.read .little state (view.pointer left) index.val = .ok a)
    (readRight : WordByteView.read .little state (view.pointer right) index.val = .ok b)
    (writeLeft : WordByteView.write .little state (view.pointer left) index.val b = .ok middle)
    (writeRight : WordByteView.write .little middle (view.pointer right) index.val a = .ok after) :
    lane.eval semantics args env state = .jumped 14 (.scalar .unit) (laneEnv env view left right index a b) after := by
  have elementLeft := ByteAccess.byte_element state view left index true initial cap hl
  have elementRight := ByteAccess.byte_element state view right index true initial cap hr
  have alignedLeft : (view.address left).offset % 4 = 0 := by simp [View.address]
  have alignedRight : (view.address right).offset % 4 = 0 := by simp [View.address]
  have firstRead := ByteAccess.read_atByte .little state (view.address left) index true false alignedLeft
  have secondRead := ByteAccess.read_atByte .little state (view.address right) index true false alignedRight
  have firstWrite := ByteAccess.write_atByte .little state (view.address left) index true false b alignedLeft
  have secondWrite := ByteAccess.write_atByte .little middle (view.address right) index true false a alignedRight
  simp only [View.pointer] at readLeft readRight writeLeft writeRight
  rw [readLeft] at firstRead
  rw [readRight] at secondRead
  rw [writeLeft] at firstWrite
  rw [writeRight] at secondWrite
  have bound : index.val < addressLimit := by
    have := index.isLt
    have : 4 < addressLimit := by decide
    omega
  have unitTyped : (Value.scalar .unit).hasType (.scalar .unit) = true := rfl
  have indexValid := size_valid index.val bound
  simp only [size] at indexValid
  simp only [lane, Code.eval_bind, Prim.eval_slice_element, Prim.eval_word_byte_load,
    Prim.eval_word_byte_store, Ref.eval_local, Ref.natural_eq, h4, h6, h13,
    byte_slice_valid, size, indexValid, ↓reduceIte, bind, Except.bind, Int.toNat_natCast,
    elementLeft, elementRight, byte_pointer_valid, byte_pointer_typed, Control.Env.set, Nat.reduceEqDiff,
    firstRead, secondRead, ByteAccess.number_valid, ByteAccess.number_typed,
    firstWrite, secondWrite, Code.eval_jump, laneEnv, unitTyped]
  rfl

theorem lane_refines (args : List Value) (env : Env) (state : State) (view : View) (items : List (BitVec 32))
    (left right : Nat) (index : Fin 4) (slot : Address)
    (initial : state.valid = true) (cap : Writable state view) (represented : Represents state view items)
    (hl : left < items.length) (hr : right < items.length) (apart : left ≠ right)
    (locals : Locals env view left right slot) (h13 : env 13 = some (size index.val)) :
    ∃ after nextEnv, lane.eval semantics args env state = .jumped 14 (.scalar .unit) nextEnv after ∧
      Locals nextEnv view left right slot ∧ nextEnv 13 = some (size index.val) ∧
      ByteExchange.step .little state view left right index = (.ok (), after) ∧
      after.valid = true ∧ Writable after view ∧
      Represents after view (ByteExchange.updated items left right (WordBytes.exchangeLane .little (items[left], items[right]) index)) ∧
      Frame view state after := by
  obtain ⟨after, ran, valid, writable, rep, frame⟩ :=
    ByteExchange.step_refines .little state view items left right index initial cap represented hl hr apart
  obtain ⟨a, b, middle, first, second, third, fourth⟩ :=
    ByteExchange.step_effects .little state after view left right index ran
  refine ⟨after, laneEnv env view left right index a b, ?_, lane_locals env view left right slot index a b locals,
    ?_, ran, valid, writable, rep, frame⟩
  · exact lane_of_effects args env state middle after view left right index a b initial cap
      (by simpa only [represented.1] using hl) (by simpa only [represented.1] using hr)
      locals.1 locals.2.1 h13 first second third fourth
  · simpa [laneEnv, Control.Env.set] using h13

end Compiler.ZigAir.MemoryWordSwap
