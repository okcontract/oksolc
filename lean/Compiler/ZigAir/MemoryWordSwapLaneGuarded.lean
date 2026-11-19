/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryWordSwapFootprint

namespace Compiler.ZigAir.MemoryWordSwap
open Memory MemoryAir Control.Machine
open Memory.WordArray (View Writable Represents)
open MemoryFill (size size_valid size_typed counter unitRef)
open MemoryByteInvocation (byte_pointer_valid byte_pointer_typed byte_slice_valid)

theorem left_borrow (view : View) (left right : Nat) (env : Env) (index : Fin 4)
    (found : env 18 = some (ByteAccess.pointer true false (ByteAccess.atByte (view.address left) index))) :
    ByteBorrow view left right env (.local 18) := by
  refine ⟨index, Or.inl ⟨rfl, ?_⟩⟩
  simp only [Ref.eval_local, found, byte_pointer_valid, ↓reduceIte]

theorem right_borrow (view : View) (left right : Nat) (env : Env) (index : Fin 4)
    (found : env 19 = some (ByteAccess.pointer true false (ByteAccess.atByte (view.address right) index))) :
    ByteBorrow view left right env (.local 19) := by
  refine ⟨index, Or.inr ⟨rfl, ?_⟩⟩
  simp only [Ref.eval_local, found, byte_pointer_valid, ↓reduceIte]

theorem lane_guarded_of_effects (args : List Value) (env : Env) (state middle after : State) (view : View)
    (left right : Nat) (index : Fin 4) (slot : Address) (a b : BitVec 8) (frames : List (Control.Machine.Frame Ty Prim Ref))
    (initial : state.valid = true) (cap : Writable state view) (hl : left < view.length) (hr : right < view.length)
    (h4 : env 4 = some (ByteAccess.slice true (view.address left)))
    (h6 : env 6 = some (ByteAccess.slice true (view.address right))) (h13 : env 13 = some (size index.val))
    (readLeft : WordByteView.read .little state (view.pointer left) index.val = .ok a)
    (readRight : WordByteView.read .little state (view.pointer right) index.val = .ok b)
    (writeLeft : WordByteView.write .little state (view.pointer left) index.val b = .ok middle)
    (writeRight : WordByteView.write .little middle (view.pointer right) index.val a = .ok after) :
    GuardedSteps semantics args (Footprint view left right slot)
      (.suspended ⟨lane.enableLoops, env, state, frames⟩)
      (jump semantics 14 (.scalar .unit) (laneEnv env view left right index a b) after frames) := by
  let leftPtr := ByteAccess.pointer true false (ByteAccess.atByte (view.address left) index)
  let rightPtr := ByteAccess.pointer true false (ByteAccess.atByte (view.address right) index)
  let leftEnv := env.set 18 leftPtr
  let rightEnv := leftEnv.set 19 rightPtr
  let firstEnv := rightEnv.set 20 (ByteAccess.number a)
  let secondEnv := firstEnv.set 21 (ByteAccess.number b)
  let writtenEnv := secondEnv.set 22 (.scalar .unit)
  have bound : index.val < addressLimit := by
    have := index.isLt
    have : 4 < addressLimit := by decide
    omega
  have indexValid := size_valid index.val bound
  simp only [size] at indexValid
  have elementLeft : (Prim.sliceElementPointer (.local 4) (.local 13)).eval args env state = (.ok leftPtr, state) := by
    simp only [Prim.eval_slice_element, Ref.eval_local, Ref.natural_eq, h4, h13, byte_slice_valid,
      indexValid, ↓reduceIte, size, bind, Except.bind, Int.toNat_natCast]
    rw [ByteAccess.byte_element state view left index true initial cap hl]
  have elementRight : (Prim.sliceElementPointer (.local 6) (.local 13)).eval args leftEnv state = (.ok rightPtr, state) := by
    simp only [Prim.eval_slice_element, Ref.eval_local, Ref.natural_eq, leftEnv, Control.Env.set,
      Nat.reduceEqDiff, ↓reduceIte, h6, h13, byte_slice_valid, indexValid, size, bind, Except.bind, Int.toNat_natCast]
    rw [ByteAccess.byte_element state view right index true initial cap hr]
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
  have loadLeft : (Prim.wordByteLoad .little (.local 18)).eval args rightEnv state = (.ok (ByteAccess.number a), state) := by
    simp only [Prim.eval_word_byte_load, Ref.eval_local, rightEnv, leftEnv, Control.Env.set,
      Nat.reduceEqDiff, ↓reduceIte, leftPtr, byte_pointer_valid, bind, Except.bind, firstRead]
  have loadRight : (Prim.wordByteLoad .little (.local 19)).eval args firstEnv state = (.ok (ByteAccess.number b), state) := by
    simp only [Prim.eval_word_byte_load, Ref.eval_local, firstEnv, rightEnv, Control.Env.set,
      Nat.reduceEqDiff, ↓reduceIte, rightPtr, byte_pointer_valid, bind, Except.bind, secondRead]
  have storeLeft : (Prim.wordByteStore .little (.local 18) (.local 21)).eval args secondEnv state = (.ok (.scalar .unit), middle) := by
    simp only [Prim.eval_word_byte_store, Ref.eval_local, secondEnv, firstEnv, rightEnv, leftEnv, Control.Env.set,
      Nat.reduceEqDiff, ↓reduceIte, leftPtr, byte_pointer_valid, ByteAccess.number_valid, bind, Except.bind, firstWrite]
  have storeRight : (Prim.wordByteStore .little (.local 19) (.local 20)).eval args writtenEnv middle = (.ok (.scalar .unit), after) := by
    simp only [Prim.eval_word_byte_store, Ref.eval_local, writtenEnv, secondEnv, firstEnv, rightEnv, Control.Env.set,
      Nat.reduceEqDiff, ↓reduceIte, rightPtr, byte_pointer_valid, ByteAccess.number_valid, bind, Except.bind, secondWrite]
  have typed (value : BitVec 8) : semantics.hasType (ByteAccess.number value) ByteAccess.byte = true := by
    simpa only [semantics] using ByteAccess.number_typed value
  have unitTyped : semantics.hasType (.scalar .unit) (.scalar .unit) = true := rfl
  have storeLeftEval : semantics.evalPrim (.wordByteStore .little (.local 18) (.local 21)) args secondEnv state =
      (.ok (.scalar .unit), middle) := by simpa only [semantics] using storeLeft
  have storeRightEval : semantics.evalPrim (.wordByteStore .little (.local 19) (.local 20)) args writtenEnv middle =
      (.ok (.scalar .unit), after) := by simpa only [semantics] using storeRight
  simp only [lane, Control.Code.enableLoops]
  apply GuardedSteps.bind_ok semantics args (Footprint view left right slot)
    (prim := .sliceElementPointer (.local 4) (.local 13)) (env := env) (state := state) (value := leftPtr)
    (by trivial) elementLeft (by rfl)
  apply GuardedSteps.bind_ok semantics args (Footprint view left right slot)
    (prim := .sliceElementPointer (.local 6) (.local 13)) (env := leftEnv) (state := state) (value := rightPtr)
    (by trivial) elementRight (by rfl)
  refine GuardedSteps.bind_ok semantics args (Footprint view left right slot)
    (prim := .wordByteLoad .little (.local 18)) (env := rightEnv) (state := state) (value := ByteAccess.number a) ?_ loadLeft (typed a) ?_
  · exact left_borrow view left right rightEnv index (by simp [rightEnv, leftEnv, Control.Env.set, leftPtr])
  refine GuardedSteps.bind_ok semantics args (Footprint view left right slot)
    (prim := .wordByteLoad .little (.local 19)) (env := firstEnv) (state := state) (value := ByteAccess.number b) ?_ loadRight (typed b) ?_
  · exact right_borrow view left right firstEnv index (by simp [firstEnv, rightEnv, Control.Env.set, rightPtr])
  refine GuardedSteps.bind_ok semantics args (Footprint view left right slot)
    (type := .scalar .unit) (prim := .wordByteStore .little (.local 18) (.local 21))
    (env := secondEnv) (state := state) (after := middle) (value := .scalar .unit) ?_ storeLeftEval unitTyped ?_
  · exact left_borrow view left right secondEnv index (by simp [secondEnv, firstEnv, rightEnv, leftEnv, Control.Env.set, leftPtr])
  refine GuardedSteps.bind_ok semantics args (Footprint view left right slot)
    (type := .scalar .unit) (prim := .wordByteStore .little (.local 19) (.local 20))
    (env := writtenEnv) (state := middle) (after := after) (value := .scalar .unit) ?_ storeRightEval unitTyped ?_
  · exact right_borrow view left right writtenEnv index (by simp [writtenEnv, secondEnv, firstEnv, rightEnv, Control.Env.set, rightPtr])
  apply GuardedSteps.control semantics args (Footprint view left right slot) _ rfl
  exact .refl _


/-- Successful lane refinement supplies all intermediate effects required by
the guarded proof; no additional memory-success assumptions escape this lemma. -/
theorem lane_guarded (args : List Value) (env nextEnv : Env) (state after : State) (view : View)
    (items : List (BitVec 32)) (left right : Nat) (index : Fin 4) (slot : Address)
    (frames : List (Control.Machine.Frame Ty Prim Ref))
    (initial : state.valid = true) (cap : Writable state view) (represented : Represents state view items)
    (hl : left < items.length) (hr : right < items.length) (apart : left ≠ right)
    (locals : Locals env view left right slot) (h13 : env 13 = some (size index.val))
    (evaluated : lane.eval semantics args env state = .jumped 14 (.scalar .unit) nextEnv after) :
    GuardedSteps semantics args (Footprint view left right slot) (.suspended ⟨lane.enableLoops, env, state, frames⟩)
      (jump semantics 14 (.scalar .unit) nextEnv after frames) := by
  obtain ⟨actual, ran, _, _, _, _⟩ :=
    ByteExchange.step_refines .little state view items left right index initial cap represented hl hr apart
  obtain ⟨a, b, middle, first, second, third, fourth⟩ :=
    ByteExchange.step_effects .little state actual view left right index ran
  have own := lane_of_effects args env state middle actual view left right index a b initial cap
    (by simpa only [represented.1] using hl) (by simpa only [represented.1] using hr)
    locals.1 locals.2.1 h13 first second third fourth
  have same : laneEnv env view left right index a b = nextEnv ∧ actual = after := by
    simpa only [Control.Outcome.jumped.injEq, true_and] using own.symm.trans evaluated
  rw [← same.1, ← same.2]
  exact lane_guarded_of_effects args env state middle actual view left right index slot a b frames initial cap
    (by simpa only [represented.1] using hl) (by simpa only [represented.1] using hr)
    locals.1 locals.2.1 h13 first second third fourth

end Compiler.ZigAir.MemoryWordSwap
