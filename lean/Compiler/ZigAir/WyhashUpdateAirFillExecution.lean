/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirFillSource

set_option maxRecDepth 8192

namespace Compiler.ZigAir.WyhashUpdateAir.Loop
open Memory AggregateAir Compiler.Extraction Control.Machine

/-- Mutating the hasher and extending its local frame preserves the owned index.
This is the same framing used by the full-block induction, before its index step. -/
theorem At.mutated {base state after : State} {id index : Nat} {ctx : Context base id} {cells next : Cells}
    (live : At ctx cells index state) (core : WyhashUpdate.Core next ctx.total)
    (stack : StackFrame (((ctx.frame.replaced cells).extend live.stack).install next) after) :
    At ctx next index after := by
  let current := (ctx.frame.replaced cells).extend live.stack
  have apart : ctx.indexSlot ≠ id := by
    have := (valid_lookup base id ctx.frame.cell ctx.valid ctx.frame.found).1
    have := ctx.indexFresh
    omega
  obtain ⟨counter, typed, valid⟩ := live.counter
  let kept := (current.after_other counter next apart).extend stack
  refine ⟨core, live.updated core stack, ⟨kept, typed, valid⟩, ?_, live.inside⟩
  exact stack.old_load true false usize ⟨ctx.indexSlot, 0⟩ _
    ((current.load_outside next ⟨ctx.indexSlot, 0⟩ apart true false usize).trans live.indexRead)

end Compiler.ZigAir.WyhashUpdateAir.Loop

namespace Compiler.ZigAir.WyhashUpdateAir.Fill
open Memory AggregateAir Compiler.Extraction Control.Machine

/-- The copy fills precisely the missing bytes, including a zero-byte copy at
the end of a full buffer. Old initialized bytes and new input reads establish
the complete native round input; no buffer-read contract is supplied. -/
theorem copy_steps {state : State} {id : Nat} (frame : CellFrame state id)
    (valid : state.valid = true) (typed : frame.cell.type = objectType) (endBound : frame.cell.base + 104 < addressLimit)
    (address : Address) (source cells : Cells) (view : ByteSlice.View) (bytes : Nat → BitVec 8)
    (geometry : ByteSlice.Geometry view) (represented : ByteSlice.Represents source view bytes)
    (reads : ByteRange.Reads state address view.length bytes) (apart : address.allocation ≠ id)
    (total length selfSlot inputSlot indexSlot : Nat) (core : WyhashUpdate.Core cells total)
    (bounded : length ≤ 48) (more : 48 - length < view.length) (budget : view.length < addressLimit)
    (head : ∀ i < length, WyhashUpdate.ByteAt cells (56 + i))
    (lengthField : cells.lookup 48 = some (WyhashLocal.word (BitVec.ofNat 64 length)))
    (selfApart : selfSlot ≠ id) (inputApart : inputSlot ≠ id) (indexApart : indexSlot ≠ id)
    (selfRead : Memory.load state (slot false (.pointer true false objectType) selfSlot) = .ok (selfPointer id))
    (inputRead : Memory.load state (slot false inputType inputSlot) = .ok (.slice inputType address view.length))
    (indexRead : Memory.load state (slot true usize indexSlot) = .ok (.scalar (.int false 64 (48 - length : Nat))))
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (foundSelf : env 4 = some (.value (slot false (.pointer true false objectType) selfSlot)))
    (foundInput : env 7 = some (.value (slot false inputType inputSlot)))
    (foundIndex : env 50 = some (.value (slot true usize indexSlot))) :
    ∃ copied nextEnv, Steps AggregateCall.semantics args (.suspended ⟨copy, env, frame.install cells, outer⟩)
        (.suspended ⟨Round.bufferSite, nextEnv, frame.install copied, outer⟩) ∧
      ByteSlice.copy source view (WyhashBuffer.buffer 0 48) 0 length (48 - length) cells = .ok copied ∧
      WyhashUpdate.Core copied total ∧ WyhashUpdate.Input.buffer.Ready copied ∧
      ∀ query < 63, nextEnv query = env query := by
  obtain ⟨targetEnv, targetPath, targetFound, targetBefore⟩ := target_steps frame cells valid typed endBound
    length (48 - length) selfSlot indexSlot (by omega) lengthField selfApart indexApart selfRead indexRead
    args env outer foundSelf foundIndex
  have sourcePath := source_steps (frame.install cells) address view.length (48 - length) inputSlot indexSlot
    bytes (reads.install frame cells _ _ _ apart) (by omega) (by omega) budget
    (load_saved frame cells inputSlot inputType 0 _ inputApart inputRead)
    ((frame.load_outside cells ⟨indexSlot, 0⟩ indexApart true false usize).trans indexRead)
    args targetEnv outer (by rw [targetBefore 7 (by decide)]; exact foundInput)
    (by rw [targetBefore 50 (by decide)]; exact foundIndex)
  let prepared := sourceEnv targetEnv address view.length (48 - length)
  obtain ⟨copied, nextEnv, copiedPath, model, nextCore, newBytes, outside, copiedBefore⟩ := copy_end_steps frame
    typed address source cells view bytes geometry represented reads apart total length (48 - length) core
    (by omega) (by omega) args prepared outer
    ((source_before targetEnv address view.length (48 - length) 72 (by decide)).trans targetFound)
    (by simp [prepared, sourceEnv, Control.Env.set])
  have full : ∀ i < 48, WyhashUpdate.ByteAt copied (56 + i) := by
    intro i inside
    by_cases old : i < length
    · simpa only [WyhashUpdate.ByteAt, outside (56 + i) (Or.inl (by omega))] using head i old
    · have atIndex := newBytes (i - length) (by omega)
      simpa only [show length + (i - length) = i by omega] using atIndex
  refine ⟨copied, nextEnv, targetPath.trans AggregateCall.semantics args
    (sourcePath.trans AggregateCall.semantics args copiedPath), model, nextCore,
    ⟨WyhashBuffer.buffer_geometry 0 48 (by decide), full⟩, ?_⟩
  intro query earlier
  exact (copiedBefore query (by omega)).trans
    ((source_before targetEnv address view.length (48 - length) query (by omega)).trans (targetBefore query earlier))

def reset : Code :=
  .bind 320 (.pointer true false objectType) (.primitive (.load (.local 4))) $
  .bind 321 (.pointer true false usize) (.primitive (.fieldPointer (.local 320) 48)) $
  .bind 322 (.scalar .unit) (.primitive (.store (.local 321) (.constant (.value (.scalar (.int false 64 0)))))) skip

theorem generated_reset : Round.lanesAt false 3 = reset := by decide +kernel

def resetEnv (env : Env) (id : Nat) : Env :=
  let env := env.set 320 (.value (selfPointer id))
  let env := env.set 321 (.value (.pointer (.pointer true false usize) ⟨id, 48⟩))
  (env.set 322 (.value (.scalar .unit))).set 52 (.value (.scalar .unit))

theorem reset_steps {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (typed : frame.cell.type = objectType) (selfSlot : Nat) (selfApart : selfSlot ≠ id)
    (selfRead : Memory.load state (slot false (.pointer true false objectType) selfSlot) = .ok (selfPointer id))
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (foundSelf : env 4 = some (.value (slot false (.pointer true false objectType) selfSlot))) :
    Steps AggregateCall.semantics args
      (.suspended ⟨Round.lanesAt false 3, env, frame.install cells, Frame.block 52 (.scalar .unit) Loop.entry :: outer⟩)
      (.suspended ⟨Loop.entry, resetEnv env id, frame.install (cells.set 48 (WyhashLocal.word 0)), outer⟩) := by
  let e320 := env.set 320 (.value (selfPointer id))
  let e321 := e320.set 321 (.value (.pointer (.pointer true false usize) ⟨id, 48⟩))
  have self := load_saved frame cells selfSlot (.pointer true false objectType) 0 _ selfApart selfRead
  have p320 := eval_load (.local 4) args env (frame.install cells) _ _
    (value_local _ _ _ foundSelf rfl) (congrArg (Except.map Register.value) self)
  have p321 := eval_field (.local 320) 48 args e320 (frame.install cells) _ _
    (value_local _ _ _ (by simp [e320, Control.Env.set]) rfl)
    (field_pointer frame cells typed 48 usize (by decide))
  have written := WyhashInit.object_word_store frame cells typed 48 (by decide) 0
  have p322 := eval_store (.local 321) (.constant (.value (.scalar (.int false 64 0)))) args e321 (frame.install cells) _
    (.pointer (.pointer true false usize) ⟨id, 48⟩) (size 0)
    (value_local _ _ _ (by simp [e321, Control.Env.set]) rfl) rfl written
  rw [generated_reset, reset]
  exact AggregateCall.primitive_steps args p320 rfl <|
    AggregateCall.primitive_steps args p321 rfl <|
    AggregateCall.primitive_steps args p322 rfl (.step _ (.refl _))

theorem reset_before (env : Env) (id query : Nat) (earlier : query < 52) : resetEnv env id query = env query := by
  simp (disch := omega) only [resetEnv, Control.Env.set, if_neg]

end Compiler.ZigAir.WyhashUpdateAir.Fill
