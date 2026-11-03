/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirFillGuard

set_option maxRecDepth 8192

namespace Compiler.ZigAir.WyhashUpdateAir.Fill
open Memory AggregateAir Compiler.Extraction Control.Machine

def copy : Code := Round.fillBody.dropBindings 5

def assign : Code :=
  .bind 61 usize (.primitive (.memory (.scalar (.arithmetic .sub .unchecked (.constant (.int false 64 48)) (.local 60))))) $
  .bind 62 (.scalar .unit) (.primitive (.store (.local 50) (.local 61))) copy

theorem generated_assign : Round.fillBody = lengthCode 58 assign := by decide +kernel

def assignedEnv (env : Env) (id length : Nat) : Env :=
  ((lengthEnv env 58 id length).set 61 (size (48 - length))).set 62 (.value (.scalar .unit))

/-- The source sets its mutable index before copying or rounding the buffer.
The same owned index and caller frame feed the later full-block loop. -/
theorem assign_steps {base state : State} {id oldIndex : Nat} (ctx : Loop.Context base id) (cells : Cells)
    (live : Loop.At ctx cells oldIndex state) (length : Nat) (bounded : length ≤ 48)
    (more : 48 - length < ctx.view.length)
    (lengthField : cells.lookup 48 = some (WyhashLocal.word (BitVec.ofNat 64 length)))
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref)) (locals : Loop.Locals ctx env) :
    ∃ after, Loop.At ctx cells (48 - length) after ∧
      Steps AggregateCall.semantics args (.suspended ⟨Round.fillBody, env, state, outer⟩)
        (.suspended ⟨copy, assignedEnv env id length, after, outer⟩) := by
  have limit : 48 < addressLimit := by decide
  let current := (ctx.frame.replaced cells).extend live.stack
  have unchanged : current.install cells = state := current.install_current live.stack.valid
  have self := live.old_load ⟨ctx.selfSlot, 0⟩ ctx.selfApart false false (.pointer true false objectType) _ ctx.selfRead
  have head := length_steps current cells ctx.typed length ctx.selfSlot 58 (by omega) lengthField
    ctx.selfApart self args env outer assign locals.1
  rw [unchanged, ← generated_assign] at head
  let loaded := lengthEnv env 58 id length
  let sized := loaded.set 61 (size (48 - length))
  have p61 := size_sub state args loaded (.constant (.int false 64 48)) (.local 60) 48 length limit bounded rfl
    (SliceBytesAir.scalar_size loaded 60 length (by omega) (by simp [loaded, lengthEnv, Control.Env.set]))
  obtain ⟨counter, typed, valid⟩ := live.counter
  obtain ⟨contents, stored, contentsValid, read⟩ := Index.store counter typed valid (48 - length) (by omega)
  have aggregateStore : AggregateAir.store state (slot true usize ctx.indexSlot) (size (48 - length)) =
      .ok (counter.install contents) := by
    simpa only [AggregateAir.store, size] using stored
  have p62 := eval_store (.local 50) (.local 61) args sized state (counter.install contents)
    (slot true usize ctx.indexSlot) (size (48 - length))
    (value_local _ _ _ (by simp [sized, loaded, lengthEnv, Control.Env.set, locals.2.2]) rfl)
    (ref_local _ _ _ (by simp [sized, Control.Env.set]) (SliceBytesAir.size_valid _ (by omega))) aggregateStore
  have tail : Steps AggregateCall.semantics args (.suspended ⟨assign, loaded, state, outer⟩)
      (.suspended ⟨copy, assignedEnv env id length, counter.install contents, outer⟩) :=
    AggregateCall.primitive_steps args p61 (SliceBytesAir.size_typed _ (by omega)) <|
      AggregateCall.primitive_steps args p62 rfl (.refl _)
  refine ⟨counter.install contents, ⟨live.core, ?_, ?_, read, more⟩,
    head.trans AggregateCall.semantics args tail⟩
  · exact live.stack.install ctx.indexSlot counter contents ctx.indexFresh (typed ▸ contentsValid)
  · exact ⟨counter.replaced contents, typed, contentsValid⟩

theorem assigned_before (env : Env) (id length query : Nat) (earlier : query < 58) :
    assignedEnv env id length query = env query := by
  simp (disch := omega) only [assignedEnv, lengthEnv, Control.Env.set, if_neg]

end Compiler.ZigAir.WyhashUpdateAir.Fill
