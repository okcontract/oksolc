/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirFillExecution

set_option maxRecDepth 8192

namespace Compiler.ZigAir.WyhashUpdateAir.Fill
open Memory AggregateAir Compiler.Extraction Control.Machine

/-- A failing fill retains the copy and the exact prefix of completed lanes. -/
def Interrupted (source : Cells) (view : ByteSlice.View) (length : Nat) (cells failed : Cells) : Prop :=
  ∃ copied completed,
    ByteSlice.copy source view (WyhashBuffer.buffer 0 48) 0 length (48 - length) cells = .ok copied ∧
    completed < 3 ∧ Round.lanePrefix .buffer 0 completed copied = .ok failed

/-- Derive the complete optional fill from the original guard, owned index,
byte copy, existing round and length reset. The result enters the full-block
loop with its invariant; OOM keeps the copy and every lane already executed. -/
theorem execute {base state : State} {id : Nat} (ctx : Loop.Context base id) (cells : Cells)
    (live : Loop.At ctx cells 0 state) (endBound : ctx.frame.cell.base + 104 < addressLimit)
    (length : Nat) (bounded : length ≤ 48) (more : 48 - length < ctx.view.length)
    (lengthField : cells.lookup 48 = some (WyhashLocal.word (BitVec.ofNat 64 length)))
    (head : ∀ i < length, WyhashUpdate.ByteAt cells (56 + i))
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref)) (locals : Loop.Locals ctx env) :
    ∃ after,
      (∃ failedCells, Interrupted ctx.source ctx.view length cells failedCells ∧
        WyhashUpdate.Core failedCells ctx.total ∧ StackFrame (ctx.frame.install failedCells) after ∧
        Steps AggregateCall.semantics args (.suspended ⟨Index.continuation, env, state, outer⟩)
          (.finished (.fault .outOfMemory after))) ∨
      ∃ filled index nextEnv,
        WyhashUpdate.fill ctx.source ctx.view length cells = .ok (filled, index) ∧ Loop.At ctx filled index after ∧
        Steps AggregateCall.semantics args (.suspended ⟨Index.continuation, env, state, outer⟩)
          (.suspended ⟨Loop.entry, nextEnv, after, outer⟩) ∧
        ∀ query < 52, nextEnv query = env query := by
  have limit : 48 < addressLimit := by decide
  have budget : ctx.view.length < addressLimit := by have := ctx.budget; omega
  have indexApart : ctx.indexSlot ≠ id := by
    have := (valid_lookup base id ctx.frame.cell ctx.valid ctx.frame.found).1
    have := ctx.indexFresh
    omega
  let current := (ctx.frame.replaced cells).extend live.stack
  have same : current.install cells = state := current.install_current live.stack.valid
  let inner := Frame.block 52 (.scalar .unit) Loop.entry :: outer
  have entered : Steps AggregateCall.semantics args (.suspended ⟨Index.continuation, env, state, outer⟩)
      (.suspended ⟨Index.guard, env, state, inner⟩) := .step _ (.refl _)
  have self := live.old_load ⟨ctx.selfSlot, 0⟩ ctx.selfApart false false (.pointer true false objectType) _ ctx.selfRead
  have guard := guard_steps current cells ctx.typed length ctx.selfSlot (by omega) lengthField ctx.selfApart
    self args env inner locals.1
  rw [same] at guard
  let selected := guardEnv env id length
  have selectedLocals : Loop.Locals ctx selected := by
    simpa only [Loop.Locals, selected, guard_before _ _ _ 4 (by decide),
      guard_before _ _ _ 7 (by decide), guard_before _ _ _ 50 (by decide)] using locals
  by_cases nonempty : 0 < length
  · rw [if_pos nonempty] at guard
    obtain ⟨assigned, assignedAt, assignedPath⟩ := assign_steps ctx cells live length bounded more lengthField
      args selected inner selectedLocals
    let assignedFrame := (ctx.frame.replaced cells).extend assignedAt.stack
    have assignedSame : assignedFrame.install cells = assigned := assignedFrame.install_current assignedAt.stack.valid
    let assignedLocals := assignedEnv selected id length
    have copiedLocals : Loop.Locals ctx assignedLocals := by
      simpa only [Loop.Locals, assignedLocals, assigned_before _ _ _ 4 (by decide),
        assigned_before _ _ _ 7 (by decide), assigned_before _ _ _ 50 (by decide)] using selectedLocals
    obtain ⟨copied, copiedEnv, copyPath, copiedRun, copiedCore, ready, copyBefore⟩ := copy_steps assignedFrame assignedAt.stack.valid
      ctx.typed endBound ctx.address ctx.source cells ctx.view ctx.bytes ctx.geometry ctx.represented assignedAt.reads ctx.apart
      ctx.total length ctx.selfSlot ctx.inputSlot ctx.indexSlot assignedAt.core bounded more budget head lengthField
      ctx.selfApart ctx.inputApart indexApart
      (assignedAt.old_load ⟨ctx.selfSlot, 0⟩ ctx.selfApart false false (.pointer true false objectType) _ ctx.selfRead)
      (assignedAt.old_load ⟨ctx.inputSlot, 0⟩ ctx.inputApart false false inputType _ ctx.inputRead)
      assignedAt.indexRead args assignedLocals inner copiedLocals.1 copiedLocals.2.1 copiedLocals.2.2
    rw [assignedSame] at copyPath
    have copiedAt := assignedAt.mutated copiedCore
      (StackFrame.refl (assignedFrame.install copied) (assignedFrame.valid copied assignedAt.stack.valid (ctx.typed ▸ copiedCore.valid)))
    let copiedFrame := assignedFrame.replaced copied
    obtain ⟨rounded, ⟨completed, failedCells, prefixBound, failedRun, failedCore, failedStack, failedPath⟩ |
        ⟨roundedCells, roundedEnv, roundedRun, roundedCore, _, _, roundedStack, roundedPath, roundedBefore⟩⟩ :=
      Round.buffer_steps copiedFrame copiedAt.stack.valid ctx.typed ctx.total copiedCore ready ctx.selfSlot
        (copiedAt.old_load ⟨ctx.selfSlot, 0⟩ ctx.selfApart false false (.pointer true false objectType) _ ctx.selfRead)
        args copiedEnv inner ((copyBefore 4 (by decide)).trans copiedLocals.1)
    · refine ⟨rounded, Or.inl ⟨failedCells, ⟨copied, completed, copiedRun, prefixBound, failedRun⟩, failedCore, ?_, ?_⟩⟩
      · exact copiedAt.updated failedCore failedStack
      · exact entered.trans AggregateCall.semantics args (guard.trans AggregateCall.semantics args
          (assignedPath.trans AggregateCall.semantics args (copyPath.trans AggregateCall.semantics args failedPath)))
    · have roundedAt := copiedAt.mutated roundedCore roundedStack
      let roundedFrame := (ctx.frame.replaced roundedCells).extend roundedAt.stack
      have roundedSame : roundedFrame.install roundedCells = rounded := roundedFrame.install_current roundedAt.stack.valid
      have finished := reset_steps roundedFrame roundedCells ctx.typed ctx.selfSlot ctx.selfApart
        (roundedAt.old_load ⟨ctx.selfSlot, 0⟩ ctx.selfApart false false (.pointer true false objectType) _ ctx.selfRead)
        args roundedEnv outer ((roundedBefore 4 (by decide)).trans ((copyBefore 4 (by decide)).trans copiedLocals.1))
      rw [roundedSame] at finished
      let finalCells := roundedCells.set 48 (WyhashLocal.word 0)
      have finalCore : WyhashUpdate.Core finalCells ctx.total := roundedCore.store_word 48 0 (by decide)
      have finalAt := roundedAt.mutated finalCore (StackFrame.refl (roundedFrame.install finalCells)
        (roundedFrame.valid finalCells roundedAt.stack.valid (ctx.typed ▸ finalCore.valid)))
      refine ⟨roundedFrame.install finalCells, Or.inr ⟨finalCells, 48 - length, resetEnv roundedEnv id,
        ?_, finalAt, ?_, ?_⟩⟩
      · rw [WyhashUpdate.fill, if_pos nonempty]
        refine WyhashLocal.bind_result _ _ _ _ copiedRun ?_
        refine WyhashLocal.bind_result _ _ _ _ roundedRun ?_
        exact WyhashLocal.bind_result _ _ _ _ (WyhashUpdate.store_eq roundedCells 48 0 (by decide)) rfl
      · exact entered.trans AggregateCall.semantics args (guard.trans AggregateCall.semantics args
          (assignedPath.trans AggregateCall.semantics args (copyPath.trans AggregateCall.semantics args
            (roundedPath.trans AggregateCall.semantics args finished))))
      · intro query earlier
        exact (reset_before roundedEnv id query earlier).trans
          ((roundedBefore query (by omega)).trans ((copyBefore query (by omega)).trans
            ((assigned_before selected id length query (by omega)).trans (guard_before env id length query (by omega)))))
  · rw [if_neg nonempty] at guard
    have jumped : Steps AggregateCall.semantics args (.suspended ⟨skip, selected, state, inner⟩)
        (.suspended ⟨Loop.entry, selected.set 52 (.value (.scalar .unit)), state, outer⟩) := .step _ (.refl _)
    refine ⟨state, Or.inr ⟨cells, 0, _, by simp only [WyhashUpdate.fill, if_neg nonempty], live,
      entered.trans AggregateCall.semantics args (guard.trans AggregateCall.semantics args jumped), ?_⟩⟩
    intro query earlier
    exact (show (selected.set 52 (.value (.scalar .unit))) query = selected query by
      simp only [Control.Env.set, if_neg (by omega : query ≠ 52)]).trans (guard_before env id length query (by omega))

end Compiler.ZigAir.WyhashUpdateAir.Fill
