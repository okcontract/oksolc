/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirFill

namespace Compiler.ZigAir.WyhashUpdateAir.Long
open Memory AggregateAir Compiler.Extraction Control.Machine

/-- The exact hasher writes reachable before a long update's allocation failure:
none, the fill copy and lane prefix, or a completed fill followed by loop work. -/
def Interrupted (source : Cells) (view : ByteSlice.View) (length : Nat) (cells failed : Cells) : Prop :=
  failed = cells ∨ Fill.Interrupted source view length cells failed ∨
    ∃ filled index, WyhashUpdate.fill source view length cells = .ok (filled, index) ∧
      (Loop.Interrupted source view index filled failed ∨
        ∃ stop, WyhashUpdate.loop source view index filled = .ok (failed, stop))

/-- From the actual mutable-index allocation through return. The existing fill
and loop invariants are composed; successful allocation or execution is never
supplied by the caller. -/
theorem execute {base : State} {id : Nat} (ctx : Loop.Context base id)
    (indexSlot : ctx.indexSlot = base.nextId)
    (core : WyhashUpdate.Core ctx.frame.cell.cells ctx.total)
    (endBound : ctx.frame.cell.base + 104 < addressLimit)
    (length : Nat) (bounded : length ≤ 48) (more : 48 - length < ctx.view.length)
    (lengthField : ctx.frame.cell.cells.lookup 48 = some (WyhashLocal.word (BitVec.ofNat 64 length)))
    (head : ∀ i < length, WyhashUpdate.ByteAt ctx.frame.cell.cells (56 + i))
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (foundSelf : env 4 = some (.value (slot false (.pointer true false objectType) ctx.selfSlot)))
    (foundInput : env 7 = some (.value (slot false inputType ctx.inputSlot))) :
    ∃ after,
      (∃ failedCells, Interrupted ctx.source ctx.view length ctx.frame.cell.cells failedCells ∧
        WyhashUpdate.Core failedCells ctx.total ∧ StackFrame (ctx.frame.install failedCells) after ∧
        Steps AggregateCall.semantics args (.suspended ⟨longBody, env, base, outer⟩)
          (.finished (.fault .outOfMemory after))) ∨
      ∃ cells, WyhashUpdate.updateBody ctx.source ctx.view length ctx.frame.cell.cells = .ok cells ∧
        WyhashUpdate.Core cells ctx.total ∧ StackFrame (ctx.frame.install cells) after ∧
        Steps AggregateCall.semantics args (.suspended ⟨longBody, env, base, outer⟩)
          (.finished (.returned (.value (.scalar .unit)) after)) := by
  obtain ⟨prepared, stack, failed | ⟨allocated, indexRead, _, counter⟩⟩ := Index.allocate_steps base ctx.valid args env outer
  · refine ⟨prepared, Or.inl ⟨ctx.frame.cell.cells, Or.inl rfl, core, ?_, failed⟩⟩
    simpa only [ctx.frame.install_current ctx.valid] using stack
  · let preparedEnv := Index.resultEnv env base.nextId
    have admitted : Loop.At ctx ctx.frame.cell.cells 0 prepared := by
      refine ⟨core, ?_, ?_, ?_, by omega⟩
      · simpa only [ctx.frame.install_current ctx.valid] using stack
      · rw [indexSlot]; exact counter
      · rw [indexSlot]; exact indexRead
    have locals : Loop.Locals ctx preparedEnv := by
      simp only [Loop.Locals, preparedEnv, Index.resultEnv, Control.Env.set, ↓reduceIte, indexSlot, foundSelf, foundInput]
      exact ⟨rfl, rfl, rfl⟩
    obtain ⟨filledState, ⟨failedCells, failedFill, failedCore, failedStack, failedPath⟩ |
        ⟨filled, index, filledEnv, fillRun, filledAt, fillPath, fillBefore⟩⟩ :=
      Fill.execute ctx ctx.frame.cell.cells admitted endBound length bounded more lengthField head args preparedEnv outer locals
    · exact ⟨filledState, Or.inl ⟨failedCells, Or.inr (Or.inl failedFill), failedCore, failedStack,
        allocated.trans AggregateCall.semantics args failedPath⟩⟩
    · have nextLocals : Loop.Locals ctx filledEnv := by
        simpa only [Loop.Locals, fillBefore 4 (by decide), fillBefore 7 (by decide), fillBefore 50 (by decide)] using locals
      obtain ⟨after, ⟨failedCells, interrupted, failedCore, failedStack, failedPath⟩ |
          ⟨cells, bodyRun, nextCore, nextStack, nextPath⟩⟩ :=
        Loop.through_return ctx filled filledAt args filledEnv outer nextLocals
      · exact ⟨after, Or.inl ⟨failedCells, Or.inr (Or.inr ⟨filled, index, fillRun, interrupted⟩), failedCore, failedStack,
          allocated.trans AggregateCall.semantics args (fillPath.trans AggregateCall.semantics args failedPath)⟩⟩
      · refine ⟨after, Or.inr ⟨cells, ?_, nextCore, nextStack,
          allocated.trans AggregateCall.semantics args (fillPath.trans AggregateCall.semantics args nextPath)⟩⟩
        rw [WyhashUpdate.updateBody, if_neg (by omega : ¬ctx.view.length ≤ 48 - length)]
        exact WyhashLocal.bind_result _ _ _ _ fillRun bodyRun

end Compiler.ZigAir.WyhashUpdateAir.Long
