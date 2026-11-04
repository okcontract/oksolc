/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirRemainderExecution

namespace Compiler.ZigAir.WyhashUpdateAir.Loop
open Memory AggregateAir Compiler.Extraction Control.Machine

/-- Consume the complete loop and all post-loop instructions in one execution.
OOM retains either an interrupted round prefix or the completed loop cells when
the remaining-slice descriptor cannot be allocated. Success reaches the original
return with the exact cells used by `updateBody`; no tail execution is assumed. -/
theorem through_return {base state : State} {id index : Nat} (ctx : Context base id) (cells : Cells)
    (live : At ctx cells index state) (args : List Register) (env : Env)
    (outer : List (Frame Ty AggregateCall.Prim Ref)) (locals : Locals ctx env) :
    ∃ after,
      (∃ failedCells,
        (Interrupted ctx.source ctx.view index cells failedCells ∨
          ∃ stop, WyhashUpdate.loop ctx.source ctx.view index cells = .ok (failedCells, stop)) ∧
        WyhashUpdate.Core failedCells ctx.total ∧ StackFrame (ctx.frame.install failedCells) after ∧
        Steps AggregateCall.semantics args (.suspended ⟨entry, env, state, outer⟩)
          (.finished (.fault .outOfMemory after))) ∨
      ∃ finalCells,
        (do
          let (rounded, stop) ← WyhashUpdate.loop ctx.source ctx.view index cells
          WyhashUpdate.remainder ctx.source ctx.view stop rounded) = .ok finalCells ∧
        WyhashUpdate.Core finalCells ctx.total ∧ StackFrame (ctx.frame.install finalCells) after ∧
        Steps AggregateCall.semantics args (.suspended ⟨entry, env, state, outer⟩)
          (.finished (.returned (.value (.scalar .unit)) after)) := by
  obtain ⟨reached, failed | ⟨rounded, stop, finalEnv, loopRun, finalAt, _, _, upper, ended, _, loopPath, before⟩⟩ :=
    entry_steps ctx cells live args env outer locals
  · obtain ⟨failedCells, interrupted, core, stack, path⟩ := failed
    exact ⟨reached, Or.inl ⟨failedCells, Or.inl interrupted, core, stack, path⟩⟩
  · let current := (ctx.frame.replaced rounded).extend finalAt.stack
    have indexApart : ctx.indexSlot ≠ id := by
      have := (valid_lookup base id ctx.frame.cell ctx.valid ctx.frame.found).1
      have := ctx.indexFresh
      omega
    have self := finalAt.old_load ⟨ctx.selfSlot, 0⟩ ctx.selfApart false false (.pointer true false objectType) _ ctx.selfRead
    have input := finalAt.old_load ⟨ctx.inputSlot, 0⟩ ctx.inputApart false false inputType _ ctx.inputRead
    obtain ⟨after, ⟨stack, path⟩ | ⟨finalCells, tailRun, finalCore, stack, path⟩⟩ :=
      Remainder.execute current finalAt.stack.valid ctx.typed ctx.address ctx.source ctx.view ctx.bytes
        ctx.geometry ctx.represented finalAt.reads ctx.apart ctx.total stop ctx.selfSlot ctx.inputSlot ctx.indexSlot
        finalAt.core upper ended (by have := ctx.budget; omega) ctx.selfApart ctx.inputApart indexApart self input finalAt.indexRead
        args finalEnv outer (by rw [before 4 (by decide)]; exact locals.1)
        (by rw [before 7 (by decide)]; exact locals.2.1) (by rw [before 50 (by decide)]; exact locals.2.2)
    · exact ⟨after, Or.inl ⟨rounded, Or.inr ⟨stop, loopRun⟩, finalAt.core, finalAt.stack.trans stack,
        loopPath.trans AggregateCall.semantics args path⟩⟩
    · refine ⟨after, Or.inr ⟨finalCells, ?_, finalCore, finalAt.updated finalCore stack,
        loopPath.trans AggregateCall.semantics args path⟩⟩
      simpa only [loopRun, bind, Except.bind] using tailRun

end Compiler.ZigAir.WyhashUpdateAir.Loop
