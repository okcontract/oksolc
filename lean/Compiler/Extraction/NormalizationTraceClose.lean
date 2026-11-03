/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationClose
import Compiler.Extraction.NormalizationTraceReplay
import Compiler.Extraction.NormalizationTraceScope

namespace Compiler.Extraction.Cache.NormalizationOwnership.Trace

theorem close_replay (p : PreparedPrimitives σ ε) (mismatch : ε) (phase : Exit) (lookup : State)
    (before : σ) (suffix : List (Event ε)) :
    let execution := normalizationOwnershipCode.closeWith (record p).release phase lookup ⟨before, []⟩
    normalizationOwnershipCode.closeWith (replay (execution.2.events ++ suffix) mismatch).release phase lookup 0 =
      (execution.1, execution.2.events.length) := by
  cases phase <;> cases owned : lookup.owned <;>
    simp [Code.closeWith, Code.deinitWith, normalizationOwnershipCode, owned, move_owned, record, replay, release]

theorem close_replay_at (p : PreparedPrimitives σ ε) (mismatch : ε) (phase : Exit) (lookup : State)
    (before : σ) (leading suffix : List (Event ε)) :
    let execution := normalizationOwnershipCode.closeWith (record p).release phase lookup ⟨before, []⟩
    normalizationOwnershipCode.closeWith (replay (leading ++ (execution.2.events ++ suffix)) mismatch).release
      phase lookup leading.length = (execution.1, leading.length + execution.2.events.length) := by
  have replayed := close_replay p mismatch phase lookup before suffix
  have mapped := close_transport normalizationOwnershipCode
    (replay ((normalizationOwnershipCode.closeWith (record p).release phase lookup ⟨before, []⟩).2.events ++ suffix) mismatch).release
    (replay (leading ++ ((normalizationOwnershipCode.closeWith (record p).release phase lookup ⟨before, []⟩).2.events ++ suffix)) mismatch).release
    (fun cursor => leading.length + cursor) (replay_prefix _ leading mismatch).release phase lookup 0
  rw [replayed] at mapped
  simpa only [Nat.add_zero] using mapped

theorem Scope.close_projection (events : List (Event ε)) (mismatch : ε) (phase : Exit) (lookup : State)
    (items : List Compiler.Algebraic.NodeId) (graph : Interner.Heap) :
    Interner.Scoped.close (resources events mismatch) ⟨⟨some lookup, items, phase⟩, graph⟩ =
      let closed := normalizationOwnershipCode.closeWith (replay events mismatch).release phase lookup graph.allocationCursor
      ⟨⟨some closed.1, items, phase⟩, { graph with allocationCursor := closed.2 }⟩ := by
  cases phase <;> rfl

end Compiler.Extraction.Cache.NormalizationOwnership.Trace
