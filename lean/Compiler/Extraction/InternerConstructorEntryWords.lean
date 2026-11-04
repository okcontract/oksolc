/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorProtocolPreparedEntry
import Compiler.Extraction.InternerPhysicalDispatchPreservation

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Recursive Caller.ProtocolTrace Interner.InvocationTrace

/-- Complete entry replay transfers logical word safety to the actual native
invocation's result and graph. Scope closure remains the separate native frame
obligation; protocol history determines only the logical resource cursor. -/
theorem EntryProjected.words (model : Interner.Primitives) (request : Interner.Request)
    (before : Interner.Heap) (leading trailing : List ProtocolEvent)
    (actual : Except Fault NodeId × Recorded σ) (checked : EntryProjected model request before leading trailing actual)
    (meaning : Meaning) (expected : Word)
    (safe : Interner.Safe meaning
      (Interner.Scoped.find (resources (actual.2.events ++ trailing) (.preparation .incomplete)) model request)
      {before with allocationCursor := leading.length} (fun id after => after.read id = some expected)) :
    Semantic.Ensures meaning before actual.1 actual.2.native.world.graph (fun id after => after.read id = some expected) := by
  apply (Semantic.Ensures.cursor_iff meaning before actual.2.native.world.graph actual.1
    leading.length actual.2.events.length (fun id read => read id = some expected)).mp
  refine safe_at _ _ _ _ _ _ ?_ safe
  intro completed
  have projected := (checked completed).1
  exact ⟨congrArg Prod.fst projected, congrArg (fun result => result.2.heap) projected⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
