/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPhysicalDispatchProduction

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Recursive
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul

/-- The target of RC, not an established preservation theorem. `actual` must be
the source-bound constructor/caller execution, including its local cleanup.
`native` describes graph/field/container correspondence and `frame` describes
the live parent borrows at this call site. Neither predicate is a host axiom.
The ledger records how their initial truth and preservation must be derived. -/
def ConstructorGoal (native frame : World σ → Prop)
    (actual : World σ → Except Fault NodeId × State σ)
    (logical : Interner.Action NodeId) (meaning : Meaning) (request : Interner.Request) : Prop :=
  Projects (fun world => native world ∧ frame world)
    (fun before => ((actual before).1, (actual before).2.world)) logical ∧
  ∀ before value, native before → frame before → Interner.Invariant meaning before.graph →
    request.item.eval meaning before.graph.read request.arguments request.sequence = some value →
    ordinary (actual before).1 = true →
    Closed (actual before).2.scope ∧
    Semantic.Ensures meaning before.graph (actual before).1 (actual before).2.world.graph
      (fun id after => after.read id = some value)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Recursive
