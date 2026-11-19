/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorProtocolComplete

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray Caller.ProtocolTrace Interner.InvocationTrace

/-- Only a reached, successfully prepared caller can need miss correspondence.
This reuses the existing local miss obligation; no complete constructor or
caller simulation, cleanup result or prepared input is assumed at entry. -/
def EntryContinuation (context : PairInput.Context σ)
    (ports : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → GraphObservations σ)
    (model : Interner.Primitives) (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before : World σ) (leading trailing : List ProtocolEvent) : Prop :=
  ∀ (constructed : World σ) (address : Compiler.ZigAir.Memory.Address) (memory : Compiler.ZigAir.Memory.State),
    prepare request.item debug before = (.ok address, constructed) →
    context.queries.atCapacity constructed.graph = false →
    Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨constructed.memory.memory.nextId, 0⟩, memory) →
    MissContinuation context.external context.budget context.allocator
      (context.primitives source address (input request.item debug)) context.queries (ports source address (input request.item debug))
      model source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      (start { constructed with memory := { constructed.memory with memory } } leading) trailing

/-- Rejected item preparation retains its exact reached world and history.
The shared native classification keeps this outcome outside ordinary returns. -/
theorem item_rejected (context : PairInput.Context σ)
    (ports : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → GraphObservations σ)
    (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before reached : World σ) (fault : Fault) (leading : List ProtocolEvent)
    (failed : prepare request.item debug before = (.error fault, reached)) :
    item context ports source request debug before leading = (.error fault, start reached leading) ∧
      ordinary (item context ports source request debug before leading).1 = false := by
  have ran : item context ports source request debug before leading = (.error fault, start reached leading) := by
    simp only [item, failed]
  exact ⟨ran, by rw [ran]; exact prepare_error_nonordinary request.item debug before reached fault failed⟩

/-- All ordinary item entries consume one fixed model and the actual complete
stream. Successful preparation supplies scratch capacity; the caller still
checks capacity before allocating scratch. Rejection is retained, and only a
reached miss needs a continuation proof. -/
theorem item_entry_projected (context : PairInput.Context σ)
    (ports : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → GraphObservations σ)
    (model : Interner.Primitives) (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before : World σ) (leading trailing : List ProtocolEvent) (other : Meaning) (read : Read) (sequence : BitVec 32)
    (good : Good source request.arguments before) (admitted : Admitted context.external)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (capacityQuery : model.atCapacity { before.graph with allocationCursor := leading.length } = context.queries.atCapacity before.graph)
    (classificationQuery : model.deterministic request.item = context.queries.deterministic request.item)
    (miss : EntryContinuation context ports model source request debug before leading trailing) :
    let actual := item context ports source request debug before leading
    let logical := Interner.Scoped.findDetailed (resources (actual.2.events ++ trailing) (.preparation .incomplete)) model request
      { before.graph with allocationCursor := leading.length }
    ordinary actual.1 = true →
      (actual.1, scopeView actual.2) = (logical.1.mapError Fault.language, logical.2) ∧ actual.2.tokens.incomplete = false := by
  intro actual logical completed
  cases made : prepare request.item debug before with
  | mk result constructed =>
    cases result with
    | error fault =>
      have rejected := (item_rejected context ports source request debug before constructed fault leading made).2
      rw [rejected] at completed
      cases completed
    | ok address =>
      have preparedItem := (prepare_success request.item debug before constructed address good.1 domain typed made).2
      obtain ⟨memory, allocated, checked⟩ := item_projected context ports model source request debug before constructed address
        leading trailing other read sequence good admitted domain typed made
        (by rw [preparedItem.graph]; exact capacityQuery) classificationQuery
      have continuation : MissContinuation context.external context.budget context.allocator
          (context.primitives source address (input request.item debug)) context.queries (ports source address (input request.item debug))
          model source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
          (start { constructed with memory := { constructed.memory with memory } } leading) trailing := by
        intro values key deterministic normalized taken room
        exact miss constructed address memory made room allocated values key deterministic room
      simpa only [preparedItem.graph] using checked continuation completed

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
