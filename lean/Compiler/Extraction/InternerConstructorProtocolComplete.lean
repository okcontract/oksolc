/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerProtocolComplete
import Compiler.Extraction.InternerConstructorProtocolFailure
import Compiler.Extraction.InternerConstructorProtocolReturn

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray Caller.ProtocolTrace Interner.InvocationTrace

/-- A typed actual item producer supplies scratch and returns every ordinary
caller outcome through the original two marks. The only remaining execution
obligation is the local reached miss; no successful initialization, classifier,
cache guard, take outcome, final scope or enclosing simulation is assumed.
This scoped observation is not yet raw graph/word constructor preservation. -/
theorem item_projected (context : PairInput.Context σ)
    (ports : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → GraphObservations σ)
    (model : Interner.Primitives) (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World σ) (address : Compiler.ZigAir.Memory.Address)
    (leading trailing : List ProtocolEvent) (other : Meaning) (read : Read) (sequence : BitVec 32)
    (good : Good source request.arguments before) (admitted : Admitted context.external)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (made : prepare request.item debug before = (.ok address, constructed))
    (capacityQuery : model.atCapacity { constructed.graph with allocationCursor := leading.length } = context.queries.atCapacity constructed.graph)
    (classificationQuery : model.deterministic request.item = context.queries.deterministic request.item) :
    ∃ memory, Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨constructed.memory.memory.nextId, 0⟩, memory) ∧
    (MissContinuation context.external context.budget context.allocator
      (context.primitives source address (input request.item debug)) context.queries (ports source address (input request.item debug))
      model source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      (start { constructed with memory := { constructed.memory with memory } } leading) trailing →
    let actual := item context ports source request debug before leading
    let logical := Interner.Scoped.findDetailed (resources (actual.2.events ++ trailing) (.preparation .incomplete)) model request
      { constructed.graph with allocationCursor := leading.length }
    ordinary actual.1 = true →
      (actual.1, scopeView actual.2) = (logical.1.mapError Fault.language, logical.2) ∧ actual.2.tokens.incomplete = false) := by
  obtain ⟨memory, allocated⟩ := prepare_scratch request.item debug before constructed address good.1 domain typed made
  refine ⟨memory, allocated, ?_⟩
  intro miss actual logical completed
  cases room : context.queries.atCapacity constructed.graph with
  | true =>
    exact (item_capacity_projected context ports model source request debug before constructed address leading trailing
      good domain typed made room capacityQuery).2.2.2
  | false =>
    have preparedItem := (prepare_success request.item debug before constructed address good.1 domain typed made).2
    have constructedGood := good_frame _ _ source request.arguments good preparedItem.valid preparedItem.memory
    have returned := (item_returned context ports source request debug before constructed address _ memory leading made room allocated).2.1
    let entry := start { constructed with memory := { constructed.memory with memory } } leading
    let p := context.primitives source address (input request.item debug)
    let observed := ports source address (input request.item debug)
    let buffer : View := ⟨constructed.memory.memory.nextId, 0, 2⟩
    let body := Caller.ProtocolTrace.findBody context.external context.budget context.allocator p context.queries observed source buffer request entry
    let called := Caller.ProtocolTrace.find context.external context.budget context.allocator p context.queries observed source buffer request entry
    have ordinaryCaller : ordinary called.1 = true := by
      have result := congrArg Prod.fst returned
      change actual.1 = called.1 at result
      rw [← result]
      exact completed
    have ordinaryBody : ordinary body.1 = true := by
      by_cases bodyCompleted : ordinary body.1 = true
      · exact bodyCompleted
      · change ordinary (Caller.ProtocolTrace.finish context.external context.allocator body.1 body.2).1 = true at ordinaryCaller
        simp only [Caller.ProtocolTrace.finish, bodyCompleted, Bool.false_eq_true, ↓reduceIte] at ordinaryCaller
    have checked := find_projected context.external context.budget context.allocator p context.queries observed model
      source request constructed memory _ leading trailing other read sequence constructedGood.1 constructedGood.2 allocated admitted
      capacityQuery classificationQuery miss ordinaryBody
    have events : actual.2.events = called.2.events := congrArg (fun result => result.2.2.1) returned
    have pairEq : (actual.1, scopeView actual.2) = (called.1, scopeView called.2) :=
      congrArg (fun result => (result.1, result.2.1)) returned
    refine ⟨?_, (congrArg (fun result => result.2.2.2) returned).trans checked.2⟩
    rw [pairEq]
    simpa only [logical, events] using checked.1

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
