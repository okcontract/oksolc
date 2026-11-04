/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerProtocolFailure
import Compiler.Extraction.InternerConstructorProtocolReturn
import Compiler.Extraction.InternerConstructorEntryFailure
import Compiler.Extraction.InternerConstructorScratch

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray Caller.ProtocolTrace Interner.InvocationTrace

/-- The source item capacity branch returns through its original item mark.
Its complete scoped observation is the shared capacity leaf; there is no
scratch allocation or initializer premise on this route. -/
theorem item_capacity_projected (context : PairInput.Context σ)
    (ports : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → GraphObservations σ)
    (model : Interner.Primitives) (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World σ) (address : Compiler.ZigAir.Memory.Address) (leading trailing : List ProtocolEvent)
    (good : Good source request.arguments before)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (made : prepare request.item debug before = (.ok address, constructed))
    (full : context.queries.atCapacity constructed.graph = true)
    (capacityQuery : model.atCapacity { constructed.graph with allocationCursor := leading.length } = context.queries.atCapacity constructed.graph) :
    let actual := item context ports source request debug before leading
    let logical := Interner.Scoped.findDetailed (resources (actual.2.events ++ trailing) (.preparation .incomplete)) model request
      { constructed.graph with allocationCursor := leading.length }
    actual.1 = .error (.language .capacity) ∧ Good source request.arguments actual.2.native.world ∧ Closed actual.2.native.scope ∧
      (actual.1, scopeView actual.2) = (logical.1.mapError Fault.language, logical.2) ∧ actual.2.tokens.incomplete = false := by
  intro actual logical
  have prepared := (prepare_success request.item debug before constructed address good.1 domain typed made).2
  have native := invoke_capacity_failed context.external context.budget context.allocator (context.primitives source)
    context.queries source request debug before constructed address good domain typed made full
  have erased := item_erases context ports source request debug before leading
  change _ = (actual.1, actual.2.native) at erased
  rw [erased] at native
  let called := Caller.ProtocolTrace.find context.external context.budget context.allocator
    (context.primitives source address (input request.item debug)) context.queries
    (ports source address (input request.item debug)) source source request (start constructed leading)
  have callRun := capacity_recorded context.external context.budget context.allocator
    (context.primitives source address (input request.item debug)) context.queries
    (ports source address (input request.item debug)) source source request constructed leading full
  have checked := capacity_projected context.external context.budget context.allocator
    (context.primitives source address (input request.item debug)) context.queries
    (ports source address (input request.item debug)) model source source request constructed leading trailing
    (good_frame _ _ source request.arguments good prepared.valid prepared.memory) full capacityQuery
  have returned : outcome actual = outcome called := by
    change outcome (item context ports source request debug before leading) = _
    rw [item, made]
    simp only [frame, full, ↓reduceIte, retire_outcome]
    exact congrArg outcome callRun.symm
  have events : actual.2.events = called.2.events := congrArg (fun result => result.2.2.1) returned
  have pairEq : (actual.1, scopeView actual.2) = (called.1, scopeView called.2) :=
    congrArg (fun result => (result.1, result.2.1)) returned
  refine ⟨congrArg Prod.fst native.1, native.2.1, native.2.2.1, ?_, ?_⟩
  · rw [pairEq]
    simpa only [logical, events] using checked.2.2.2.1
  · exact (congrArg (fun result => result.2.2.2) returned).trans checked.2.2.2.2

/-- Typed item preparation derives the actual scratch allocation before the
failed initializer is inspected. The complete captured caller then returns
through both original marks, retaining its reached allocator effects and exact
scoped observation. No successful cleanup or enclosing simulation is assumed. -/
theorem item_initialization_failed_projected (context : PairInput.Context σ)
    (ports : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → GraphObservations σ)
    (model : Interner.Primitives) (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World σ) (address : Compiler.ZigAir.Memory.Address) (leading trailing : List ProtocolEvent)
    (other : Meaning) (read : Read) (sequence : BitVec 32)
    (good : Good source request.arguments before) (admitted : Admitted context.external)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (made : prepare request.item debug before = (.ok address, constructed))
    (room : context.queries.atCapacity constructed.graph = false)
    (capacityQuery : model.atCapacity { constructed.graph with allocationCursor := leading.length } = context.queries.atCapacity constructed.graph) :
    ∃ memory, Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨constructed.memory.memory.nextId, 0⟩, memory) ∧
    ∀ (fault : Fault) (reached : OwnedCall.State σ),
      Caller.initLookup context.external context.budget context.allocator source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
        ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩ = (.error fault, reached) →
      ordinary (.error fault : Except Fault NodeId) = true →
      let actual := item context ports source request debug before leading
      let logical := Interner.Scoped.findDetailed (resources (actual.2.events ++ trailing) (.preparation .incomplete)) model request
        { constructed.graph with allocationCursor := leading.length }
      actual.1 = .error fault ∧
        actual.2.native = { reached with world := returnWorld before.memory.memory.nextId constructed.memory.memory.nextId reached.world } ∧
        Good source request.arguments actual.2.native.world ∧ Closed actual.2.native.scope ∧
        (actual.1, scopeView actual.2) = (logical.1.mapError Fault.language, logical.2) ∧ actual.2.tokens.incomplete = false := by
  obtain ⟨memory, allocated⟩ := prepare_scratch request.item debug before constructed address good.1 domain typed made
  refine ⟨memory, allocated, ?_⟩
  intro fault reached failed completed actual logical
  have prepared := (prepare_success request.item debug before constructed address good.1 domain typed made).2
  have constructedGood := good_frame _ _ source request.arguments good prepared.valid prepared.memory
  have scratch := caller_buffer constructed.memory memory _ source request.arguments constructedGood.1 constructedGood.2 allocated
  have checked := initialization_failed_projected context.external context.budget context.allocator
    (context.primitives source address (input request.item debug)) context.queries
    (ports source address (input request.item debug)) model source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
    { constructed with memory := { constructed.memory with memory } } fault reached leading trailing other read sequence
    ⟨scratch.1, scratch.2.1⟩ scratch.2.2.1 rfl admitted room failed completed capacityQuery
  have returned := (item_returned context ports source request debug before constructed address _ memory leading made room allocated).2.1
  have native := invoke_init_failed context.external context.budget context.allocator (context.primitives source)
    context.queries source request debug before constructed address _ memory fault reached good admitted domain typed made room allocated
    failed completed
  have erased := item_erases context ports source request debug before leading
  change _ = (actual.1, actual.2.native) at erased
  rw [erased] at native
  let called := Caller.ProtocolTrace.find context.external context.budget context.allocator
    (context.primitives source address (input request.item debug)) context.queries
    (ports source address (input request.item debug)) source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
    (start { constructed with memory := { constructed.memory with memory } } leading)
  have events : actual.2.events = called.2.events := congrArg (fun result => result.2.2.1) returned
  have pairEq : (actual.1, scopeView actual.2) = (called.1, scopeView called.2) :=
    congrArg (fun result => (result.1, result.2.1)) returned
  refine ⟨native.1, congrArg Prod.snd native.2.1, native.2.2.1, native.2.2.2.1, ?_, ?_⟩
  · rw [pairEq]
    simpa only [logical, events] using checked.2.2.2.2.1
  · exact (congrArg (fun result => result.2.2.2) returned).trans checked.2.2.2.2.2

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
