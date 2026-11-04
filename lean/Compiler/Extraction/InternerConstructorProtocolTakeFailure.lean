/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerProtocolTakeFailure
import Compiler.Extraction.InternerConstructorProtocolReturn
import Compiler.Extraction.InternerConstructorTakeFailure
import Compiler.Extraction.InternerConstructorScratch

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray Caller.ProtocolTrace Interner.InvocationTrace

/-- The actual item producer derives scratch allocation, then returns refused
borrowing through its two original cleanup marks. The native failure proof and
the recorded/scoped proof share the actual initialized and reached states. -/
theorem item_take_failed_projected (context : PairInput.Context σ)
    (ports : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → GraphObservations σ)
    (model : Interner.Primitives) (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World σ) (address : Compiler.ZigAir.Memory.Address) (commutative : Bool)
    (leading trailing : List ProtocolEvent) (other : Meaning) (read : Read) (sequence : BitVec 32)
    (good : Good source request.arguments before) (admitted : Admitted context.external)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (made : prepare request.item debug before = (.ok address, constructed))
    (room : context.queries.atCapacity constructed.graph = false)
    (decoded : Interner.Scoped.commutative request.item = .ok commutative)
    (capacityQuery : model.atCapacity { constructed.graph with allocationCursor := leading.length } = context.queries.atCapacity constructed.graph)
    (classificationQuery : model.deterministic request.item = context.queries.deterministic request.item) :
    ∃ memory, Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨constructed.memory.memory.nextId, 0⟩, memory) ∧
    ∀ (values : List NodeId) (prepared reached : OwnedCall.State σ) (fault : Fault) (key : Key) (deterministic : Bool),
      Caller.initLookup context.external context.budget context.allocator source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
        ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared) →
      context.queries.deterministic request.item = .ok deterministic →
      Interner.makeKey request values = .ok key →
      (deterministic = true → constructed.graph.table key = none) →
      OwnedCall.take context.external context.allocator prepared = (.error fault, reached) →
      let actual := item context ports source request debug before leading
      let logical := Interner.Scoped.findDetailed (resources (actual.2.events ++ trailing) (.preparation .incomplete)) model request
        { constructed.graph with allocationCursor := leading.length }
      fault = .language .outOfMemory ∧ actual.1 = .error fault ∧
        actual.2.native.world = returnWorld before.memory.memory.nextId constructed.memory.memory.nextId reached.world ∧
        Good source request.arguments actual.2.native.world ∧ Closed actual.2.native.scope ∧
        (actual.1, scopeView actual.2) = (logical.1.mapError Fault.language, logical.2) ∧ actual.2.tokens.incomplete = false := by
  obtain ⟨memory, allocated⟩ := prepare_scratch request.item debug before constructed address good.1 domain typed made
  refine ⟨memory, allocated, ?_⟩
  intro values prepared reached fault key deterministic initialized classified keyed absent failed actual logical
  have preparedItem := (prepare_success request.item debug before constructed address good.1 domain typed made).2
  have constructedGood := good_frame _ _ source request.arguments good preparedItem.valid preparedItem.memory
  have checked := take_failed_projected context.external context.budget context.allocator commutative
    (context.primitives source address (input request.item debug)) context.queries (ports source address (input request.item debug))
    model source request constructed memory _ values prepared reached fault key deterministic leading trailing other read sequence
    constructedGood.1 constructedGood.2 allocated decoded admitted initialized room classified keyed absent failed
    capacityQuery classificationQuery
  have returned := (item_returned context ports source request debug before constructed address _ memory leading made room allocated).2.1
  have native := invoke_take_failed context.external context.budget context.allocator (context.primitives source)
    context.queries source request debug before constructed address _ memory values prepared reached fault key deterministic
    good admitted domain typed made room allocated initialized classified keyed absent failed
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
  refine ⟨native.1, native.2.1, native.2.2.1, native.2.2.2.1, native.2.2.2.2.1, ?_, ?_⟩
  · rw [pairEq]
    simpa only [logical, events] using checked.2.2.2.2.1
  · exact (congrArg (fun result => result.2.2.2) returned).trans checked.2.2.2.2.2

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
