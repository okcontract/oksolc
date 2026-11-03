/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerProtocolInduction
import Compiler.Extraction.InternerConstructorResourceEntries

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Caller.ProtocolTrace
open NativeRecursion Recursive Interner.InvocationTrace

/-- The complete item entry now consumes proper-child induction data instead
of a caller/miss simulation premise. Actual item preparation supplies source
validity; only a reached taken miss needs a native frame and a binding of the
fixed entry model to the child's dispatcher and recorded suffix ports.
Deriving those local data, native frame/word preservation and finite induction
remain separate obligations. -/
theorem item_induction_projected
    (ops : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (allocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (safety : Bool) (owner : Nat) (meaning : Meaning)
    (base : PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (growth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent))) (usizeBits : Nat)
    (children : Constructors (Publication.Effects σ)) (observations : ChildTrace.Observations σ ProtocolEvent)
    (model : Interner.Primitives) (debug : AssemblyItem.Fields.Values) (source : View) (request : Interner.Request)
    (before : ChildTrace.TracedWorld σ ProtocolEvent) (leading trailing : List ProtocolEvent)
    (other : Meaning) (read : Read) (sequence : BitVec 32)
    (good : Good source request.arguments before) (admitted : Admitted (Publication.external ops.arguments))
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (capacityQuery : model.atCapacity { before.graph with allocationCursor := leading.length } = base.queries.atCapacity before.graph)
    (classificationQuery : model.deterministic request.item = base.queries.deterministic request.item)
    (induction : ∀ (constructed : ChildTrace.TracedWorld σ ProtocolEvent)
      (address : Compiler.ZigAir.Memory.Address) (memory : Compiler.ZigAir.Memory.State),
      prepare request.item debug before = (.ok address, constructed) →
      base.queries.atCapacity constructed.graph = false →
      Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) =
        .ok (.pointer (.pointer true false (.array 2 word)) ⟨constructed.memory.memory.nextId, 0⟩, memory) →
      Caller.ProtocolTrace.Native.EntryInduction ops allocate safety owner meaning base growth usizeBits children observations
        debug source address (input request.item debug) request model ⟨constructed.memory.memory.nextId, 0, 2⟩
        (start { constructed with memory := { constructed.memory with memory } } leading) trailing) :
    EntryProjected model request before.graph leading trailing
      (item (NativeRecursion.context (callerContext ops allocate safety owner meaning base growth) owner usizeBits
        (ChildTrace.constructors children observations) debug)
        (Caller.ProtocolTrace.Native.graphObservations ops allocate safety owner meaning base growth usizeBits
          (ChildTrace.constructors children observations) (ChildTrace.liftObservations observations) debug)
        source request debug before leading) := by
  apply ResourceEntry.item_projected ops allocate safety owner meaning base growth usizeBits children observations debug
    model source request before leading trailing other read sequence good admitted domain typed capacityQuery classificationQuery
  intro constructed address memory made room allocated
  exact Caller.ProtocolTrace.Native.ResourceEntry.EntryInduction.of_unrestricted ops allocate safety owner meaning base growth usizeBits
    children observations debug source address (input request.item debug) request model ⟨constructed.memory.memory.nextId, 0, 2⟩
    (start { constructed with memory := { constructed.memory with memory } } leading) trailing
    (induction constructed address memory made room allocated)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
