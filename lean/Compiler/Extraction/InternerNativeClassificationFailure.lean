/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorClassificationFailure
import Compiler.Extraction.InternerNativeLookupReturn

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray

/-- Classification errors close an initialized proper-child leaf without a
child simulation or insertion premise. Native retention and semantic error
preservation specialize the same return used by cache hits. -/
theorem step_classification_failed_verified (base : PairInput.Context (Publication.Effects σ))
    (host : External σ) (owner usizeBits capacity : Nat) (safety : Bool)
    (children : Constructors (Publication.Effects σ)) (data : Compiler.ZigAir.Memory.Address) (rows : List Storage.Cell)
    (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World (Publication.Effects σ)) (address : Compiler.ZigAir.Memory.Address)
    (pointer : Compiler.ZigAir.Memory.Value) (memory : Compiler.ZigAir.Memory.State)
    (values : List NodeId) (prepared : State (Publication.Effects σ)) (error : Interner.Error)
    (other : Meaning) (expected : Word)
    (external : base.external = Publication.external host)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (represented : Represents before.memory.memory source request.arguments) (admitted : Admitted host)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (typed : AssemblyItem.Initializers.DebugTyped debug)
    (made : prepare request.item debug before = (.ok address, constructed))
    (room : base.queries.atCapacity constructed.graph = false)
    (allocated : Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) = .ok (pointer, memory))
    (initialized : Caller.initLookup base.external base.budget base.allocator source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (classified : base.queries.deterministic request.item = .error error)
    (completed : ordinary (.error (.language error) : Except Fault NodeId) = true)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph) :
    let actual := invoke base.external base.budget base.allocator
      ((context base owner usizeBits children debug).primitives source) base.queries source request debug before
    actual.1 = .error (.language error) ∧
      Returns (GraphFrame safety base.allocator owner rows (Retains before)) actual (.error (.language error)) before.graph ∧
      Semantic.Ensures (Folding.wordMeaning other) before.graph actual.1 actual.2.world.graph
        (fun id after => after.read id = some expected) ∧
      (∀ opcode borrowed, request = Interner.constructorCode.operationRequest opcode borrowed.items → source = view borrowed →
        (step base owner usizeBits children).borrowedOperation borrowed.address opcode borrowed.items debug before =
          (.error (.language error), actual.2.world)) := by
  apply step_initialized_verified base host owner usizeBits capacity safety children data rows source request debug
    before constructed address pointer memory values prepared (.error (.language error)) other expected external facts represented admitted
    domain typed made room allocated initialized completed
    (Caller.find_classification_failed base.external base.budget base.allocator
      ((context base owner usizeBits children debug).primitives source address (input request.item debug)) base.queries source
      ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      { constructed with memory := { constructed.memory with memory } } values prepared error room initialized classified) valid
  intro _ _ impossible
  cases impossible

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
