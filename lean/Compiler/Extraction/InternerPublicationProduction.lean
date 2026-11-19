/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPublicationProofs

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray

def InsertionMemory (allocator : Nat) (source : View) (values : List NodeId)
    (p : Primitives (Effects σ)) : Prop :=
  ∀ key slice deterministic before, key.arguments = slice.items → Held allocator source values slice before →
    let executed := p.insert key slice deterministic before
    ordinary executed.1 = true → Good source values executed.2

def InsertionSemantics (allocator : Nat) (source : View) (values : List NodeId)
    (meaning : Meaning) (p : Primitives (Effects σ)) : Prop :=
  ∀ key slice deterministic before value, key.arguments = slice.items →
    Held allocator source values slice before → Interner.Invariant meaning before.graph →
    key.eval meaning before.graph.read = some value →
    let executed := p.insert key slice deterministic before
    Semantic.Ensures meaning before.graph executed.1 executed.2.graph (fun id after => after.read id = some value)

/-- Publication has no correctness premise. Its postconditions follow from
admission and the checked body. Native insertion remains a separate obligation. -/
theorem graph_contracts (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ) (allocator : Nat)
    (source : View) (values : List NodeId) (meaning : Meaning) (p : Primitives (Effects σ))
    (memoryInsert : InsertionMemory allocator source values p)
    (semanticInsert : InsertionSemantics allocator source values meaning p) :
    OwnedCall.GraphContracts allocator source values (callbacks hostProbe host allocator source p) ∧
    Semantic.GraphContracts allocator source values meaning (callbacks hostProbe host allocator source p) := by
  refine ⟨⟨?_, memoryInsert⟩, ⟨semanticInsert, ?_⟩⟩
  · intro key slice id before _ held completed
    have preserved := publish_held hostProbe host allocator source values key slice id before held completed
    exact ⟨preserved.1, fun _ _ => preserved.2.1⟩
  · intro key slice id before value _ _ valid evaluated actual
    exact publish_semantics hostProbe host allocator source key slice id before meaning value valid evaluated actual

/-- Both complete callers use the actual shared dispatcher and the concrete
admitted publication body, including normalization, transfer and cleanup.
Admission is transparent on accepted calls and rejects with a semantic fault.
Universal native admission, hash-map binding, insertion, queries and recursive
constructor simulation remain compiler obligations, not host assumptions. -/
theorem production_verified (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ)
    (budget allocator : Nat) (p : Primitives (Effects σ)) (q : Caller.Queries)
    (reads : Interner.Heap → Nested.Reads) (usizeBits : Nat) (find : Recursive.Find (Effects σ))
    (source : View) (request : Interner.Request) (id : NodeId) (before : World (Effects σ))
    (memory : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (env : AddressMask.Environment) (other : Meaning) (value : Word)
    (good : Good source request.arguments before)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (admitted : Admitted host)
    (memoryInsert : InsertionMemory allocator source request.arguments p)
    (semanticInsert : InsertionSemantics allocator source request.arguments (Dispatch.wordDispatchMeaning env other) p)
    (model : Associative.Constructors Unit)
    (coupled : ∀ slice, (Recursive.projection (Held allocator source request.arguments slice)).Constructors
      (Recursive.constructors find) model)
    (correct : Associative.ConstructorSound (Dispatch.wordBaseMeaning env other) model)
    (addresses : AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) model.operation)
    (shifts : ArithmeticShift.Constructs (AddressMask.addressMeaning env other) model.operation)
    (coherent : ∀ heap, Interner.Invariant (Dispatch.wordDispatchMeaning env other) heap →
      Nested.Sound (Dispatch.wordDispatchMeaning env other) heap.read (reads heap))
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read request.arguments request.sequence = some value) :
    let buffer : View := ⟨before.memory.memory.nextId, 0, 2⟩
    let input : World (Effects σ) := { before with memory := { before.memory with memory } }
    let actual := Recursive.callbacks (callbacks hostProbe host allocator source p) reads usizeBits find
    Semantic.Verified (external host) allocator source request.arguments (Dispatch.wordDispatchMeaning env other)
      (Caller.findBody (external host) budget allocator actual q source buffer request) input (fun id after => after.read id = some value) ∧
    (request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read request.arguments 0 = some value →
      before.graph.read id = some value →
      Semantic.Verified (external host) allocator source request.arguments (Dispatch.wordDispatchMeaning env other)
        (Caller.forceBody (external host) budget allocator actual q source buffer id request.item request.arguments) input (fun _ _ => True)) := by
  have contracts := graph_contracts hostProbe host allocator source request.arguments _ p memoryInsert semanticInsert
  exact Recursive.production_verified (external host) budget allocator (callbacks hostProbe host allocator source p) q
    reads usizeBits find source request id before memory pointer env other value good allocated
    (external_admitted host admitted) contracts.1 contracts.2 model coupled correct addresses shifts coherent valid evaluated

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication
