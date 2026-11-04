/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionCaller

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open AssemblyClone (Value)

/-- The descriptor provider observes the reached world. Its native field
projection is explicitly outside the current admitted execution theorem. -/
def insertionCallbacks (ops : Operations σ) (allocator : Nat) (source : View) (meaning : Meaning)
    (select : Key → World (Publication.Effects σ) → Value Metadata) (p : Primitives (Publication.Effects σ)) :
    Primitives (Publication.Effects σ) :=
  { p with insert := fun key slice deterministic before => insert ops allocator source meaning (select key before) key slice deterministic before }

def graphCallbacks (ops : Operations σ) (allocator : Nat) (source : View) (meaning : Meaning)
    (select : Key → World (Publication.Effects σ) → Value Metadata) (p : Primitives (Publication.Effects σ)) :
    Primitives (Publication.Effects σ) :=
  Publication.callbacks ops.probe ops.arguments allocator source (insertionCallbacks ops allocator source meaning select p)

theorem insertion_memory (ops : Operations σ) (allocator : Nat) (source : View) (values : List NodeId)
    (meaning : Meaning) (select : Key → World (Publication.Effects σ) → Value Metadata)
    (p : Primitives (Publication.Effects σ)) (admitted : Admitted ops.arguments) :
    Publication.InsertionMemory allocator source values (insertionCallbacks ops allocator source meaning select p) := by
  intro key slice deterministic before _ held
  dsimp only [insertionCallbacks, insert]
  cases represented : before.graph.representatives with
  | none => simp [ordinary, Fault.recoverable]
  | some cells => exact body_memory ops allocator source values meaning (select key before) key slice deterministic cells before held.1 admitted

theorem insertion_semantics (ops : Operations σ) (allocator : Nat) (source : View) (values : List NodeId)
    (meaning : Meaning) (select : Key → World (Publication.Effects σ) → Value Metadata)
    (p : Primitives (Publication.Effects σ)) (admitted : Admitted ops.arguments) :
    Publication.InsertionSemantics allocator source values meaning (insertionCallbacks ops allocator source meaning select p) := by
  intro key slice deterministic before value _ held valid evaluated
  dsimp only [insertionCallbacks, insert]
  cases represented : before.graph.representatives with
  | none => exact Semantic.Ensures.error meaning before.graph _ _ valid
  | some cells =>
    exact body_semantics ops allocator source meaning (select key before) key slice deterministic cells before value
      represented held.1.1 admitted valid evaluated

/-- Both graph obligations follow from the same physical insertion and
publication execution. Neither callback's whole postcondition is a premise. -/
theorem graph_contracts (ops : Operations σ) (allocator : Nat) (source : View) (values : List NodeId)
    (meaning : Meaning) (select : Key → World (Publication.Effects σ) → Value Metadata)
    (p : Primitives (Publication.Effects σ)) (admitted : Admitted ops.arguments) :
    OwnedCall.GraphContracts allocator source values (graphCallbacks ops allocator source meaning select p) ∧
    Semantic.GraphContracts allocator source values meaning (graphCallbacks ops allocator source meaning select p) :=
  Publication.graph_contracts ops.probe ops.arguments allocator source values meaning _
    (insertion_memory ops allocator source values meaning select p admitted)
    (insertion_semantics ops allocator source values meaning select p admitted)

/-- Complete physical find/force callers with concrete allocation, clone,
argument ownership, publication and cleanup. The shared recursive dispatcher is
composed under its existing constructor contracts. Native fields/containers,
universal admission and recursive constructor simulation remain open; the fixed
host boundary is unchanged. -/
theorem production_verified (ops : Operations σ)
    (select : Key → World (Publication.Effects σ) → Value Metadata)
    (budget allocator : Nat) (p : Primitives (Publication.Effects σ)) (q : Caller.Queries)
    (reads : Interner.Heap → Nested.Reads) (usizeBits : Nat) (find : Recursive.Find (Publication.Effects σ))
    (source : View) (request : Interner.Request) (id : NodeId) (before : World (Publication.Effects σ))
    (memory : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (env : AddressMask.Environment) (other : Meaning) (value : Word)
    (good : Good source request.arguments before)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (admitted : Admitted ops.arguments)
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
    let input : World (Publication.Effects σ) := { before with memory := { before.memory with memory } }
    let actual := Recursive.callbacks (graphCallbacks ops allocator source (Dispatch.wordDispatchMeaning env other) select p) reads usizeBits find
    Semantic.Verified (Publication.external ops.arguments) allocator source request.arguments (Dispatch.wordDispatchMeaning env other)
      (Caller.findBody (Publication.external ops.arguments) budget allocator actual q source buffer request) input (fun id after => after.read id = some value) ∧
    (request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read request.arguments 0 = some value →
      before.graph.read id = some value →
      Semantic.Verified (Publication.external ops.arguments) allocator source request.arguments (Dispatch.wordDispatchMeaning env other)
        (Caller.forceBody (Publication.external ops.arguments) budget allocator actual q source buffer id request.item request.arguments) input (fun _ _ => True)) := by
  exact Publication.production_verified ops.probe ops.arguments budget allocator
    (insertionCallbacks ops allocator source (Dispatch.wordDispatchMeaning env other) select p) q reads usizeBits find
    source request id before memory pointer env other value good allocated admitted
    (insertion_memory ops allocator source request.arguments _ select p admitted)
    (insertion_semantics ops allocator source request.arguments _ select p admitted)
    model coupled correct addresses shifts coherent valid evaluated

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion
