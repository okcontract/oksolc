/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerQueries
import Compiler.Extraction.InternerInsertionProduction

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Query
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open AssemblyClone (Value)
open Interner.Queries (queries admit)

def findBody (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (source buffer : View) (request : Interner.Request) : Action σ NodeId :=
  admit (Caller.findBody external budget allocator p queries source buffer request)

def forceBody (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (source buffer : View) (id : NodeId) (item : Item) (values : List NodeId) : Action σ Unit :=
  admit (Caller.forceBody external budget allocator p queries source buffer id item values)

theorem admitted_verified (external : External σ) (allocator : Nat) (source : View) (values : List NodeId)
    (meaning : Meaning) (action : Action σ α) (before : World σ) (post : α → Interner.Heap → Prop)
    (represented : before.graph.representatives.isSome = true)
    (checked : Semantic.Verified external allocator source values meaning action before post) :
    Semantic.Verified external allocator source values meaning (admit action) before post := by
  simpa only [Semantic.Verified, Caller.Verified, Caller.invoke, admit, represented, if_true] using checked

/-- Both complete physical caller bodies, with the actual source-bound queries
and representative readers. No capacity, determinism, validation or read-soundness
oracle is supplied. Insertion, publication and normalization remain the same
checked execution; recursive constructor simulation and native graph/field
refinement remain explicit outstanding obligations. -/
theorem production_verified (ops : Insertion.Operations σ)
    (select : Key → World (Publication.Effects σ) → Value Metadata)
    (budget allocator : Nat) (p : Primitives (Publication.Effects σ))
    (usizeBits : Nat) (find : Recursive.Find (Publication.Effects σ))
    (source : View) (request : Interner.Request) (id : NodeId) (before : World (Publication.Effects σ))
    (memory : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (env : AddressMask.Environment) (other : Meaning) (value : Word)
    (good : Good source request.arguments before)
    (represented : before.graph.representatives.isSome = true)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (admitted : Admitted ops.arguments)
    (model : Associative.Constructors Unit)
    (coupled : ∀ slice, (Recursive.projection (Held allocator source request.arguments slice)).Constructors
      (Recursive.constructors find) model)
    (correct : Associative.ConstructorSound (Dispatch.wordBaseMeaning env other) model)
    (addresses : AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) model.operation)
    (shifts : ArithmeticShift.Constructs (AddressMask.addressMeaning env other) model.operation)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read request.arguments request.sequence = some value) :
    let buffer : View := ⟨before.memory.memory.nextId, 0, 2⟩
    let input : World (Publication.Effects σ) := { before with memory := { before.memory with memory } }
    let actual := Recursive.callbacks (Insertion.graphCallbacks ops allocator source (Dispatch.wordDispatchMeaning env other) select p)
      Interner.representativeReads usizeBits find
    Semantic.Verified (Publication.external ops.arguments) allocator source request.arguments (Dispatch.wordDispatchMeaning env other)
      (findBody (Publication.external ops.arguments) budget allocator actual source buffer request) input
      (fun id after => after.read id = some value) ∧
    (request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read request.arguments 0 = some value →
      before.graph.read id = some value →
      Semantic.Verified (Publication.external ops.arguments) allocator source request.arguments (Dispatch.wordDispatchMeaning env other)
        (forceBody (Publication.external ops.arguments) budget allocator actual source buffer id request.item request.arguments) input (fun _ _ => True)) := by
  have checked := Insertion.production_verified ops select budget allocator p queries Interner.representativeReads usizeBits find
    source request id before memory pointer env other value good allocated admitted model coupled correct addresses shifts
    (fun heap invariant => Interner.representative_reads_sound _ heap invariant) valid evaluated
  exact ⟨admitted_verified _ _ _ _ _ _ _ _ represented checked.1,
    fun equation actual => admitted_verified _ _ _ _ _ _ _ _ represented (checked.2 equation actual)⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Query
