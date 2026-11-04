/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPhysicalDispatchPreservation

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Recursive
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray

/-- Supply the actual dispatcher's ownership contract from recursive borrowing.
The seed simplifier is ignored and has no correctness premise. -/
theorem ownership_contracts (allocator : Nat) (source : View) (values : List NodeId)
    (p : Primitives σ) (graph : OwnedCall.GraphContracts allocator source values p)
    (reads : Interner.Heap → Nested.Reads) (usizeBits : Nat) (find : Find σ)
    (borrow : ∀ slice request, Keeps (Held allocator source values slice) (find request)) :
    OwnedCall.Contracts allocator source values (callbacks p reads usizeBits find) := by
  refine { publish := graph.publish, insert := graph.insert, simplify := ?_ }
  intro key slice before _aligned held
  exact simplify_borrows allocator source values p reads usizeBits find borrow key slice before held

/-- Derive both callback contract families for the same complete dispatcher.
Only insertion/publication and observed recursive constructor simulation remain premises;
there is no simplifier preservation or normalization correctness premise. -/
theorem caller_contracts_cursor (cursor : World σ → Nat) (allocator : Nat) (source : View) (values : List NodeId)
    (p : Primitives σ) (memory : OwnedCall.GraphContracts allocator source values p)
    (env : AddressMask.Environment) (other : Meaning)
    (graph : Semantic.GraphContracts allocator source values (Dispatch.wordDispatchMeaning env other) p)
    (reads : Interner.Heap → Nested.Reads) (usizeBits : Nat) (find : Find σ)
    (model : Associative.Constructors Unit)
    (coupled : ∀ slice, (projectionAt (cursorGraph cursor) (Held allocator source values slice)).Constructors (constructors find) model)
    (correct : Associative.ConstructorSound (Dispatch.wordBaseMeaning env other) model)
    (addresses : AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) model.operation)
    (shifts : ArithmeticShift.Constructs (AddressMask.addressMeaning env other) model.operation)
    (coherent : ∀ before, Interner.Invariant (Dispatch.wordDispatchMeaning env other) before →
      Nested.Sound (Dispatch.wordDispatchMeaning env other) before.read (reads before)) :
    OwnedCall.Contracts allocator source values (callbacks p reads usizeBits find) ∧
    Semantic.Contracts allocator source values (Dispatch.wordDispatchMeaning env other) (callbacks p reads usizeBits find) := by
  refine ⟨{ publish := memory.publish, insert := memory.insert, simplify := ?_ },
    { insert := graph.insert, publish := graph.publish, simplify := ?_ }⟩
  · intro key slice before _aligned held completed
    exact ((projectionAt (cursorGraph cursor) (Held allocator source values slice)).simplify (coupled slice)
      (reads before.graph) usizeBits key.instruction key.arguments () before held completed).1
  · intro key slice before value operation _aligned held valid evaluated
    exact (simplify_verified_cursor cursor (Held allocator source values slice) p reads usizeBits find model (coupled slice)
      env other correct addresses shifts key slice before value held operation valid (coherent before.graph valid) evaluated).2

/-- Derive both callback contract families for the same complete dispatcher.
Only insertion/publication and recursive constructor simulation remain premises;
there is no simplifier preservation or normalization correctness premise. -/
theorem caller_contracts (allocator : Nat) (source : View) (values : List NodeId)
    (p : Primitives σ) (memory : OwnedCall.GraphContracts allocator source values p)
    (env : AddressMask.Environment) (other : Meaning)
    (graph : Semantic.GraphContracts allocator source values (Dispatch.wordDispatchMeaning env other) p)
    (reads : Interner.Heap → Nested.Reads) (usizeBits : Nat) (find : Find σ)
    (model : Associative.Constructors Unit)
    (coupled : ∀ slice, (projection (Held allocator source values slice)).Constructors (constructors find) model)
    (correct : Associative.ConstructorSound (Dispatch.wordBaseMeaning env other) model)
    (addresses : AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) model.operation)
    (shifts : ArithmeticShift.Constructs (AddressMask.addressMeaning env other) model.operation)
    (coherent : ∀ before, Interner.Invariant (Dispatch.wordDispatchMeaning env other) before →
      Nested.Sound (Dispatch.wordDispatchMeaning env other) before.read (reads before)) :
    OwnedCall.Contracts allocator source values (callbacks p reads usizeBits find) ∧
    Semantic.Contracts allocator source values (Dispatch.wordDispatchMeaning env other) (callbacks p reads usizeBits find) :=
  caller_contracts_cursor (fun world => world.graph.allocationCursor) allocator source values p memory env other graph
    reads usizeBits find model coupled correct addresses shifts coherent

/-- Allocation, normalization, actual recursive dispatch, ownership transfer,
publication/insertion and cleanup compose on one production caller execution.
Observed constructor simulation and graph/query implementations remain named
compiler obligations; none are promoted to host assumptions. -/
theorem production_verified_cursor (cursor : World σ → Nat) (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries)
    (reads : Interner.Heap → Nested.Reads) (usizeBits : Nat) (find : Find σ)
    (source : View) (request : Interner.Request) (id : NodeId) (before : World σ)
    (memory : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (env : AddressMask.Environment) (other : Meaning) (value : Word)
    (good : Good source request.arguments before)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (admitted : Admitted external)
    (ownership : OwnedCall.GraphContracts allocator source request.arguments p)
    (graph : Semantic.GraphContracts allocator source request.arguments (Dispatch.wordDispatchMeaning env other) p)
    (model : Associative.Constructors Unit)
    (coupled : ∀ slice, (projectionAt (cursorGraph cursor) (Held allocator source request.arguments slice)).Constructors (constructors find) model)
    (correct : Associative.ConstructorSound (Dispatch.wordBaseMeaning env other) model)
    (addresses : AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) model.operation)
    (shifts : ArithmeticShift.Constructs (AddressMask.addressMeaning env other) model.operation)
    (coherent : ∀ heap, Interner.Invariant (Dispatch.wordDispatchMeaning env other) heap →
      Nested.Sound (Dispatch.wordDispatchMeaning env other) heap.read (reads heap))
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read request.arguments request.sequence = some value) :
    let buffer : View := ⟨before.memory.memory.nextId, 0, 2⟩
    let input : World σ := { before with memory := { before.memory with memory } }
    let actual := callbacks p reads usizeBits find
    Semantic.Verified external allocator source request.arguments (Dispatch.wordDispatchMeaning env other)
      (Caller.findBody external budget allocator actual q source buffer request) input (fun id after => after.read id = some value) ∧
    (request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read request.arguments 0 = some value →
      before.graph.read id = some value →
      Semantic.Verified external allocator source request.arguments (Dispatch.wordDispatchMeaning env other)
        (Caller.forceBody external budget allocator actual q source buffer id request.item request.arguments) input (fun _ _ => True)) := by
  have contracts := caller_contracts_cursor cursor allocator source request.arguments p ownership env other graph reads usizeBits find
    model coupled correct addresses shifts coherent
  exact Semantic.production_verified external budget allocator (callbacks p reads usizeBits find) q source request id before
    memory pointer (Dispatch.wordBaseMeaning env other) value good allocated admitted contracts.1 contracts.2 valid evaluated


/-- Allocation, normalization, actual recursive dispatch, ownership transfer,
publication/insertion and cleanup compose on one production caller execution.
Native constructor simulation and graph/query implementations remain named
compiler obligations; none are promoted to host assumptions. -/
theorem production_verified (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries)
    (reads : Interner.Heap → Nested.Reads) (usizeBits : Nat) (find : Find σ)
    (source : View) (request : Interner.Request) (id : NodeId) (before : World σ)
    (memory : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (env : AddressMask.Environment) (other : Meaning) (value : Word)
    (good : Good source request.arguments before)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (admitted : Admitted external)
    (ownership : OwnedCall.GraphContracts allocator source request.arguments p)
    (graph : Semantic.GraphContracts allocator source request.arguments (Dispatch.wordDispatchMeaning env other) p)
    (model : Associative.Constructors Unit)
    (coupled : ∀ slice, (projection (Held allocator source request.arguments slice)).Constructors (constructors find) model)
    (correct : Associative.ConstructorSound (Dispatch.wordBaseMeaning env other) model)
    (addresses : AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) model.operation)
    (shifts : ArithmeticShift.Constructs (AddressMask.addressMeaning env other) model.operation)
    (coherent : ∀ heap, Interner.Invariant (Dispatch.wordDispatchMeaning env other) heap →
      Nested.Sound (Dispatch.wordDispatchMeaning env other) heap.read (reads heap))
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read request.arguments request.sequence = some value) :
    let buffer : View := ⟨before.memory.memory.nextId, 0, 2⟩
    let input : World σ := { before with memory := { before.memory with memory } }
    let actual := callbacks p reads usizeBits find
    Semantic.Verified external allocator source request.arguments (Dispatch.wordDispatchMeaning env other)
      (Caller.findBody external budget allocator actual q source buffer request) input (fun id after => after.read id = some value) ∧
    (request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read request.arguments 0 = some value →
      before.graph.read id = some value →
      Semantic.Verified external allocator source request.arguments (Dispatch.wordDispatchMeaning env other)
        (Caller.forceBody external budget allocator actual q source buffer id request.item request.arguments) input (fun _ _ => True)) :=
  production_verified_cursor (fun world => world.graph.allocationCursor) external budget allocator p q reads usizeBits find
    source request id before memory pointer env other value good allocated admitted ownership graph model coupled
    correct addresses shifts coherent valid evaluated

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Recursive
