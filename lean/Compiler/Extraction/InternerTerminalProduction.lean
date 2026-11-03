/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerQueryProduction

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Terminal
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray

/-- This replacement is used only after proving equality of the complete
caller execution. It is never an interpretation of a reached recursive call. -/
def withoutSimplifier (p : Primitives σ) : Primitives σ :=
  { p with simplify := fun _ _ => pure none }

theorem force_independent (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Caller.Queries) (source buffer : View) (id : NodeId) (item : Item) (values : List NodeId) :
    Caller.forceBody external budget allocator (withoutSimplifier p) q source buffer id item values =
      Caller.forceBody external budget allocator p q source buffer id item values := rfl

theorem find_independent (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Caller.Queries) (source buffer : View) (request : Interner.Request)
    (terminal : request.item.kind ≠ 1) :
    Caller.findBody external budget allocator (withoutSimplifier p) q source buffer request =
      Caller.findBody external budget allocator p q source buffer request := by
  unfold Caller.findBody Interner.FindCode.controlRun Interner.FindCode.controlOwned Interner.FindCode.controlMiss
  simp only [beq_eq_false_iff_ne.mpr terminal, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem contracts (allocator : Nat) (source : View) (values : List NodeId) (p : Primitives σ)
    (meaning : Meaning) (memory : OwnedCall.GraphContracts allocator source values p)
    (words : Semantic.GraphContracts allocator source values meaning p) :
    OwnedCall.Contracts allocator source values (withoutSimplifier p) ∧
      Semantic.Contracts allocator source values meaning (withoutSimplifier p) := by
  refine ⟨{ publish := memory.publish, insert := memory.insert, simplify := ?_ },
    { publish := words.publish, insert := words.insert, simplify := ?_ }⟩
  · intro key slice before aligned held completed
    exact held
  · intro key slice before value operation aligned held valid evaluated
    exact Semantic.Ensures.pure meaning before.graph none _ valid (by simp)

/-- Complete non-operation find and every forceEqual execution use the actual
source-bound queries, normalization, insertion/publication and cleanup. Their
proofs require no recursive constructor model or simulation. Field/container
refinement and universal native admission remain separate obligations. -/
theorem production_verified (ops : Insertion.Operations σ)
    (select : Key → World (Publication.Effects σ) → AssemblyClone.Value Metadata)
    (budget allocator : Nat) (p : Primitives (Publication.Effects σ))
    (source : View) (request : Interner.Request) (id : NodeId) (before : World (Publication.Effects σ))
    (memory : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (other : Meaning) (value : Word)
    (good : Good source request.arguments before)
    (represented : before.graph.representatives.isSome = true)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (admitted : Admitted ops.arguments)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (evaluated : request.item.eval (Folding.wordMeaning other) before.graph.read request.arguments request.sequence = some value) :
    let buffer : View := ⟨before.memory.memory.nextId, 0, 2⟩
    let input : World (Publication.Effects σ) := { before with memory := { before.memory with memory } }
    let actual := Insertion.graphCallbacks ops allocator source (Folding.wordMeaning other) select p
    (request.item.kind ≠ 1 →
      Semantic.Verified (Publication.external ops.arguments) allocator source request.arguments (Folding.wordMeaning other)
        (Query.findBody (Publication.external ops.arguments) budget allocator actual source buffer request) input
        (fun id after => after.read id = some value)) ∧
    (request.item.eval (Folding.wordMeaning other) before.graph.read request.arguments 0 = some value →
      before.graph.read id = some value →
      Semantic.Verified (Publication.external ops.arguments) allocator source request.arguments (Folding.wordMeaning other)
        (Query.forceBody (Publication.external ops.arguments) budget allocator actual source buffer id request.item request.arguments) input
        (fun _ _ => True)) := by
  have graph := Insertion.graph_contracts ops allocator source request.arguments (Folding.wordMeaning other) select p admitted
  have checked := contracts allocator source request.arguments _ _ graph.1 graph.2
  have bodies := Semantic.production_verified (Publication.external ops.arguments) budget allocator _ Interner.Queries.queries
    source request id before memory pointer other value good allocated
    (Publication.external_admitted ops.arguments admitted) checked.1 checked.2 valid evaluated
  constructor
  · intro terminal
    apply Query.admitted_verified _ _ _ _ _ _ { before with memory := { before.memory with memory } } _ represented
    simpa only [find_independent _ _ _ _ _ _ _ _ terminal] using bodies.1
  · intro equation actual
    apply Query.admitted_verified _ _ _ _ _ _ { before with memory := { before.memory with memory } } _ represented
    simpa only [force_independent] using bodies.2 equation actual

/-- The equality premise remains essential: forceEqual publishes an existing
representative and does not establish equality by normalizing or cleaning up. -/
theorem force_verified (ops : Insertion.Operations σ)
    (select : Key → World (Publication.Effects σ) → AssemblyClone.Value Metadata)
    (budget allocator : Nat) (p : Primitives (Publication.Effects σ))
    (source : View) (item : Item) (values : List NodeId) (id : NodeId) (before : World (Publication.Effects σ))
    (memory : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (other : Meaning) (value : Word)
    (good : Good source values before) (represented : before.graph.representatives.isSome = true)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (admitted : Admitted ops.arguments) (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (evaluated : item.eval (Folding.wordMeaning other) before.graph.read values 0 = some value)
    (equal : before.graph.read id = some value) :
    let buffer : View := ⟨before.memory.memory.nextId, 0, 2⟩
    let input : World (Publication.Effects σ) := { before with memory := { before.memory with memory } }
    let actual := Insertion.graphCallbacks ops allocator source (Folding.wordMeaning other) select p
    Semantic.Verified (Publication.external ops.arguments) allocator source values (Folding.wordMeaning other)
      (Query.forceBody (Publication.external ops.arguments) budget allocator actual source buffer id item values) input
      (fun _ _ => True) :=
  (production_verified ops select budget allocator p source ⟨item, values, 0⟩ id before memory pointer other value
    good represented allocated admitted valid evaluated).2 evaluated equal

/-- Constant construction is a terminal production find, even when a caller
supplies a simplifier that fails or changes physical state. -/
theorem constant_verified (ops : Insertion.Operations σ)
    (select : Key → World (Publication.Effects σ) → AssemblyClone.Value Metadata)
    (budget allocator : Nat) (p : Primitives (Publication.Effects σ))
    (source : View) (before : World (Publication.Effects σ))
    (memory : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (other : Meaning) (value : Word) (pushes : Associative.Pushes other)
    (good : Good source [] before) (represented : before.graph.representatives.isSome = true)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (admitted : Admitted ops.arguments)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph) :
    let buffer : View := ⟨before.memory.memory.nextId, 0, 2⟩
    let input : World (Publication.Effects σ) := { before with memory := { before.memory with memory } }
    let actual := Insertion.graphCallbacks ops allocator source (Folding.wordMeaning other) select p
    Semantic.Verified (Publication.external ops.arguments) allocator source [] (Folding.wordMeaning other)
      (Query.findBody (Publication.external ops.arguments) budget allocator actual source buffer
        (Interner.constructorCode.constantRequest value)) input (fun id after => after.read id = some value) := by
  have evaluated : (Interner.constructorCode.constantRequest value).item.eval (Folding.wordMeaning other)
      before.graph.read [] 0 = some value := by
    simpa [Interner.constructorCode, Interner.ConstructorCode.constantRequest, Scalar.run, Item.eval,
      readArguments, Folding.wordMeaning] using pushes value
  exact (production_verified ops select budget allocator p source (Interner.constructorCode.constantRequest value) 0
    before memory pointer other value good represented allocated admitted valid evaluated).1 (by change (2 : Kind) ≠ 1; decide)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Terminal
