/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeLeafFrame

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray

/-- Lift a derived native caller postcondition to an unchanged-graph step leaf.
Entry proofs discharge these local premises before applying this composition
lemma; it is not a production preservation theorem by itself. -/
theorem step_return_verified (base : PairInput.Context (Publication.Effects σ))
    (owner usizeBits capacity : Nat) (safety : Bool) (children : Constructors (Publication.Effects σ))
    (data : Compiler.ZigAir.Memory.Address) (rows : List Storage.Cell)
    (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before : World (Publication.Effects σ)) (outcome : Except Fault NodeId) (other : Meaning) (expected : Word) :
    let actual := invoke base.external base.budget base.allocator
      ((context base owner usizeBits children debug).primitives source) base.queries source request debug before
    ∀ (_result : actual.1 = outcome)
    (_native : NativeGraph.Facts safety base.allocator owner data capacity
      actual.2.world rows)
    (_closed : Closed actual.2.scope)
    (_graph : actual.2.world.graph = before.graph)
    (_keys : actual.2.world.memory.effects.keys = before.memory.effects.keys)
    (_memory : ∀ id cell, before.memory.memory.heap.lookup id = some cell →
      actual.2.world.memory.memory.heap.lookup id = some cell)
    (_registry : ∀ id block, before.memory.heap id = some block →
      actual.2.world.memory.heap id = some block)
    (_valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (_word : ∀ id, outcome = .ok id → before.graph.read id = some expected),
    actual.1 = outcome ∧
      Returns (GraphFrame safety base.allocator owner rows (Retains before)) actual outcome before.graph ∧
      Semantic.Ensures (Folding.wordMeaning other) before.graph actual.1 actual.2.world.graph
        (fun id after => after.read id = some expected) ∧
      (∀ opcode borrowed, request = Interner.constructorCode.operationRequest opcode borrowed.items → source = view borrowed →
        (step base owner usizeBits children).borrowedOperation borrowed.address opcode borrowed.items debug before =
          (outcome, actual.2.world)) := by
  dsimp only
  intro result native closed graph keys memory registry valid word
  refine ⟨result, ?_, ?_, ?_⟩
  · intro _
    exact ⟨closed, ⟨⟨[], data, capacity, by simpa only [List.append_nil] using native⟩, keys, memory, registry⟩, result, graph⟩
  · rw [result, graph]
    cases outcome with
    | error error => exact Semantic.Ensures.error _ _ _ _ valid
    | ok id => exact Semantic.Ensures.pure _ _ _ _ valid (word id rfl)
  · intro opcode borrowed requestEq sourceEq
    subst request source
    exact Prod.ext result rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
