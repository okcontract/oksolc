/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPhysicalOwned

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Semantic
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray

/-- Word preservation for the exact complete physical find body. The successful
normalizer projection comes from its checked memory execution, not a sort or
normalization oracle supplied by the caller. -/
theorem find_body_safe (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries)
    (source buffer : View) (request : Interner.Request) (before : World σ) (other : Meaning) (value : Word)
    (good : Good source request.arguments before)
    (scratch : ∀ commutative : Bool, commutative = true → 2 ≤ source.length → source.length ≤ buffer.length → Scratch source buffer before.memory)
    (admitted : Admitted external) (memory : OwnedCall.Contracts allocator source request.arguments p)
    (contracts : Contracts allocator source request.arguments (Folding.wordMeaning other) p)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (evaluated : request.item.eval (Folding.wordMeaning other) before.graph.read request.arguments request.sequence = some value) :
    let executed := Caller.findBody external budget allocator p q source buffer request ⟨before, { lookup := none }⟩
    Ensures (Folding.wordMeaning other) before.graph executed.1 executed.2.world.graph (fun id after => after.read id = some value) := by
  let meaning := Folding.wordMeaning other
  unfold Caller.findBody Interner.FindCode.controlRun
  simp only [Caller.execution, OwnedCall.execution, bind, Effect.bind]
  by_cases capacity : q.atCapacity before.graph = true
  · simp only [capacity, ↓reduceIte, Except.mapError]
    exact Ensures.error meaning before.graph _ _ valid
  · simp only [capacity, Bool.false_eq_true, ↓reduceIte, Effect.bind]
    cases initialized : Caller.initLookup external budget allocator source buffer request ⟨before, { lookup := none }⟩ with
    | mk result after =>
      have checked := Caller.initialize_verified external budget allocator source buffer request before good scratch admitted
      have graphSame := Caller.initialize_graph external budget allocator source buffer request ⟨before, { lookup := none }⟩
      rw [initialized] at checked graphSame
      dsimp only at graphSame
      cases result with
      | error fault => simpa only [graphSame] using Ensures.error meaning before.graph fault _ valid
      | ok args =>
        obtain ⟨handle, scope, ready, same, normalized⟩ := checked
        rcases after with ⟨world, localScope⟩
        dsimp only at scope ready graphSame
        subst localScope
        subst args
        have argsBefore : request.item.eval meaning before.graph.read handle.values request.sequence = some value :=
          (Compiler.Extraction.InsertionSort.normalize_word other request.item request.arguments handle.values before.graph.read request.sequence normalized).trans evaluated
        have currentValid : Interner.Invariant meaning world.graph := by rw [graphSame]; exact valid
        have argsCurrent : request.item.eval meaning world.graph.read handle.values request.sequence = some value := by rw [graphSame]; exact argsBefore
        cases deterministic : q.deterministic request.item with
        | error error =>
          simp only [Except.mapError]
          simpa only [graphSame] using Ensures.error meaning before.graph (.language error) _ valid
        | ok flag =>
          simp only [Except.mapError]
          cases flag with
          | false =>
            simpa only [graphSame] using owned_safe external allocator p request false handle source request.arguments world
              meaning value ready admitted memory contracts currentValid argsCurrent
          | true =>
            simp only [↓reduceIte, Effect.bind]
            cases keyed : Interner.makeKey request handle.values with
            | error error =>
              dsimp only
              simpa only [graphSame] using Ensures.error meaning before.graph (.language error) _ valid
            | ok key =>
              dsimp only
              have keyValue := Interner.makeKey_sound meaning before.graph request handle.values value key argsBefore keyed
              cases found : before.graph.table key with
              | some id =>
                obtain ⟨cached, cachedKey, actual⟩ := valid.cache key id found
                have same : cached = value := by rw [keyValue] at cachedKey; exact Option.some.inj cachedKey.symm
                subst cached
                simpa only [pure, Effect.pure, Interner.findCode, Interner.ResultId.run, graphSame] using
                  Ensures.pure meaning before.graph id _ valid actual
              | none =>
                simpa only [graphSame] using owned_safe external allocator p request true handle source request.arguments world
                  meaning value ready admitted memory contracts currentValid argsCurrent

/-- The complete physical forceEqual body retains the equality premise needed
to publish a correct representative. Cleanup never supplies that premise. -/
theorem force_body_safe (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries)
    (source buffer : View) (id : NodeId) (item : Item) (values : List NodeId) (before : World σ) (other : Meaning) (value : Word)
    (good : Good source values before)
    (scratch : ∀ commutative : Bool, commutative = true → 2 ≤ source.length → source.length ≤ buffer.length → Scratch source buffer before.memory)
    (admitted : Admitted external) (contracts : GraphContracts allocator source values (Folding.wordMeaning other) p)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (evaluated : item.eval (Folding.wordMeaning other) before.graph.read values 0 = some value)
    (actual : before.graph.read id = some value) :
    let executed := Caller.forceBody external budget allocator p q source buffer id item values ⟨before, { lookup := none }⟩
    Ensures (Folding.wordMeaning other) before.graph executed.1 executed.2.world.graph (fun _ _ => True) := by
  let meaning := Folding.wordMeaning other
  unfold Caller.forceBody Interner.ForceCode.controlRun
  simp only [Caller.execution, OwnedCall.execution, bind, Effect.bind]
  cases validated : q.validate id before.graph with
  | error error =>
    simp only [Except.mapError]
    exact Ensures.error meaning before.graph _ _ valid
  | ok returned =>
    cases returned
    simp only [Except.mapError]
    cases initialized : Caller.initLookup external budget allocator source buffer ⟨item, values, 0⟩ ⟨before, { lookup := none }⟩ with
    | mk result after =>
      have checked := Caller.initialize_verified external budget allocator source buffer ⟨item, values, 0⟩ before good scratch admitted
      have graphSame := Caller.initialize_graph external budget allocator source buffer ⟨item, values, 0⟩ ⟨before, { lookup := none }⟩
      rw [initialized] at checked graphSame
      dsimp only at graphSame
      cases result with
      | error fault => simpa only [graphSame] using Ensures.error meaning before.graph fault _ valid
      | ok args =>
        obtain ⟨handle, scope, ready, same, normalized⟩ := checked
        rcases after with ⟨world, localScope⟩
        dsimp only at scope ready graphSame
        subst localScope
        subst args
        have argsBefore : item.eval meaning before.graph.read handle.values 0 = some value :=
          (Compiler.Extraction.InsertionSort.normalize_word other item values handle.values before.graph.read 0 normalized).trans evaluated
        have currentValid : Interner.Invariant meaning world.graph := by rw [graphSame]; exact valid
        have argsCurrent : item.eval meaning world.graph.read handle.values 0 = some value := by rw [graphSame]; exact argsBefore
        have actualCurrent : world.graph.read id = some value := by rw [graphSame]; exact actual
        cases keyed : Interner.makeKey ⟨item, values, 0⟩ handle.values with
        | error error =>
          simp only [keyed]
          simpa only [graphSame] using Ensures.error meaning before.graph (.language error) _ valid
        | ok key =>
          simp only [keyed]
          cases found : before.graph.table key with
          | some existing =>
            simpa only [pure, Effect.pure, graphSame] using Ensures.pure meaning before.graph () (fun _ _ => True) valid trivial
          | none =>
            simpa only [graphSame] using force_owned_safe external allocator p ⟨item, values, 0⟩ id handle source values world
              meaning value ready admitted contracts currentValid argsCurrent actualCurrent

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Semantic
