/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeMissFrame

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul

/-- Word obligations for actual completed suffixes at the reached native world.
They retain cleanup outcomes but require no raw logical heap equality. Only the
source simplification branch requires publication and child-failure cleanup. -/
structure MissWords (external : External σ) (allocator : Nat) (p : Primitives σ)
    (ready : World σ → Prop) (meaning : Meaning) (expected : Word)
    (key : Key) (slice : ArgumentSlice) (lookup : Handle) (deterministic simplifying : Bool) : Prop where
  insertion : ∀ world, ready world → Interner.Invariant meaning world.graph →
    key.eval meaning world.graph.read = some expected →
    let ran := (do let _ ← handoff; graph (fun slice => p.insert key slice deterministic) : Action σ NodeId)
      ⟨world, ⟨some lookup, some slice, false⟩⟩
    let actual := OwnedCall.finish external allocator ran.1 ran.2
    Semantic.Ensures meaning world.graph actual.1 actual.2.world.graph (fun id after => after.read id = some expected)
  publication : simplifying = true → ∀ world id, ready world → Interner.Invariant meaning world.graph →
    key.eval meaning world.graph.read = some expected → world.graph.read id = some expected →
    let ran := (do
      let _ ← graph (fun slice => p.publish key slice (Interner.findCode.published.run id))
      let _ ← handoff
      pure (Interner.findCode.simplified.run id) : Action σ NodeId)
      ⟨world, ⟨some lookup, some slice, false⟩⟩
    let actual := OwnedCall.finish external allocator ran.1 ran.2
    Semantic.Ensures meaning world.graph actual.1 actual.2.world.graph (fun id after => after.read id = some expected)
  failure : simplifying = true → ∀ world fault, ready world → Interner.Invariant meaning world.graph →
    let actual := OwnedCall.finish external allocator (.error fault : Except Fault NodeId)
      ⟨world, ⟨some lookup, some slice, false⟩⟩
    Semantic.Ensures meaning world.graph actual.1 actual.2.world.graph (fun id after => after.read id = some expected)

/-- Compose child words with reached suffix semantics on the same actual miss.
No whole-miss simulation is assumed. Child stability transports the original
key's value before insertion/publication; failure keeps the reached child graph. -/
theorem miss_words (external : External σ) (allocator : Nat) (p : Primitives σ)
    (ready : World σ → Prop) (meaning : Meaning) (expected : Word)
    (request : Interner.Request) (key : Key) (slice : ArgumentSlice) (lookup : Handle)
    (deterministic : Bool) (before : World σ) (initial : ready before)
    (valid : Interner.Invariant meaning before.graph) (evaluated : key.eval meaning before.graph.read = some expected)
    (steps : MissWords external allocator p ready meaning expected key slice lookup deterministic
      (deterministic && (request.item.kind == 1)))
    (childFrame : (deterministic && (request.item.kind == 1)) = true →
      ordinary (p.simplify key slice before).1 = true → ready (p.simplify key slice before).2)
    (childWords : (deterministic && (request.item.kind == 1)) = true →
      Semantic.Ensures meaning before.graph (p.simplify key slice before).1 (p.simplify key slice before).2.graph
        (fun found after => ∀ id, found = some id → after.read id = some expected)) :
    let ran := Interner.findCode.controlMiss (OwnedCall.execution external allocator p) request key deterministic
      ⟨before, ⟨some lookup, some slice, false⟩⟩
    let actual := OwnedCall.finish external allocator ran.1 ran.2
    Semantic.Ensures meaning before.graph actual.1 actual.2.world.graph (fun id after => after.read id = some expected) := by
  dsimp only
  unfold Interner.FindCode.controlMiss
  by_cases branch : (deterministic && (request.item.kind == 1)) = true
  · simp only [branch, ↓reduceIte, OwnedCall.execution]
    cases called : p.simplify key slice before with
    | mk result middle =>
      have words := childWords branch
      have retained := childFrame branch
      simp only [called] at words retained
      cases result with
      | error fault =>
        simp only [graph, called, bind, Effect.bind]
        intro completed
        have ordinaryChild : ordinary (.error fault : Except Fault (Option NodeId)) = true := by
          cases rejected : ordinary (.error fault : Except Fault NodeId) with
          | false => simp only [OwnedCall.finish, rejected, Bool.false_eq_true, ↓reduceIte] at completed
          | true => exact rejected
        have semantic := words ordinaryChild
        exact Semantic.Ensures.extend meaning before.graph middle.graph _ _ _ semantic.2.1
          (steps.failure branch middle fault (retained ordinaryChild) semantic.1) completed
      | ok found =>
        have semantic := words rfl
        have keyMiddle := key_stable meaning before.graph.read middle.graph.read semantic.2.1 key expected evaluated
        cases found with
        | none =>
          simpa only [graph, called, bind, Effect.bind, pure, Effect.pure] using
            Semantic.Ensures.extend meaning before.graph middle.graph _ _ _ semantic.2.1
              (steps.insertion middle (retained rfl) semantic.1 keyMiddle)
        | some id =>
          simpa only [graph, called, bind, Effect.bind, pure, Effect.pure] using
            Semantic.Ensures.extend meaning before.graph middle.graph _ _ _ semantic.2.1
              (steps.publication branch middle id (retained rfl) semantic.1 keyMiddle (semantic.2.2 id rfl))
  · simpa only [branch, Bool.false_eq_true, ↓reduceIte, OwnedCall.execution, bind, Effect.bind, pure, Effect.pure] using
      steps.insertion before initial valid evaluated

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
