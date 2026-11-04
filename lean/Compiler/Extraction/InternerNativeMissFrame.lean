/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeFrames

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Recursive

/-- Native suffix obligations at the actual reached world. They require no
logical heap equality or insertion/publication model. Child failure and
publication are needed only on the source's simplification branch. -/
structure MissFrames (external : External σ) (allocator : Nat) (p : Primitives σ)
    (ready frame : World σ → Prop) (key : Key) (slice : ArgumentSlice) (lookup : Handle)
    (deterministic simplifying : Bool) : Prop where
  insertion : ∀ world, ready world →
    let ran := (do let _ ← handoff; graph (fun slice => p.insert key slice deterministic) : Action σ NodeId)
      ⟨world, ⟨some lookup, some slice, false⟩⟩
    FramePost frame (OwnedCall.finish external allocator ran.1 ran.2)
  publication : simplifying = true → ∀ world id, ready world →
    let ran := (do
      let _ ← graph (fun slice => p.publish key slice (Interner.findCode.published.run id))
      let _ ← handoff
      pure (Interner.findCode.simplified.run id) : Action σ NodeId)
      ⟨world, ⟨some lookup, some slice, false⟩⟩
    FramePost frame (OwnedCall.finish external allocator ran.1 ran.2)
  failure : simplifying = true → ∀ world fault, ready world →
    FramePost frame (OwnedCall.finish external allocator (.error fault : Except Fault NodeId)
      ⟨world, ⟨some lookup, some slice, false⟩⟩)

/-- Preserve native scope and frame through the complete owned miss. Proper
children need only retain the reached input frame; no raw-cursor simulation is
used. Both success branches and ordinary failure keep the child's reached world. -/
theorem miss_frame (external : External σ) (allocator : Nat) (p : Primitives σ)
    (ready frame : World σ → Prop) (request : Interner.Request) (key : Key)
    (slice : ArgumentSlice) (lookup : Handle) (deterministic : Bool)
    (before : World σ) (initial : ready before)
    (steps : MissFrames external allocator p ready frame key slice lookup deterministic
      (deterministic && (request.item.kind == 1)))
    (simplifies : (deterministic && (request.item.kind == 1)) = true →
      ordinary (p.simplify key slice before).1 = true → ready (p.simplify key slice before).2) :
    let ran := Interner.findCode.controlMiss (OwnedCall.execution external allocator p) request key deterministic
      ⟨before, ⟨some lookup, some slice, false⟩⟩
    FramePost frame (OwnedCall.finish external allocator ran.1 ran.2) := by
  dsimp only
  unfold Interner.FindCode.controlMiss
  by_cases branch : (deterministic && (request.item.kind == 1)) = true
  · simp only [branch, ↓reduceIte, OwnedCall.execution]
    cases called : p.simplify key slice before with
    | mk result middle =>
      cases result with
      | error fault =>
        simp only [graph, called, bind, Effect.bind]
        intro completed
        have ordinaryChild : ordinary (.error fault : Except Fault (Option NodeId)) = true := by
          cases rejected : ordinary (.error fault : Except Fault NodeId) with
          | false => simp only [OwnedCall.finish, rejected, Bool.false_eq_true, ↓reduceIte] at completed
          | true => exact rejected
        have checked := simplifies branch (by rw [called]; exact ordinaryChild)
        simp only [called] at checked
        exact steps.failure branch middle fault checked completed
      | ok found =>
        have checked := simplifies branch (by rw [called]; rfl)
        simp only [called] at checked
        cases found with
        | none =>
          simpa only [graph, called, bind, Effect.bind, pure, Effect.pure] using steps.insertion middle checked
        | some id =>
          simpa only [graph, called, bind, Effect.bind, pure, Effect.pure] using steps.publication branch middle id checked
  · simpa only [branch, Bool.false_eq_true, ↓reduceIte, OwnedCall.execution, bind, Effect.bind, pure, Effect.pure] using
      steps.insertion before initial

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
