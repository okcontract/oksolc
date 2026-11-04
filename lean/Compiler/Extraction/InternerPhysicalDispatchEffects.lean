/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.DispatchEffects
import Compiler.Extraction.InternerPhysicalDispatch
import Compiler.Extraction.InternerOwnedMemoryEffects

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Recursive
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache

/-- Instantiate the existing dispatcher effect algebra with exact private-effect
erasure. Reads observe the same graph, including on failed child executions. -/
def erasing (project : σ → τ) : Dispatch.Effects (GraphAction σ) (GraphAction τ) where
  related := Effect.Transport (World.mapEffects project)
  pure := Effect.Transport.pure (World.mapEffects project)
  bind := Effect.Transport.bind (World.mapEffects project)
  lift := fun _ _ => rfl

theorem constructors_erase {Debug : Type} (project : σ → τ) (left : Find σ) (right : Find τ)
    (children : ∀ request, Effect.Transport (World.mapEffects project) (left request) (right request)) :
    (erasing project).Constructors (constructors (Debug := Debug) left) (constructors right) :=
  ⟨fun _ _ _ => children _, fun _ _ => children _, fun _ _ _ => children _,
   fun _ _ _ _ => children _, fun _ _ _ _ _ _ => children _⟩

/-- The source-bound dispatcher transports the same child request encoding.
This does not establish child erasure or record its internal resource events. -/
theorem simplify_erases (project : σ → τ) (left : Find σ) (right : Find τ)
    (children : ∀ request, Effect.Transport (World.mapEffects project) (left request) (right request))
    (p : Primitives σ) (q : Primitives τ) (reads : Interner.Heap → Nested.Reads) (usizeBits : Nat)
    (key : Key) (slice : ArgumentSlice) :
    Effect.Transport (World.mapEffects project)
      ((callbacks p reads usizeBits left).simplify key slice)
      ((callbacks q reads usizeBits right).simplify key slice) := by
  intro before
  exact (erasing project).simplify (constructors_erase project left right children)
    (reads before.graph) usizeBits key.instruction key.arguments () before

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Recursive
