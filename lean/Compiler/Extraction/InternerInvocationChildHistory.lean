/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorProtocolTrace
import Compiler.Extraction.InternerInvocationChildTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ChildTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray ConstructorItem.ProtocolTrace

/-- Observe an already traced child at the same underlying native input. Its
earlier history is bookkeeping, never an argument to the child observation. -/
def liftObservations (observations : Observations σ ε) : Observations (Recorded σ ε) ε :=
  mapConstructors (fun observe before => observe (erase before)) observations

/-- Keep the outer history when comparing two nested recordings with one.
The inner history may have an unrelated prefix; no equality is assumed. -/
def flatten (effects : Recorded (Recorded σ ε) ε) : Recorded σ ε :=
  (effects.1.1, effects.2)

theorem record_flatten (action : GraphAction (Publication.Effects σ) α)
    (observe : World (Publication.Effects σ) → List ε) :
    Effect.Transport (World.mapEffects (Publication.Effects.mapAllocator flatten))
      (record (record action observe) (fun before => observe (erase before))) (record action observe) := by
  intro before
  simp only [record, erase, history, restore, flatten, World.mapEffects, Session.mapEffects,
    Publication.Effects.mapAllocator]

/-- Every constructor field consumes the same request, native input and child
observation in both history layers. This includes failure and unchanged worlds. -/
theorem constructors_flatten (children : Constructors (Publication.Effects σ)) (observations : Observations σ ε) :
    (Recursive.erasing (Publication.Effects.mapAllocator flatten)).Constructors
      (constructors (constructors children observations) (liftObservations observations)) (constructors children observations) :=
  ⟨fun _ _ _ => record_flatten _ _, fun _ _ => record_flatten _ _, fun _ _ _ => record_flatten _ _,
   fun _ _ _ _ => record_flatten _ _, fun _ _ _ _ _ _ => record_flatten _ _⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ChildTrace
