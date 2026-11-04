/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerAllocationNativeWords
import Compiler.Extraction.InternerNativeConstructors

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Recursive Caller.ProtocolTrace

/-- Transfer complete captured replay and logical safety to the raw native
constructor. The stream is the actual complete run's history; erasure preserves
its result and world exactly. Consumers must derive both replay and safety. -/
theorem captured_constructor_words (meaning : Meaning) (frame : World (Publication.Effects σ) → Prop)
    (physical : GraphAction (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)) NodeId)
    (native : GraphAction (Publication.Effects σ) NodeId) (models : List ProtocolEvent → Interner.Action NodeId)
    (erases : Effect.Transport ChildTrace.erase physical native)
    (before : World (Publication.Effects σ)) (held : frame before) (expected : Word)
    (related : ∀ stream, Resource.Projects ChildTrace.history stream
      (cursorGraph (MissStream.childCursor 0 (ChildTrace.restore [] before)))
      (Frame (ChildTrace.restore [] before) frame) physical (models stream))
    (safe : ∀ stream, Interner.Safe meaning (models stream)
      (cursorGraph (MissStream.childCursor 0 (ChildTrace.restore [] before)) (ChildTrace.restore [] before))
      (fun id after => after.read id = some expected)) :
    ConstructorPost meaning frame before.graph (native before) expected := by
  let root : ChildTrace.TracedWorld σ ProtocolEvent := ChildTrace.restore [] before
  let stream := ChildTrace.history (physical root).2
  have erased := erases root
  simp only [root, ChildTrace.erase_restore] at erased
  intro completed
  rw [erased] at completed ⊢
  have initial : Frame root frame root := ⟨by simpa only [root, ChildTrace.erase_restore] using held, List.prefix_refl _⟩
  have admitted : Resource.Admitted ChildTrace.history stream physical root := List.prefix_refl _
  refine ⟨((related stream).run root initial admitted completed).1.1, ?_⟩
  exact (Semantic.Ensures.cursor_iff meaning root.graph (physical root).2.graph (physical root).1
    (MissStream.childCursor 0 root root) (MissStream.childCursor 0 root (physical root).2)
    (fun id read => read id = some expected)).mp
      ((related stream).safe ChildTrace.history stream _ _ physical (models stream) meaning root initial admitted _ (safe stream))

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
