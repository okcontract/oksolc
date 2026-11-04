/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorJointEntries
import Compiler.Extraction.InternerNativeFrameEffects
import Compiler.Extraction.InternerRecursiveProtocolEffects

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Caller.ProtocolTrace NativeRecursion

/-- The same capture retains its scoped protocol observation, caller closure,
native frame and words when only allocator-private instrumentation is erased. -/
theorem JointPost.mapAllocator (project : σ → τ) {model : Interner.Primitives} {request : Interner.Request}
    {before : Interner.Heap} {leading trailing : List ProtocolEvent} {meaning : Meaning}
    {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell} {parent : World (Publication.Effects τ) → Prop}
    {actual : Except Fault NodeId × Recorded (Publication.Effects σ)} {expected : Word}
    (post : JointPost model request before leading trailing meaning
      (GraphFrame safety allocator owner rows (fun world => parent (world.mapEffects (Publication.Effects.mapAllocator project)))) actual expected) :
    JointPost model request before leading trailing meaning (GraphFrame safety allocator owner rows parent)
      (mapReturn (Publication.Effects.mapAllocator project) actual) expected := by
  refine ⟨EntryProjected.of_outcome (mapReturn_outcome _ actual) post.1, ?_⟩
  intro completed
  obtain ⟨closed, frame, words⟩ := post.2 completed
  exact ⟨closed, frame.mapAllocator project, words⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
