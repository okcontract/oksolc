/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerEnclosingFrames
import Compiler.Extraction.InternerNativeStep

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray

/-- All enclosing publication and failure frames follow from original child
provenance and the actual reached frame. Only insertion's native frame remains
an input. The publication proof uses the actual probe decision directly and needs no
logical primitive family. -/
theorem Enclosing.missFrames {safety : Bool} {allocator owner : Nat}
    {parent : World (Publication.Effects σ) → Prop} (stack : Enclosing safety allocator owner parent)
    {before : World (Publication.Effects σ)} (initial : parent before)
    {source : View} {request : Interner.Request} {values : List NodeId}
    {taken : State (Publication.Effects σ)} {owned : ArgumentSlice} {lookup : Handle}
    (origin : Caller.Origin allocator source request values before taken owned lookup)
    (rows : List Storage.Cell) (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue)
    (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ)
    (p : Primitives (Publication.Effects σ))
    (published : p.publish = Publication.publish hostProbe host allocator source)
    (key : Key) (deterministic simplifying : Bool) (aligned : key.arguments = owned.items)
    (insertion : ∀ world, CallFrame safety allocator owner rows source request.arguments owned address native parent world →
      let ran := (do let _ ← handoff; graph (fun slice => p.insert key slice deterministic) : Action (Publication.Effects σ) NodeId)
        ⟨world, ⟨some lookup, some owned, false⟩⟩
      FramePost (GraphFrame safety allocator owner rows parent) (OwnedCall.finish (Publication.external host) allocator ran.1 ran.2)) :
    MissFrames (Publication.external host) allocator p
      (CallFrame safety allocator owner rows source request.arguments owned address native parent)
      (GraphFrame safety allocator owner rows parent) key owned lookup deterministic simplifying where
  insertion := insertion
  failure := by
    intro _ world fault frame
    obtain ⟨added, data, capacity, facts, custody, _⟩ := frame.1.1
    exact (frame.failure host lookup origin.detached fault (fun after freed =>
      stack.release initial frame.parent origin host facts.projected custody freed)).framePost
  publication := by
    intro _ world id frame
    have returned := frame.publication_action hostProbe host key id lookup origin.detached aligned
      (fun key id => Interner.publish (hostProbe key (Publication.forget world.memory)).1 key id) rfl
      (stack.publish initial origin frame hostProbe host key id aligned)
      (fun reached after rows held projected custody freed => stack.release initial held origin host projected custody freed)
    simpa only [published] using returned.framePost


end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
