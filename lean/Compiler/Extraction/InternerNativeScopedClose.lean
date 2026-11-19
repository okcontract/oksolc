/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeScopedDispatch
import Compiler.Extraction.InternerCallerScopedClose

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray Recursive
open ResourceAdapter NormalizationOwnership.Trace

/-- Compose the actual native miss with its deferred cleanup and the close of
the same reached scoped state. Proper children supply dispatch preservation;
only insertion/publication keep explicit local graph and lifetime obligations.
The entry token and cleanup cursor must still be bound to the invocation. -/
theorem closed_miss_from_frame (cursor : World (Publication.Effects σ) → Nat) (safety : Bool) (owner : Nat)
    (base : PairInput.Context (Publication.Effects σ)) (usizeBits : Nat)
    (children : Constructors (Publication.Effects σ)) (model : Associative.Constructors AssemblyItem.Fields.Values)
    (seed : Interner.Primitives) (debug : AssemblyItem.Fields.Values) (source : View) (values : List NodeId)
    (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized : ArgumentSlice) (originalRows : List Storage.Cell) (before : State (Publication.Effects σ))
    (predicate : World (Publication.Effects σ) → Prop) (initial : predicate before.world)
    (lookup : NormalizationOwnership.State) (handle : Handle) (request : Interner.Request) (deterministic : Bool)
    (locals : before.scope = ⟨some handle, some normalized, false⟩)
    (detached : handle.owned = none) (unowned : lookup.owned = false) (caller : lookup.owner = .caller)
    (input : InputFrame safety base.allocator owner originalRows source values normalized before.world)
    (aligned : key.arguments = normalized.items)
    (coupled : ∀ rows, (projectionAt (cursorGraph cursor) (fun world => predicate world ∧
      InputFrame safety base.allocator owner rows source values normalized world)).SourceConstructorsAt (Nested.storageReads rows) debug children model)
    (publishes : ∀ id, ProjectsAt (cursorGraph cursor) predicate
      ((base.primitives source address native).publish key normalized id) (seed.publish key id))
    (inserts : ProjectsAt (cursorGraph cursor) predicate
      ((base.primitives source address native).insert key normalized deterministic) (seed.insert key deterministic))
    (publishLifetime : ∀ id world, predicate world → Held base.allocator source values normalized world →
      ordinary ((base.primitives source address native).publish key normalized id world).1 = true →
      Good source values ((base.primitives source address native).publish key normalized id world).2 ∧
        (∀ fault, ((base.primitives source address native).publish key normalized id world).1 = .error fault →
          SliceValid base.allocator ((base.primitives source address native).publish key normalized id world).2.memory.heap normalized))
    (insertLifetime : ∀ world, predicate world → Held base.allocator source values normalized world →
      ordinary ((base.primitives source address native).insert key normalized deterministic world).1 = true →
      Good source values ((base.primitives source address native).insert key normalized deterministic world).2)
    (leading suffix : List (Event Failure)) :
    let physical := (context base owner usizeBits children debug).primitives source address native
    let body := Interner.findCode.controlMiss (OwnedCall.execution base.external base.allocator physical) request key deterministic before
    ordinary body.1 = true → cursor body.2.world = leading.length →
    ∃ after, OwnedCall.finish base.external base.allocator body.1 body.2 = (body.1, after) ∧
      CleanupPost base.external base.allocator source values normalized body.2 after ∧ predicate body.2.world ∧
      let phase : NormalizationOwnership.Exit := if body.2.scope.handedOff then .transfer else .cleanup
      let execution := Caller.Close.capture base.external base.allocator lookup phase handle body.2
      let resources := Scope.resources (leading ++ (execution.2.events ++ suffix)) (.preparation .incomplete)
      let logical := Interner.findCode.controlMiss (Interner.Scoped.execution resources (dispatchModel seed model usizeBits debug))
        request key deterministic (Caller.ScopeProjection.scopeAt (cursorGraph cursor) lookup handle.values before)
      body.1 = logical.1.mapError Fault.language ∧
      logical.2 = Caller.ScopeProjection.scopeAt (cursorGraph cursor) lookup handle.values body.2 ∧
      after.world.memory = execution.2.effects.session ∧
      Caller.Close.checked execution leading suffix lookup logical.2.scope.phase logical.2.scope.items logical.2.heap =
        .ok (Interner.Scoped.close resources logical.2) := by
  intro physical body completed start
  obtain ⟨added, data, capacity, facts, custody, privateSource⟩ := input.1
  have simplifies := simplify_at cursor safety owner base usizeBits children model seed debug source values address native
    key normalized (originalRows ++ added) before.world predicate initial facts aligned input.2 custody privateSource
    (coupled (originalRows ++ added))
  have post := miss_post_at base.external base.allocator physical source values request key normalized handle deterministic
    before.world predicate initial input.2
    (fun ordinary => ⟨(simplifies ordinary).1.1, (simplifies ordinary).1.2.2⟩) publishLifetime insertLifetime
  have shape : (⟨before.world, ⟨some handle, some normalized, false⟩⟩ : State (Publication.Effects σ)) = before := by
    rw [← locals]
  rw [shape] at post
  have completion := Caller.Close.of_post base.external base.allocator source values lookup handle normalized body
    detached unowned caller post input.2.2.2 completed leading suffix
  let phase : NormalizationOwnership.Exit := if body.2.scope.handedOff then .transfer else .cleanup
  let execution := Caller.Close.capture base.external base.allocator lookup phase handle body.2
  let resources := Scope.resources (leading ++ (execution.2.events ++ suffix)) (.preparation .incomplete)
  have projected := scoped_miss_from_frame cursor safety owner base usizeBits children model seed debug source values address native
    key normalized originalRows before predicate initial resources lookup handle.values handle request deterministic
    ⟨congrArg Local.lookup locals, congrArg Local.slice locals⟩ input aligned coupled publishes inserts completed
  obtain ⟨after, finished, clean, reached, checked⟩ := Caller.ScopeProjection.close_completion base.external base.allocator
    source values lookup handle normalized body cursor leading suffix _ completion projected.2.2.symm start
  exact ⟨after, finished, clean, projected.1.2.2, projected.2.1, projected.2.2.symm, reached, checked⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
