/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeScopedClose

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray Recursive
open ResourceAdapter NormalizationOwnership.Trace

/-- The actual successful take supplies the native slice, detached lookup and
recorded token used by native miss and checked close. Source/argument alignment
comes from that same take; no independent token-ownership premise remains.
Local graph contracts and the invocation-wide resource stream remain open. -/
theorem closed_miss_after_take (cursor : World (Publication.Effects σ) → Nat) (safety : Bool) (owner : Nat)
    (base : PairInput.Context (Publication.Effects σ)) (usizeBits : Nat)
    (children : Constructors (Publication.Effects σ)) (model : Associative.Constructors AssemblyItem.Fields.Values)
    (seed : Interner.Primitives) (debug : AssemblyItem.Fields.Values) (source : View) (values : List NodeId)
    (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized : ArgumentSlice) (originalRows : List Storage.Cell)
    (before : World (Publication.Effects σ)) (handle remaining : Handle) (called : State (Publication.Effects σ))
    (origin : NormalizationOwnership.Origin)
    (ready : Ready base.allocator source values handle before.memory) (admitted : Admitted base.external)
    (transferred : OwnedCall.take base.external base.allocator ⟨before, { lookup := some handle }⟩ = (.ok (), called))
    (predicate : World (Publication.Effects σ) → Prop) (initial : predicate called.world)
    (request : Interner.Request) (deterministic : Bool)
    (locals : called.scope = ⟨some remaining, some normalized, false⟩)
    (input : InputFrame safety base.allocator owner originalRows source values normalized called.world)
    (aligned : key.arguments = handle.values)
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
    let lookup := (Caller.Take.capture base.external base.allocator origin handle before.memory).1.2
    Normalization.Taken base.allocator source values handle before.memory normalized remaining called.world.memory ∧
    let physical := (context base owner usizeBits children debug).primitives source address native
    let body := Interner.findCode.controlMiss (OwnedCall.execution base.external base.allocator physical) request key deterministic called
    ordinary body.1 = true → cursor body.2.world = leading.length →
    ∃ after, OwnedCall.finish base.external base.allocator body.1 body.2 = (body.1, after) ∧
      CleanupPost base.external base.allocator source values normalized body.2 after ∧ predicate body.2.world ∧
      let phase : NormalizationOwnership.Exit := if body.2.scope.handedOff then .transfer else .cleanup
      let execution := Caller.Close.capture base.external base.allocator lookup phase remaining body.2
      let resources := Scope.resources (leading ++ (execution.2.events ++ suffix)) (.preparation .incomplete)
      let logical := Interner.findCode.controlMiss (Interner.Scoped.execution resources (dispatchModel seed model usizeBits debug))
        request key deterministic (Caller.ScopeProjection.scopeAt (cursorGraph cursor) lookup remaining.values called)
      body.1 = logical.1.mapError Fault.language ∧
      logical.2 = Caller.ScopeProjection.scopeAt (cursorGraph cursor) lookup remaining.values body.2 ∧
      after.world.memory = execution.2.effects.session ∧
      Caller.Close.checked execution leading suffix lookup logical.2.scope.phase logical.2.scope.items logical.2.heap =
        .ok (Interner.Scoped.close resources logical.2) := by
  have succeeded := congrArg Prod.fst transferred
  obtain ⟨unowned, ownerToken, actual, detached, scope, memory⟩ :=
    Caller.Close.take_success base.external base.allocator origin source values handle before ready admitted succeeded
  rw [transferred] at scope memory
  have same := Local.mk.inj (scope.symm.trans locals)
  cases Option.some.inj same.1
  cases Option.some.inj same.2.1
  refine ⟨memory, ?_⟩
  exact closed_miss_from_frame cursor safety owner base usizeBits children model seed debug source values address native
    key normalized originalRows called predicate initial _ remaining request deterministic locals memory.detached unowned ownerToken
    input (aligned.trans memory.values.symm) coupled publishes inserts publishLifetime insertLifetime leading suffix

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
