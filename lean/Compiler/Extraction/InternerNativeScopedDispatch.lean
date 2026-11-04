/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeDispatch
import Compiler.Extraction.InternerCallerScopeProjection

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray Recursive

/-- The same shared dispatcher on the observed graph. Debug fields belong to
this constructor call; insertion and publication remain the seed operations. -/
def dispatchModel (seed : Interner.Primitives) (children : Associative.Constructors AssemblyItem.Fields.Values)
    (usizeBits : Nat) (debug : AssemblyItem.Fields.Values) : Interner.Primitives :=
  { seed with simplify := fun key before =>
      Dispatch.simplify (Interner.representativeReads before) children usizeBits key.instruction key.arguments debug before }

attribute [local irreducible] Dispatch.simplify

/-- Derive the actual native simplify step from proper children at this input.
The snapshot frame is needed during dispatch; it is not imposed on later
publication/insertion states that may release the normalized allocation. -/
theorem simplify_at (cursor : World (Publication.Effects σ) → Nat) (safety : Bool) (owner : Nat)
    (base : PairInput.Context (Publication.Effects σ)) (usizeBits : Nat)
    (children : Constructors (Publication.Effects σ)) (model : Associative.Constructors AssemblyItem.Fields.Values)
    (seed : Interner.Primitives) (debug : AssemblyItem.Fields.Values) (source : View) (values : List NodeId)
    (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized : ArgumentSlice) (rows : List Storage.Cell) (before : World (Publication.Effects σ))
    (predicate : World (Publication.Effects σ) → Prop) (initial : predicate before)
    {data : Compiler.ZigAir.Memory.Address} {capacity : Nat}
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (aligned : key.arguments = normalized.items) (held : Held base.allocator source values normalized before)
    (custody : Caller.GraphCustody base.allocator normalized rows before.memory)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys)
    (coupled : (projectionAt (cursorGraph cursor) (fun world => predicate world ∧
      InputFrame safety base.allocator owner rows source values normalized world)).SourceConstructorsAt (Nested.storageReads rows) debug children model) :
    let executed := ((context base owner usizeBits children debug).primitives source address native).simplify key normalized before
    let logical := (dispatchModel seed model usizeBits debug).simplify key (cursorGraph cursor before)
    ordinary executed.1 = true →
      (predicate executed.2 ∧ InputFrame safety base.allocator owner rows source values normalized executed.2) ∧
      executed.1 = logical.1.mapError Fault.language ∧ cursorGraph cursor executed.2 = logical.2 := by
  simp only [dispatcher_snapshot]
  rw [facts.reads]
  exact dispatch_projects_framed_at (cursorGraph cursor) safety owner base usizeBits children model debug source values
    key normalized rows before facts.projected aligned _ (fun _ frame => frame.2) coupled before
    ⟨initial, InputFrame.initial facts held custody privateSource⟩

/-- The native dispatcher supplies the first graph step of actual miss control.
Only proper children preserve the live dispatch frame. The seed publication and
insertion projections preserve the separate invariant after release/transfer. -/
theorem scoped_miss_at (cursor : World (Publication.Effects σ) → Nat) (safety : Bool) (owner : Nat)
    (base : PairInput.Context (Publication.Effects σ)) (usizeBits : Nat)
    (children : Constructors (Publication.Effects σ)) (model : Associative.Constructors AssemblyItem.Fields.Values)
    (seed : Interner.Primitives) (debug : AssemblyItem.Fields.Values) (source : View) (values : List NodeId)
    (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized : ArgumentSlice) (rows : List Storage.Cell) (before : State (Publication.Effects σ))
    (predicate : World (Publication.Effects σ) → Prop) (initial : predicate before.world)
    (resources : Interner.Scoped.Resources) (lookup : NormalizationOwnership.State) (items : List NodeId) (handle : Handle)
    (request : Interner.Request) (deterministic : Bool)
    (locals : before.scope.lookup = some handle ∧ before.scope.slice = some normalized)
    {data : Compiler.ZigAir.Memory.Address} {capacity : Nat}
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before.world rows)
    (aligned : key.arguments = normalized.items) (held : Held base.allocator source values normalized before.world)
    (custody : Caller.GraphCustody base.allocator normalized rows before.world.memory)
    (privateSource : Caller.SourcePrivate source before.world.memory.effects.keys)
    (coupled : (projectionAt (cursorGraph cursor) (fun world => predicate world ∧
      InputFrame safety base.allocator owner rows source values normalized world)).SourceConstructorsAt (Nested.storageReads rows) debug children model)
    (publishes : ∀ id, ProjectsAt (cursorGraph cursor) predicate
      ((base.primitives source address native).publish key normalized id) (seed.publish key id))
    (inserts : ProjectsAt (cursorGraph cursor) predicate
      ((base.primitives source address native).insert key normalized deterministic) (seed.insert key deterministic)) :
    let physical := (context base owner usizeBits children debug).primitives source address native
    let executed := Interner.findCode.controlMiss (OwnedCall.execution base.external base.allocator physical) request key deterministic before
    let logical := Interner.findCode.controlMiss (Interner.Scoped.execution resources (dispatchModel seed model usizeBits debug))
      request key deterministic (Caller.ScopeProjection.scopeAt (cursorGraph cursor) lookup items before)
    ordinary executed.1 = true → Caller.ScopeProjection.Frame predicate handle normalized executed.2 ∧
      executed.1 = logical.1.mapError Fault.language ∧
      Caller.ScopeProjection.scopeAt (cursorGraph cursor) lookup items executed.2 = logical.2 := by
  apply Caller.ScopeProjection.miss_at (cursorGraph cursor) predicate base.external base.allocator _ _ resources
    lookup items handle normalized request key deterministic before ⟨locals.1, locals.2, initial⟩
  · intro completed
    have projected := simplify_at cursor safety owner base usizeBits children model seed debug source values address native
      key normalized rows before.world predicate initial facts aligned held custody privateSource coupled completed
    exact ⟨projected.1.1, projected.2⟩
  · exact publishes
  · exact inserts

/-- An existing caller frame supplies the actual entry snapshot, including any
rows appended before dispatch. Proper-child simulation is instantiated at that
snapshot, so an older prefix is never mistaken for the current graph. -/
theorem scoped_miss_from_frame (cursor : World (Publication.Effects σ) → Nat) (safety : Bool) (owner : Nat)
    (base : PairInput.Context (Publication.Effects σ)) (usizeBits : Nat)
    (children : Constructors (Publication.Effects σ)) (model : Associative.Constructors AssemblyItem.Fields.Values)
    (seed : Interner.Primitives) (debug : AssemblyItem.Fields.Values) (source : View) (values : List NodeId)
    (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized : ArgumentSlice) (originalRows : List Storage.Cell) (before : State (Publication.Effects σ))
    (predicate : World (Publication.Effects σ) → Prop) (initial : predicate before.world)
    (resources : Interner.Scoped.Resources) (lookup : NormalizationOwnership.State) (items : List NodeId) (handle : Handle)
    (request : Interner.Request) (deterministic : Bool)
    (locals : before.scope.lookup = some handle ∧ before.scope.slice = some normalized)
    (input : InputFrame safety base.allocator owner originalRows source values normalized before.world)
    (aligned : key.arguments = normalized.items)
    (coupled : ∀ rows, (projectionAt (cursorGraph cursor) (fun world => predicate world ∧
      InputFrame safety base.allocator owner rows source values normalized world)).SourceConstructorsAt (Nested.storageReads rows) debug children model)
    (publishes : ∀ id, ProjectsAt (cursorGraph cursor) predicate
      ((base.primitives source address native).publish key normalized id) (seed.publish key id))
    (inserts : ProjectsAt (cursorGraph cursor) predicate
      ((base.primitives source address native).insert key normalized deterministic) (seed.insert key deterministic)) :
    let physical := (context base owner usizeBits children debug).primitives source address native
    let executed := Interner.findCode.controlMiss (OwnedCall.execution base.external base.allocator physical) request key deterministic before
    let logical := Interner.findCode.controlMiss (Interner.Scoped.execution resources (dispatchModel seed model usizeBits debug))
      request key deterministic (Caller.ScopeProjection.scopeAt (cursorGraph cursor) lookup items before)
    ordinary executed.1 = true → Caller.ScopeProjection.Frame predicate handle normalized executed.2 ∧
      executed.1 = logical.1.mapError Fault.language ∧
      Caller.ScopeProjection.scopeAt (cursorGraph cursor) lookup items executed.2 = logical.2 := by
  obtain ⟨added, data, capacity, facts, custody, privateSource⟩ := input.1
  exact scoped_miss_at cursor safety owner base usizeBits children model seed debug source values address native key normalized
    (originalRows ++ added) before predicate initial resources lookup items handle request deterministic locals facts aligned input.2
    custody privateSource (coupled (originalRows ++ added)) publishes inserts

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
