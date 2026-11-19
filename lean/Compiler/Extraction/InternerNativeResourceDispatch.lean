/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerResourceProjection
import Compiler.Extraction.InternerNativeDispatchFrames

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray Recursive

theorem operand_grows (history : World σ → List Event) (source : ArgumentSlice) (index : Nat) (annotation : NodeId) :
    Resource.Grows history (operand source index annotation) := by
  intro before
  rw [operand_world]
  exact List.prefix_refl _

theorem resource_read_bind (history : World σ → List Event) (stream : List Event)
    (observe : World σ → Interner.Heap) (predicate : World σ → Prop) :
    Dispatch.Effects.ReadBind (Resource.projection history stream observe predicate) where
  bind := by
    intro α β result nextLeft nextRight following
    cases result with
    | ok value => exact following value rfl
    | error error =>
      cases error <;> exact ⟨fun _ => List.prefix_refl _, fun _ held _ _ => ⟨held, rfl, rfl⟩⟩

/-- Actual native reads reuse their existing memory proof. They emit no
resource events, so resource admission adds no new read-value premise. -/
theorem InputFrame.resource_queries {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    (history : World (Publication.Effects σ) → List Event) (stream : List Event)
    (observe : World (Publication.Effects σ) → Interner.Heap) (predicate : World (Publication.Effects σ) → Prop)
    (input : ∀ world, predicate world → InputFrame safety allocator owner rows source values normalized world)
    (heap : Interner.Heap) (projected : heap.representatives = some rows) :
    Dispatch.Effects.Inputs (Resource.projection history stream observe predicate)
      (Interner.representativeReads heap) operand where
  queried := by
    intro id opcode slice found index annotation item
    exact Resource.Projects.of_projects history stream observe predicate _ _ (operand_grows history slice index annotation)
      ((InputFrame.queries_at observe predicate input heap projected).queried id opcode slice found index annotation item)

theorem InputFrame.resource_root {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    (history : World (Publication.Effects σ) → List Event) (stream : List Event)
    (observe : World (Publication.Effects σ) → Interner.Heap) (predicate : World (Publication.Effects σ) → Prop)
    (input : ∀ world, predicate world → InputFrame safety allocator owner rows source values normalized world) :
    Dispatch.Effects.SliceInput (Resource.projection history stream observe predicate) operand normalized := by
  intro index annotation item
  exact Resource.Projects.of_projects history stream observe predicate _ _ (operand_grows history normalized index annotation)
    (InputFrame.root_at observe predicate input index annotation item)

/-- The complete shared dispatcher consumes resource-conditional proper-child
laws. Bind derives each reached child's admission from the actual whole trace;
no uniform model agreement or admission of every structural frame is assumed. -/
theorem dispatch_resource_projected (history : World (Publication.Effects σ) → List Event) (stream : List Event)
    (observe : World (Publication.Effects σ) → Interner.Heap) (safety : Bool) (owner : Nat)
    (base : PairInput.Context (Publication.Effects σ)) (usizeBits : Nat)
    (children : Constructors (Publication.Effects σ)) (model : Associative.Constructors AssemblyItem.Fields.Values)
    (debug : AssemblyItem.Fields.Values) (source : View) (values : List NodeId)
    (key : Key) (normalized : ArgumentSlice) (rows : List Storage.Cell) (snapshot : Interner.Heap)
    (projected : snapshot.representatives = some rows) (aligned : key.arguments = normalized.items)
    (predicate : World (Publication.Effects σ) → Prop)
    (input : ∀ world, predicate world → InputFrame safety base.allocator owner rows source values normalized world)
    (proper : (Resource.projection history stream observe predicate).SourceConstructorsAt
      (Nested.storageReads rows) debug children model) :
    Resource.Projects history stream observe predicate
      (Dispatch.simplifyWithInputs (Interner.representativeReads snapshot) children usizeBits
        key.instruction key.arguments debug operand normalized.address)
      (Dispatch.simplify (Interner.representativeReads snapshot) model usizeBits key.instruction key.arguments debug) := by
  exact Dispatch.Effects.simplify_with_inputs_at _ (resource_read_bind history stream observe predicate) _ operand
    (InputFrame.resource_queries history stream observe predicate input snapshot projected) debug
    (by simpa only [Interner.representativeReads, projected] using proper) usizeBits key.instruction key.arguments normalized.address
    (by simpa only [aligned] using InputFrame.resource_root history stream observe predicate input)

/-- Apply the resource-aware dispatcher proof to the actual native reads and
execution. The stream is fixed for this invocation; it may record ordinary OOM.
Frame preservation and exact result/observed-graph correspondence are derived
only for the actions whose actual history fits that stream. -/
theorem dispatcher_resource_projected (history : World (Publication.Effects σ) → List Event) (stream : List Event)
    (observe : World (Publication.Effects σ) → Interner.Heap) (safety : Bool) (owner usizeBits : Nat)
    (base : PairInput.Context (Publication.Effects σ)) (children : Constructors (Publication.Effects σ))
    (model : Associative.Constructors AssemblyItem.Fields.Values) (debug : AssemblyItem.Fields.Values)
    (source : View) (values : List NodeId) (address : Compiler.ZigAir.Memory.Address)
    (native : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (rows : List Storage.Cell) (before : World (Publication.Effects σ)) (data : Compiler.ZigAir.Memory.Address) (capacity : Nat)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (aligned : key.arguments = normalized.items) (predicate : World (Publication.Effects σ) → Prop)
    (initial : predicate before)
    (input : ∀ world, predicate world → InputFrame safety base.allocator owner rows source values normalized world)
    (proper : (Resource.projection history stream observe predicate).SourceConstructorsAt
      (Nested.storageReads rows) debug children model) :
    let action := ((context base owner usizeBits children debug).primitives source address native).simplify key normalized
    let logical := Dispatch.simplify (Nested.storageReads rows) model usizeBits key.instruction key.arguments debug
    Resource.Admitted history stream action before → ordinary (action before).1 = true →
      predicate (action before).2 ∧ (action before).1 = (logical (observe before)).1.mapError Fault.language ∧
      observe (action before).2 = (logical (observe before)).2 := by
  dsimp only
  intro admitted completed
  simp only [Resource.Admitted, dispatcher_snapshot] at admitted completed ⊢
  have reads : NativeReads.reads owner before.memory.memory = Interner.representativeReads before.graph := facts.reads
  rw [reads] at admitted completed ⊢
  have checked := dispatch_resource_projected history stream observe safety owner base usizeBits children model debug source values
    key normalized rows before.graph facts.projected aligned predicate input proper
  simpa only [Interner.representativeReads, facts.projected] using checked.run before initial admitted completed

/-- Select the fixed resource stream from the same complete native dispatcher
execution. Admission is derived, not supplied. The observer counts that exact
history, and the proper-child laws must hold for this stream, including OOM.
Correctness of the child recorder and the recursive child laws remain to prove. -/
theorem dispatcher_captured_projected (history : World (Publication.Effects σ) → List Event)
    (trailing : List Event) (safety : Bool) (owner usizeBits : Nat)
    (base : PairInput.Context (Publication.Effects σ)) (children : Constructors (Publication.Effects σ))
    (model : Associative.Constructors AssemblyItem.Fields.Values) (debug : AssemblyItem.Fields.Values)
    (source : View) (values : List NodeId) (address : Compiler.ZigAir.Memory.Address)
    (native : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (rows : List Storage.Cell) (before : World (Publication.Effects σ)) (data : Compiler.ZigAir.Memory.Address) (capacity : Nat)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (aligned : key.arguments = normalized.items) (predicate : World (Publication.Effects σ) → Prop)
    (initial : predicate before)
    (input : ∀ world, predicate world → InputFrame safety base.allocator owner rows source values normalized world) :
    let action := ((context base owner usizeBits children debug).primitives source address native).simplify key normalized
    let stream := history (action before).2 ++ trailing
    let observe := cursorGraph (fun world => (history world).length)
    let logical := Dispatch.simplify (Nested.storageReads rows) model usizeBits key.instruction key.arguments debug
    (Resource.projection history stream observe predicate).SourceConstructorsAt (Nested.storageReads rows) debug children model →
    ordinary (action before).1 = true →
      predicate (action before).2 ∧ (action before).1 = (logical (observe before)).1.mapError Fault.language ∧
      observe (action before).2 = (logical (observe before)).2 := by
  intro action stream observe logical proper
  exact dispatcher_resource_projected history stream observe safety owner usizeBits base children model debug source values
    address native key normalized rows before data capacity facts aligned predicate initial input proper
    (Resource.Admitted.captured history action before trailing)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
