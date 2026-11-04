/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerRecursionTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication.Recording
open Compiler.Algebraic Normalization.HostTrace

/-- Observe a segment from the same native input with an empty recorder history.
The heap, key table, allocator effects and graph are unchanged. -/
def clearHistory (before : World (Effects (Recorded σ))) : World (Effects (Recorded σ)) :=
  before.mapEffects (Effects.mapAllocator (fun state => { state with events := [] }))

theorem restore_history (before : World (Effects (Recorded σ))) :
    (clearHistory before).mapEffects (Effects.mapAllocator (prepend before.memory.effects.allocator.events)) = before := by
  simp only [clearHistory, World.mapEffects, Session.mapEffects, Effects.mapAllocator, prepend, List.append_nil]

/-- History independence determines an exact appended segment, including the
reached state on failure. No existential log or cursor is supplied by a caller. -/
theorem action_segment (action : GraphAction (Effects (Recorded σ)) α)
    (independent : ∀ leading, Effect.Transport (World.mapEffects (Effects.mapAllocator (prepend leading))) action action)
    (before : World (Effects (Recorded σ))) :
    let captured := action (clearHistory before)
    action before = (captured.1, captured.2.mapEffects (Effects.mapAllocator (prepend before.memory.effects.allocator.events))) ∧
      (action before).2.memory.effects.allocator.events =
        before.memory.effects.allocator.events ++ captured.2.memory.effects.allocator.events := by
  intro captured
  have observed := independent before.memory.effects.allocator.events (clearHistory before)
  rw [restore_history] at observed
  exact ⟨observed, congrArg (fun pair => pair.2.memory.effects.allocator.events) observed⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication.Recording

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Normalization.HostTrace

/-- Every finite native entry retains arbitrary prior recorder history. The
existing entry induction consumes the actual host prefix laws, including
growth release; no child-prefix or native-result premise remains. -/
theorem unfold_recorded_prefix (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (runtimeSafety : Bool) (container : Nat) (meaning : Meaning)
    (base : PairInput.Context (Publication.Effects (Recorded σ))) (growth : Option (Growth.Registered.Callbacks σ))
    (owner usizeBits depth : Nat) (leading : List Event) :
    let family := unfold (callerContext (Insertion.Recording.operations ops) (recordBacking allocate)
      runtimeSafety container meaning base (growth.map recordGrowth)) owner usizeBits depth
    (Recursive.erasing (Publication.Effects.mapAllocator (prepend leading))).Constructors family family :=
  unfold_caller_erases (prefix_transport ops.arguments leading) (Publication.Recording.probe_prefix ops.probe leading)
    (release_request_prefix _ ops.bytes leading) (release_request_prefix _ ops.objects leading)
    (request_prefix _ ops.create leading) (request_prefix _ ops.copy leading) (backing_prefix allocate leading)
    runtimeSafety container meaning (optional_growth_prefix growth leading) rfl rfl rfl owner usizeBits depth

/-- The native dispatcher inherits history independence from the actual finite
constructor family. Reads and source guards remain the existing dispatcher. -/
theorem dispatcher_recorded_prefix (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (runtimeSafety : Bool) (container : Nat) (meaning : Meaning)
    (base : PairInput.Context (Publication.Effects (Recorded σ))) (growth : Option (Growth.Registered.Callbacks σ))
    (owner usizeBits depth : Nat) (debug : AssemblyItem.Fields.Values) (source : View)
    (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (owned : ArgumentSlice) (leading : List Event) :
    let bound := callerContext (Insertion.Recording.operations ops) (recordBacking allocate)
      runtimeSafety container meaning base (growth.map recordGrowth)
    let p := (context bound owner usizeBits (unfold bound owner usizeBits depth) debug).primitives source address native
    Effect.Transport (World.mapEffects (Publication.Effects.mapAllocator (prepend leading))) (p.simplify key owned) (p.simplify key owned) :=
  dispatcher_erases (Publication.Effects.mapAllocator (prepend leading)) _ _ owner usizeBits
    (unfold_recorded_prefix ops allocate runtimeSafety container meaning base growth owner usizeBits depth leading)
    debug source address native key owned

/-- Bind the actual dispatcher segment and native execution together. The
recorded suffix is computed from the same native input without history, then
appended in source order. These are physical host events, not tagged protocol
slots; converting between those observations remains a separate obligation. -/
theorem dispatcher_recorded_segment (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (runtimeSafety : Bool) (container : Nat) (meaning : Meaning) (growth : Option (Growth.Registered.Callbacks σ))
    {leftBase : PairInput.Context (Publication.Effects (Recorded σ))} {rightBase : PairInput.Context (Publication.Effects σ)}
    (budgets : leftBase.budget = rightBase.budget) (allocators : leftBase.allocator = rightBase.allocator)
    (queries : leftBase.queries = rightBase.queries) (owner usizeBits depth : Nat)
    (debug : AssemblyItem.Fields.Values) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (native : AssemblyClone.NativeFields.ItemValue) (key : Key) (owned : ArgumentSlice)
    (before : World (Publication.Effects (Recorded σ))) :
    let leftBound := callerContext (Insertion.Recording.operations ops) (recordBacking allocate)
      runtimeSafety container meaning leftBase (growth.map recordGrowth)
    let rightBound := callerContext ops allocate runtimeSafety container meaning rightBase growth
    let left := ((context leftBound owner usizeBits (unfold leftBound owner usizeBits depth) debug).primitives source address native).simplify key owned
    let right := ((context rightBound owner usizeBits (unfold rightBound owner usizeBits depth) debug).primitives source address native).simplify key owned
    let captured := left (Publication.Recording.clearHistory before)
    right (before.mapEffects (Publication.Effects.mapAllocator Recorded.effects)) =
      (captured.1, captured.2.mapEffects (Publication.Effects.mapAllocator Recorded.effects)) ∧
      left before = (captured.1, captured.2.mapEffects (Publication.Effects.mapAllocator (prepend before.memory.effects.allocator.events))) ∧
      (left before).2.memory.effects.allocator.events = before.memory.effects.allocator.events ++ captured.2.memory.effects.allocator.events := by
  intro leftBound rightBound left right captured
  have segment := Publication.Recording.action_segment left
    (dispatcher_recorded_prefix ops allocate runtimeSafety container meaning leftBase growth owner usizeBits depth debug source address native key owned) before
  have erased := dispatcher_erases (Publication.Effects.mapAllocator Recorded.effects) leftBound rightBound owner usizeBits
    (unfold_recorded_erases ops allocate runtimeSafety container meaning growth budgets allocators queries owner usizeBits depth)
    debug source address native key owned (Publication.Recording.clearHistory before)
  exact ⟨erased, segment⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
