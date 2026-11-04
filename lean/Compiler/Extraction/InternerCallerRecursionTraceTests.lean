/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerTraceSegments
import Compiler.Extraction.InternerInsertionAppendEffectsTests
import Compiler.Extraction.InternerNativeRecursionEffectsTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.CallerTraceTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Normalization.HostTrace

/-- Reuse the existing fixture seeds. Their unsupported insertion and arbitrary
publication are replaced, and budget/allocator/debug values remain general. -/
theorem existing_entries_erase (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (safety : Bool) (container budget allocator owner usizeBits depth : Nat) :
    (Recursive.erasing (Publication.Effects.mapAllocator Recorded.effects)).Constructors
      (unfold (callerContext (Insertion.Recording.operations ops) (recordBacking allocate) safety container Insertion.Tests.model
        (RecursionEffectTests.base (record ops.arguments) (Publication.Recording.recordProbe ops.probe) budget allocator)
        (growth.map recordGrowth)) owner usizeBits depth)
      (unfold (callerContext ops allocate safety container Insertion.Tests.model
        (RecursionEffectTests.base ops.arguments ops.probe budget allocator) growth) owner usizeBits depth) :=
  unfold_recorded_erases ops allocate safety container Insertion.Tests.model growth rfl rfl rfl owner usizeBits depth

def ops (fail : Bool) : Insertion.Operations Nat :=
  { Insertion.Tests.ops with arguments := Publication.Tests.host, probe := Publication.Tests.attempt fail }

def native (fail : Bool) := context
  (callerContext (Insertion.Recording.operations (ops fail)) (recordBacking (fun _ _ _ effects => (none, effects)))
    false 3 Insertion.Tests.model (EffectTests.base (record Publication.Tests.host)) none)
  3 64 exhausted AssemblyItem.Initializers.Tests.debug

def replacement (fail : Bool) :=
  ((native fail).primitives Publication.Tests.source ⟨0, 0⟩ (input Publication.Tests.request.item AssemblyItem.Initializers.Tests.debug)).publish
    Publication.Tests.forceKey ⟨8, [1, 3]⟩ 42 (Publication.Recording.Tests.capture Publication.Tests.publicationWorld)

/-- Actual publication in the recursive caller is the already tested complete
probe/release/commit execution, including its failure path. -/
theorem replacement_is_existing (fail : Bool) : replacement fail = Publication.Recording.Tests.replacement fail := by
  unfold replacement native
  rw [context_publishes]
  dsimp only [Publication.Recording.Tests.replacement, Insertion.Recording.operations, ops, EffectTests.base]

theorem replacement_events : (replacement false).2.memory.effects.allocator.events =
    [.publicationProbe Publication.Tests.forceKey true, .free ⟨5, [1, 3]⟩] := by
  rw [replacement_is_existing]
  exact Publication.Recording.Tests.replacement_events

theorem replacement_reached : (replacement false).1 = .ok () ∧
    (replacement false).2.memory.effects.keys Publication.Tests.forceKey = some ⟨8, 42⟩ ∧
    (replacement false).2.memory.memory.heap.lookup 5 = none ∧
    (replacement false).2.memory.effects.allocator.effects = 125 := by
  rw [replacement_is_existing]
  exact Publication.Recording.Tests.replacement_reached

theorem refused_probe : (replacement true).1 = .error (.language .outOfMemory) ∧
    (replacement true).2.memory.effects.allocator = (⟨23, [.publicationProbe Publication.Tests.forceKey false]⟩ : Recorded Nat) ∧
    (replacement true).2.memory.effects.keys Publication.Tests.forceKey = some ⟨5, 42⟩ := by
  rw [replacement_is_existing]
  exact Publication.Recording.Tests.refused_probe

theorem exhausted_keeps_history (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (base : PairInput.Context (Publication.Effects (Recorded σ))) (growth : Option (Growth.Registered.Callbacks σ))
    (safety : Bool) (container owner usizeBits : Nat) (value : Contract.Yul.Word) (debug : AssemblyItem.Fields.Values)
    (before : World (Publication.Effects (Recorded σ))) :
    (unfold (callerContext (Insertion.Recording.operations ops) (recordBacking allocate) safety container Insertion.Tests.model
      base (growth.map recordGrowth)) owner usizeBits 0).constant value debug before =
      (.error (.language .unsupported), before) := rfl

/-- The same general entry fixture now preserves arbitrary recorder history at
all finite depths, including both optional-growth shapes. -/
theorem existing_entries_prefix (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (safety : Bool) (container budget allocator owner usizeBits depth : Nat)
    (leading : List Event) :
    let family := unfold (callerContext (Insertion.Recording.operations ops) (recordBacking allocate) safety container Insertion.Tests.model
      (RecursionEffectTests.base (record ops.arguments) (Publication.Recording.recordProbe ops.probe) budget allocator)
      (growth.map recordGrowth)) owner usizeBits depth
    (Recursive.erasing (Publication.Effects.mapAllocator (prepend leading))).Constructors family family :=
  unfold_recorded_prefix ops allocate safety container Insertion.Tests.model _ growth owner usizeBits depth leading

/-- Reuse the initialized owner and equal-input dispatcher case. The child now
runs the bound native insertion with a refused backing allocator. -/
def childBound := callerContext (Insertion.Recording.operations (ops false))
  (recordBacking (fun _ _ _ effects => (none, effects))) false 3 Insertion.Tests.model
  (EffectTests.base (record Publication.Tests.host)) none

def childDispatch (depth : Nat) :=
  ((context childBound 3 64 (unfold childBound 3 64 depth) AssemblyItem.Initializers.Tests.debug).primitives
    Publication.Tests.source ⟨0, 0⟩ (input Publication.Tests.request.item AssemblyItem.Initializers.Tests.debug)).simplify
      ⟨1, 24, 0, [1, 1], 0⟩ ⟨0, [1, 1]⟩

theorem child_dispatch_prefix (depth : Nat) (leading : List Event) :
    Effect.Transport (World.mapEffects (Publication.Effects.mapAllocator (prepend leading)))
      (childDispatch depth) (childDispatch depth) :=
  dispatcher_recorded_prefix (ops false) _ false 3 Insertion.Tests.model _ none 3 64 depth
    AssemblyItem.Initializers.Tests.debug Publication.Tests.source ⟨0, 0⟩
    (input Publication.Tests.request.item AssemblyItem.Initializers.Tests.debug) _ _ leading

theorem child_dispatch_segment (depth : Nat) (before : World (Publication.Effects (Recorded Nat))) :
    let captured := childDispatch depth (Publication.Recording.clearHistory before)
    childDispatch depth before =
      (captured.1, captured.2.mapEffects (Publication.Effects.mapAllocator (prepend before.memory.effects.allocator.events))) ∧
      (childDispatch depth before).2.memory.effects.allocator.events =
        before.memory.effects.allocator.events ++ captured.2.memory.effects.allocator.events :=
  Publication.Recording.action_segment (childDispatch depth) (child_dispatch_prefix depth) before

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- A real proper child allocates its item, encounters backing OOM, and frees
that item. Exhaustion remains distinct and emits none of those host calls. -/
theorem child_failure_events :
    (childDispatch 1 EffectTests.recorded).1 = .error (.language .outOfMemory) ∧
    (childDispatch 1 EffectTests.recorded).2.memory.effects.allocator.events =
      [.itemAllocate 224 16 (some 352), .backingAllocate 7 160 8 none, .itemFree 6] ∧
    (childDispatch 1 EffectTests.recorded).2.memory.effects.allocator.effects = 553 ∧
    (childDispatch 1 EffectTests.recorded).2.memory.memory.heap.lookup 6 = none ∧
    childDispatch 0 EffectTests.recorded = (.error (.language .unsupported), EffectTests.recorded) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by rfl'⟩

theorem child_failure_keeps_history (leading : List Event) :
    let before := EffectTests.recorded.mapEffects (Publication.Effects.mapAllocator (prepend leading))
    (childDispatch 1 before).1 = .error (.language .outOfMemory) ∧
    (childDispatch 1 before).2.memory.effects.allocator.events =
      leading ++ [.itemAllocate 224 16 (some 352), .backingAllocate 7 160 8 none, .itemFree 6] ∧
    (childDispatch 1 before).2.memory.effects.allocator.effects = 553 := by
  have bound := child_dispatch_prefix 1 leading EffectTests.recorded
  dsimp only
  rw [bound]
  simp only [World.mapEffects, Session.mapEffects, Publication.Effects.mapAllocator, prepend]
  exact ⟨child_failure_events.1, congrArg (leading ++ ·) child_failure_events.2.1, child_failure_events.2.2.1⟩

/-- The same segment also identifies the unrecorded native dispatcher result
and reached world. History cannot select a different native child outcome. -/
theorem child_paired_segment (depth : Nat) (before : World (Publication.Effects (Recorded Nat))) :
    let base := callerContext (ops false) (fun _ _ _ effects => (none, effects)) false 3 Insertion.Tests.model
      (EffectTests.base Publication.Tests.host) none
    let original := ((context base 3 64 (unfold base 3 64 depth) AssemblyItem.Initializers.Tests.debug).primitives
      Publication.Tests.source ⟨0, 0⟩ (input Publication.Tests.request.item AssemblyItem.Initializers.Tests.debug)).simplify
        ⟨1, 24, 0, [1, 1], 0⟩ ⟨0, [1, 1]⟩
    let captured := childDispatch depth (Publication.Recording.clearHistory before)
    original (before.mapEffects (Publication.Effects.mapAllocator Recorded.effects)) =
      (captured.1, captured.2.mapEffects (Publication.Effects.mapAllocator Recorded.effects)) ∧
    childDispatch depth before =
      (captured.1, captured.2.mapEffects (Publication.Effects.mapAllocator (prepend before.memory.effects.allocator.events))) ∧
    (childDispatch depth before).2.memory.effects.allocator.events =
      before.memory.effects.allocator.events ++ captured.2.memory.effects.allocator.events :=
  dispatcher_recorded_segment (ops false) _ false 3 Insertion.Tests.model none
    (leftBase := EffectTests.base (record Publication.Tests.host)) (rightBase := EffectTests.base Publication.Tests.host)
    rfl rfl rfl 3 64 depth AssemblyItem.Initializers.Tests.debug Publication.Tests.source ⟨0, 0⟩
    (input Publication.Tests.request.item AssemblyItem.Initializers.Tests.debug) _ _ before

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.CallerTraceTests
