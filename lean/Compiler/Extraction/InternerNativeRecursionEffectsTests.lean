/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeRecursionEffects
import Compiler.Extraction.InternerNativeDispatchEffectsTests
import Compiler.Extraction.InternerLocalArgumentsTests
import Compiler.Extraction.InternerTemporaryArgumentsTests
import Compiler.Extraction.AssemblyItemInitializationTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.RecursionEffectTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open Publication Normalization.HostTrace

/-- Reuse the existing unsupported-insertion fixture. Both seed simplification
and seed publication are replaced by the actual recursion/publication adapters. -/
def base (host : External σ) (probe : OwnedKeys.Physical.Probe σ) (budget allocator : Nat) : PairInput.Context (Effects σ) :=
  ⟨external host, budget, allocator,
   fun source _ _ => callbacks probe host allocator source (Publication.Tests.seedFor σ), Caller.Tests.queries⟩

theorem base_erases (host : External σ) (probe : OwnedKeys.Physical.Probe σ) (budget allocator : Nat) :
    BaseTransport (base (record host) (Recording.recordProbe probe) budget allocator)
      (base host probe budget allocator) (Effects.mapAllocator Recorded.effects) :=
  ⟨external_transport (transport host), rfl, rfl, rfl,
   fun source _ _ key owned id => Recording.publish_erases probe host allocator source key owned id,
   fun _ _ _ _ _ _ _ => rfl⟩

/-- The shared induction handles arbitrary budgets, allocator identities,
owners, debug values and reached states. There is no recursive premise left. -/
theorem all_depths_erase (host : External σ) (probe : OwnedKeys.Physical.Probe σ)
    (budget allocator owner usizeBits depth : Nat) :
    (Recursive.erasing (Effects.mapAllocator Recorded.effects)).Constructors
      (unfold (base (record host) (Recording.recordProbe probe) budget allocator) owner usizeBits depth)
      (unfold (base host probe budget allocator) owner usizeBits depth) :=
  unfold_erases (base_erases host probe budget allocator) owner usizeBits depth

def children (depth : Nat) := unfold
  (base (record Publication.Tests.host) (Recording.recordProbe (Publication.Tests.attempt false)) 160 7) 3 64 depth

theorem literal_entry_erases (depth : Nat) (opcode : Opcode) (values : List NodeId) (debug : AssemblyItem.Fields.Values) :
    Effect.Transport (World.mapEffects (Effects.mapAllocator Recorded.effects))
      ((children depth).operation opcode values debug)
      ((unfold (base Publication.Tests.host (Publication.Tests.attempt false) 160 7) 3 64 depth).operation opcode values debug) :=
  (all_depths_erase _ _ 160 7 3 64 depth).operation opcode values debug

theorem borrowed_entry_erases (depth address : Nat) (opcode : Opcode) (values : List NodeId)
    (debug : AssemblyItem.Fields.Values) :
    Effect.Transport (World.mapEffects (Effects.mapAllocator Recorded.effects))
      ((children depth).borrowedOperation address opcode values debug)
      ((unfold (base Publication.Tests.host (Publication.Tests.attempt false) 160 7) 3 64 depth).borrowedOperation address opcode values debug) :=
  (all_depths_erase _ _ 160 7 3 64 depth).borrowedOperation address opcode values debug

theorem local_entry_erases (depth : Nat) (opcode : Opcode) (source : ArgumentSlice)
    (selected repeated : Nat) (first : Bool) (debug : AssemblyItem.Fields.Values) :
    Effect.Transport (World.mapEffects (Effects.mapAllocator Recorded.effects))
      ((children depth).localOperation opcode source selected repeated first debug)
      ((unfold (base Publication.Tests.host (Publication.Tests.attempt false) 160 7) 3 64 depth).localOperation opcode source selected repeated first debug) :=
  (all_depths_erase _ _ 160 7 3 64 depth).localOperation opcode source selected repeated first debug

theorem constant_entry_erases (depth : Nat) (value : Contract.Yul.Word) (debug : AssemblyItem.Fields.Values) :
    Effect.Transport (World.mapEffects (Effects.mapAllocator Recorded.effects))
      ((children depth).constant value debug)
      ((unfold (base Publication.Tests.host (Publication.Tests.attempt false) 160 7) 3 64 depth).constant value debug) :=
  (all_depths_erase _ _ 160 7 3 64 depth).constant value debug

theorem materialize_entry_erases (depth : Nat) (id : NodeId) (value : Contract.Yul.Word) (debug : AssemblyItem.Fields.Values) :
    Effect.Transport (World.mapEffects (Effects.mapAllocator Recorded.effects))
      ((children depth).materialize id value debug)
      ((unfold (base Publication.Tests.host (Publication.Tests.attempt false) 160 7) 3 64 depth).materialize id value debug) :=
  (all_depths_erase _ _ 160 7 3 64 depth).materialize id value debug

theorem local_shape_guard (depth : Nat) (debug : AssemblyItem.Fields.Values) :
    (children (depth + 1)).localOperation 24 ⟨0, [1, 2, 3]⟩ 0 99 true debug EffectTests.recorded =
      (.error .outsideOwnedContinuation, EffectTests.recorded) := rfl

/-- Erasure retains the old aggregate fault and its rollback, rather than
replacing it with an allocation refusal or exposing the first scalar store. -/
theorem aggregate_fault_erases (leading : List Event) :
    let before := LocalArguments.Tests.short.mapEffects (fun n => (⟨n, leading⟩ : Recorded Nat))
    (LocalArguments.initPair LocalArguments.Tests.target 99 1 before).1 = .error (.memory (.preparation (.memory .memoryValidity))) ∧
    (LocalArguments.initPair LocalArguments.Tests.target 99 1 before).2.mapEffects Recorded.effects = LocalArguments.Tests.short := by
  dsimp only
  have erased := LocalArguments.EffectTransport.initPair Recorded.effects LocalArguments.Tests.target 99 1
    (LocalArguments.Tests.short.mapEffects (fun n => (⟨n, leading⟩ : Recorded Nat)))
  change LocalArguments.initPair LocalArguments.Tests.target 99 1 LocalArguments.Tests.short = _ at erased
  exact ⟨(congrArg Prod.fst erased).symm.trans LocalArguments.Tests.aggregate_rejection_has_no_prefix.1,
    (congrArg Prod.snd erased).symm.trans LocalArguments.Tests.aggregate_rejection_has_no_prefix.2.1⟩

theorem exhausted_keeps_world (debug : AssemblyItem.Fields.Values) :
    (children 0).constant 0 debug EffectTests.recorded = (.error (.language .unsupported), EffectTests.recorded) := rfl

def recursiveCall (depth : Nat) := (children depth).operation 24 [1, 1]
  AssemblyItem.Initializers.Tests.debug EffectTests.recorded

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Reuse the existing equal-input native dispatcher case. At depth two its
constant child actually enters both native frames before unsupported insertion;
at depth one exhaustion occurs before either child frame is allocated. -/
theorem proper_child_enters_frames :
    (recursiveCall 1).1 = .error (.language .unsupported) ∧
    (recursiveCall 2).1 = .error (.language .unsupported) ∧
    (recursiveCall 2).2.memory.memory.nextId = (recursiveCall 1).2.memory.memory.nextId + 2 :=
  ⟨by rfl', by rfl', by rfl'⟩

theorem reached_child_erases :
    (unfold (base Publication.Tests.host (Publication.Tests.attempt false) 160 7) 3 64 2).operation
        24 [1, 1] AssemblyItem.Initializers.Tests.debug EffectTests.initial =
      ((recursiveCall 2).1, (recursiveCall 2).2.mapEffects (Effects.mapAllocator Recorded.effects)) := by
  have erased := literal_entry_erases 2 24 [1, 1] AssemblyItem.Initializers.Tests.debug EffectTests.recorded
  rw [show EffectTests.recorded.mapEffects (Effects.mapAllocator Recorded.effects) = EffectTests.initial from rfl] at erased
  exact erased

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.RecursionEffectTests
