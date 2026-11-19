/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeDispatchEffects
import Compiler.Extraction.InternerGraphInitOwnershipTests
import Compiler.Extraction.InternerPublicationHostTraceTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.EffectTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open Publication Normalization.HostTrace
open Publication.Tests (seedFor host attempt source buffer request)
open Recording.Tests (capture capture_erases)

def initial := GraphInit.Ownership.Tests.owned false
def recorded := capture initial

/-- Reuse the existing initialized native owner and parent allocation. Deliberately
wrong annotations cannot supply the returned value or conceal a failed load. -/
theorem native_operand_ignores_annotation :
    operand ⟨0, [99, 99, 99]⟩ 1 99 recorded = (.ok 1, recorded) := by rfl'

theorem native_operand_bounds :
    operand ⟨0, [99]⟩ 1 99 recorded = (.error (.memory (.preparation (.memory .sourceBounds))), recorded) := by rfl'

def retired := { recorded with memory := { recorded.memory with memory := Compiler.ZigAir.Memory.erase recorded.memory.memory 0 } }

theorem native_operand_after_retirement :
    operand ⟨0, [99, 99, 99]⟩ 1 99 retired = (.error (.memory (.preparation (.memory .unallocated))), retired) := by rfl'

theorem reached_operand_erases (source : ArgumentSlice) (index : Nat) (annotation : NodeId) :
    operand source index annotation (retired.mapEffects (Effects.mapAllocator Recorded.effects)) =
      ((operand source index annotation retired).1,
       (operand source index annotation retired).2.mapEffects (Effects.mapAllocator Recorded.effects)) :=
  operand_erases (Effects.mapAllocator Recorded.effects) source index annotation retired

theorem empty_native_query : NativeReads.query 3 (fun reads => reads.operation 0 1) recorded =
    (.ok none, recorded) := by rfl'

theorem invalid_native_query : NativeReads.query 99 (fun reads => reads.constant 0) recorded =
    (.error (.language .safetyFault), recorded) := by rfl'

theorem all_native_queries_erase (owner : Nat) (action : Nested.Reads → Except ReadError α) :
    NativeReads.query owner action initial =
      ((NativeReads.query owner action recorded).1,
       (NativeReads.query owner action recorded).2.mapEffects (Effects.mapAllocator Recorded.effects)) := by
  have erased := query_erases (Effects.mapAllocator Recorded.effects) owner action recorded
  rw [show recorded.mapEffects (Effects.mapAllocator Recorded.effects) = initial from capture_erases initial] at erased
  exact erased

def base (externalHost : External σ) : PairInput.Context (Effects σ) :=
  ⟨external externalHost, 160, 7, fun _ _ _ => seedFor σ, Caller.Tests.queries⟩

def primitives (externalHost : External σ) (owner : Nat) (debug : AssemblyItem.Fields.Values) :=
  (context (base externalHost) owner 64 exhausted debug).primitives source ⟨0, 0⟩ (input request.item debug)

theorem native_dispatch_erases (owner : Nat) (debug : AssemblyItem.Fields.Values) (key : Key) (slice : ArgumentSlice) :
    Effect.Transport (World.mapEffects (Effects.mapAllocator Recorded.effects))
      ((primitives (record host) owner debug).simplify key slice)
      ((primitives host owner debug).simplify key slice) :=
  dispatcher_erases (Effects.mapAllocator Recorded.effects) (base (record host)) (base host) owner 64
    (exhausted_erases _) debug source ⟨0, 0⟩ (input request.item debug) key slice

theorem native_dispatch_reaches_child (debug : AssemblyItem.Fields.Values) :
    (primitives (record host) 3 debug).simplify ⟨1, 24, 0, [1, 1], 0⟩ ⟨0, [1, 1]⟩ recorded =
      (.error (.language .unsupported), recorded) := by rfl'

theorem native_dispatch_query_failure (debug : AssemblyItem.Fields.Values) :
    (primitives (record host) 99 debug).simplify ⟨1, 24, 0, [1, 1], 0⟩ ⟨0, [1, 1]⟩ recorded =
      (.error (.language .safetyFault), recorded) := by rfl'

def found (externalHost : External σ) (hostProbe : OwnedKeys.Physical.Probe σ)
    (owner : Nat) (debug : AssemblyItem.Fields.Values) (before : World (Effects σ)) :=
  Caller.find (external externalHost) 160 7
    (callbacks hostProbe externalHost 7 source (primitives externalHost owner debug))
    Caller.Tests.queries source buffer request before

theorem native_caller_erases (owner : Nat) (debug : AssemblyItem.Fields.Values) (before : World (Effects Nat)) :
    found host (attempt false) owner debug before =
      ((found (record host) (Recording.recordProbe (attempt false)) owner debug (capture before)).1,
       (found (record host) (Recording.recordProbe (attempt false)) owner debug (capture before)).2.mapEffects
         (Effects.mapAllocator Recorded.effects)) := by
  have erased := recorded_find_erases (attempt false) host 160 7 source buffer (base (record host)) (base host)
    owner 64 (exhausted_erases _) debug ⟨0, 0⟩ (input request.item debug) (fun _ _ _ _ => rfl)
    Caller.Tests.queries request (capture before)
  rw [capture_erases] at erased
  exact erased

def rejected (debug : AssemblyItem.Fields.Values) :=
  found (record host) (Recording.recordProbe (attempt false)) 99 debug (capture Publication.Tests.world)

/-- The existing normalization/caller execution retains reached ownership on a
native query fault. Neither a publication probe nor ordinary cleanup is invented. -/
theorem caller_query_fault_retains_scope (debug : AssemblyItem.Fields.Values) :
    (rejected debug).1 = .error (.language .safetyFault) ∧
    (rejected debug).2.world.memory.effects.allocator.effects = 13 ∧
    (rejected debug).2.scope.slice = some ⟨5, [1, 3]⟩ ∧
    (rejected debug).2.world.memory.effects.allocator.events = [.allocate .duplicate 8 (some 76)] :=
  ⟨by rfl', by rfl', by rfl', by rfl'⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.EffectTests
