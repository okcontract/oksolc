/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerMissChildTrace
import Compiler.Extraction.InternerCallerCacheStreamTests
import Compiler.Extraction.InternerNativeDispatchEffectsTests
import Compiler.Extraction.InternerNativeScopedDispatchTests
import Compiler.Extraction.InternerCallerProtocolTraceTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ChildTrace.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray Interner.InvocationTrace
open RepresentativeArray
open Publication.OriginTests (Case source request)
open MissStream (ProtocolEvent)

abbrev cacheStart := Caller.CacheStream.Tests.start
abbrev cacheEvents (case : Case) := Caller.CacheStream.Tests.events case [] []
def cachePorts : Caller.ProtocolTrace.GraphObservations (Publication.Effects Nat) :=
  ⟨fun _ _ _ => [], fun _ _ _ _ => [], fun _ _ _ _ => []⟩
def cacheObservation (case : Case) (before : World (Publication.Effects Nat)) :=
  (Caller.ProtocolTrace.find Caller.CacheStream.Tests.host 160 11 CacheTests.poison Interner.Queries.queries
    cachePorts (source case) ⟨(CacheTests.constructed case).memory.memory.nextId, 0, 2⟩ (request case)
    ⟨⟨before, { lookup := none }⟩, {}, []⟩).2.events
def cacheAction (case : Case) : GraphAction (Publication.Effects Nat) NodeId := fun before =>
  let called := Caller.find Caller.CacheStream.Tests.host 160 11 CacheTests.poison Interner.Queries.queries
    (source case) ⟨(CacheTests.constructed case).memory.memory.nextId, 0, 2⟩ (request case) before
  (called.1, called.2.world)

/-- These observations are the actual six cache executions already checked by
the general cache theorem. The record wrapper retains their native world and
places their complete initialization/cleanup events after arbitrary history. -/
theorem recorded_cache_family (case : Case) (leading trailing : List ProtocolEvent)
    (other : Meaning) (read : Read) (sequence : BitVec 32) :
    let ran := record (cacheAction case) (cacheObservation case) (restore leading (cacheStart case))
    ran.1 = .ok 17 ∧ erase ran.2 = (Caller.CacheStream.Tests.actual case).2.world ∧
      Good (source case) (request case).arguments (erase ran.2) ∧
      history ran.2 = leading ++ cacheEvents case ∧
      (Caller.CacheStream.Tests.logical case leading trailing).1 = .ok 17 ∧
      (Caller.CacheStream.Tests.logical case leading trailing).2.heap.allocationCursor = (history ran.2).length := by
  intro ran
  have native := Caller.CacheStream.Tests.existing_family case leading trailing other read sequence
  have erased : erase ran.2 = (Caller.CacheStream.Tests.actual case).2.world := by
    simp only [ran, record, erase_restore]
    rfl
  have observed : cacheObservation case (cacheStart case) = cacheEvents case :=
    (Caller.ProtocolTrace.Tests.cache_events case cachePorts []).1
  have events : history ran.2 = leading ++ cacheEvents case := by
    change leading ++ cacheObservation case (cacheStart case) = _
    rw [observed]
  refine ⟨?_, erased, by rw [erased]; exact native.2.1, events, native.2.2.2.2.2.1, ?_⟩
  · exact native.1
  · rw [native.2.2.2.2.2.2, events]
    simp only [cacheEvents, Caller.CacheStream.Tests.events, List.nil_append, List.append_nil, List.append_assoc]

/-- Control-only child effects make order and early failure observable. Their
markers are not certificates of insertion/publication semantics. Real protocol
observations are exercised separately by `recorded_cache_family`. -/
def child (failure : Option (Nat × Fault)) : GraphAction (Publication.Effects Nat) NodeId := fun before =>
  let count := before.memory.effects.allocator
  let result := match failure with
    | some (position, fault) => if count = position then .error fault else .ok (count + 1)
    | none => .ok (count + 1)
  (result, { before with memory := { before.memory with effects := { before.memory.effects with allocator := count + 1 } } })

def marker (count : Nat) : ProtocolEvent := .publicationProbe ⟨1, 24, 0, [count], 0⟩ true
def children (failure : Option (Nat × Fault)) := ScopeTests.resultChildren (child failure)
def observations : Observations Nat ProtocolEvent := ScopeTests.resultChildren (fun before => [marker before.memory.effects.allocator])
def traced (failure : Option (Nat × Fault)) := constructors (children failure) observations
def initial : World (Publication.Effects Nat) :=
  EffectTests.initial.mapEffects (Publication.Effects.mapAllocator (fun _ => 0))

def dispatch (base : PairInput.Context (Publication.Effects (Recorded Nat ProtocolEvent))) (failure : Option (Nat × Fault)) :=
  ((context base 3 64 (traced failure) CacheTests.debug).primitives Publication.Tests.source ⟨0, 0⟩
    (input Publication.Tests.request.item CacheTests.debug)).simplify ⟨1, 24, 0, [1, 1], 0⟩ ⟨0, [1, 1]⟩

theorem native_dispatch_child (base : PairInput.Context (Publication.Effects (Recorded Nat ProtocolEvent))) :
    (dispatch base none (restore [] initial)).1 = .ok (some 1) ∧
    history (dispatch base none (restore [] initial)).2 = [marker 0] ∧
    (erase (dispatch base none (restore [] initial)).2).memory.effects.allocator = 1 := by
  exact ⟨by rfl', by rfl', by rfl'⟩

/-- The source guard contributes either the real child marker or an empty
segment. Prior history and the caller's initialization/take offset are general. -/
theorem guarded_boundaries (ops : Insertion.Operations (Recorded Nat ProtocolEvent))
    (allocate : Backing.Registry.Allocate (Recorded Nat ProtocolEvent)) (safety : Bool) (meaning : Meaning)
    (base : PairInput.Context (Publication.Effects (Recorded Nat ProtocolEvent)))
    (growth : Option (Growth.Registered.Callbacks (Recorded Nat ProtocolEvent)))
    (leading : List ProtocolEvent) (start : Nat) :
    let before := restore leading initial
    let request := Interner.constructorCode.operationRequest 24 [1, 1]
    let key : Key := ⟨1, 24, 0, [1, 1], 0⟩
    let slice : ArgumentSlice := ⟨0, [1, 1]⟩
    let p := MissStream.physical ops allocate safety 3 meaning base growth 3 64 (traced none) CacheTests.debug
      Publication.Tests.source ⟨0, 0⟩ (input Publication.Tests.request.item CacheTests.debug)
    let reached := MissStream.selected p request key slice true before
    history reached.2 = leading ++ [marker 0] ∧
      MissStream.childCursor start before reached.2 = start + 1 ∧
      MissStream.selected p request key slice false before = (.ok none, before) := by
  intro before request key slice p reached
  have boundaries := MissStream.child_boundaries ops allocate safety 3 meaning base growth 64 (children none) observations
    CacheTests.debug Publication.Tests.source ⟨0, 0⟩ (input Publication.Tests.request.item CacheTests.debug)
    request key slice true before start
  have observed : history (MissStream.selected p request key slice true (restore [] (erase before))).2 = [marker 0] :=
    (native_dispatch_child base).2.1
  exact ⟨boundaries.1.trans (congrArg (leading ++ ·) observed),
    boundaries.2.2.trans (congrArg (fun events => start + events.length) observed), rfl⟩

def sequence (failure : Option (Nat × Fault)) := Dispatch.maxExponent (traced failure)
  (fun one debug => (traced failure).operation 22 [one] debug) CacheTests.debug

theorem sequence_prefix (failure : Option (Nat × Fault)) (leading : List ProtocolEvent) :
    Effect.Transport (World.mapEffects (Publication.Effects.mapAllocator (prepend leading))) (sequence failure) (sequence failure) := by
  let r := Recursive.erasing (Publication.Effects.mapAllocator (prepend (σ := Nat) leading))
  have c := constructors_prefix (children failure) observations leading
  unfold sequence Dispatch.maxExponent
  exact r.bind (c.constant _ _) (fun _ => r.bind (c.operation _ _ _) (fun _ =>
    r.bind (c.operation _ _ _) (fun _ => r.bind (c.operation _ _ _) (fun _ => r.pure _))))

theorem successful_order :
    (sequence none (restore [] initial)).1 = .ok (some 4) ∧
    history (sequence none (restore [] initial)).2 = [marker 0, marker 1, marker 2, marker 3] ∧
    (erase (sequence none (restore [] initial)).2).memory.effects.allocator = 4 := by
  exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

/-- Ordinary OOM and semantic faults both stop the source sequence after the
second child. History and the reached allocator effect are retained exactly. -/
theorem failed_order (fault : Fault) (leading : List ProtocolEvent) :
    (sequence (some (1, fault)) (restore leading initial)).1 = .error fault ∧
    history (sequence (some (1, fault)) (restore leading initial)).2 = leading ++ [marker 0, marker 1] ∧
    (erase (sequence (some (1, fault)) (restore leading initial)).2).memory.effects.allocator = 2 := by
  have observed : (sequence (some (1, fault)) (restore [] initial)).1 = .error fault ∧
      history (sequence (some (1, fault)) (restore [] initial)).2 = [marker 0, marker 1] ∧
      (erase (sequence (some (1, fault)) (restore [] initial)).2).memory.effects.allocator = 2 := by
    exact ⟨by rfl', by rfl', by rfl'⟩
  have transported := sequence_prefix (some (1, fault)) leading (restore [] initial)
  have before : (restore [] initial).mapEffects (Publication.Effects.mapAllocator (prepend leading)) = restore leading initial := by
    simp only [restore, World.mapEffects, Session.mapEffects, Publication.Effects.mapAllocator, prepend, List.append_nil]
  rw [before] at transported
  rw [transported]
  exact ⟨observed.1, congrArg (leading ++ ·) observed.2.1, observed.2.2⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ChildTrace.Tests
