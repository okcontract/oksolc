/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursiveProtocolReturn
import Compiler.Extraction.InternerCallerProtocolTraceTests
import Compiler.Extraction.InternerCallerRecursionTraceTests
import Compiler.Extraction.InternerLocalArgumentsTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray Caller.ProtocolTrace
open Publication.OriginTests (Case source request)

def cacheContext : PairInput.Context (Publication.Effects Nat) :=
  ⟨Caller.CacheStream.Tests.host, 160, 11, fun _ _ _ => CacheTests.poison, Interner.Queries.queries⟩

def cached (case : Case)
    (ports : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → GraphObservations (Publication.Effects Nat))
    (leading : List ProtocolEvent) :=
  item cacheContext ports (source case) (request case) CacheTests.debug (CacheTests.before case) leading

/-- All cache ownership cases share the same item/scratch return proof used
by initialized misses. The caller's original result and full metadata survive. -/
theorem cache_returned (case : Case)
    (ports : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → GraphObservations (Publication.Effects Nat))
    (leading : List ProtocolEvent) :
    outcome (cached case ports leading) = outcome (Caller.ProtocolTrace.Tests.cached case
      (ports (source case) CacheTests.address (input (request case).item CacheTests.debug)) leading) := by
  have observed := CacheTests.prefix_observed case
  exact (item_returned cacheContext ports (source case) (request case) CacheTests.debug
    (CacheTests.before case) (CacheTests.constructed case) CacheTests.address _ _ leading observed.1
    observed.2.2.2.2.1 observed.2.2.1).2.1

/-- All six existing cache ownership cases now pass through item and scratch
preparation and retirement. Their computed protocol is the already checked
complete cache stream; graph observers remain arbitrary and unreachable. -/
theorem cache_events (case : Case)
    (ports : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → GraphObservations (Publication.Effects Nat))
    (leading : List ProtocolEvent) :
    (cached case ports leading).2.events = Caller.CacheStream.Tests.events case leading [] ∧
      (cached case ports leading).2.tokens.incomplete = false := by
  have returned := cache_returned case ports leading
  have events := congrArg (fun result => result.2.2.1) returned
  have complete := congrArg (fun result => result.2.2.2) returned
  have checked := Caller.ProtocolTrace.Tests.cache_events case
    (ports (source case) CacheTests.address (input (request case).item CacheTests.debug)) leading
  exact ⟨events.trans checked.1, complete.trans checked.2⟩

theorem cache_scope (case : Case)
    (ports : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → GraphObservations (Publication.Effects Nat))
    (leading trailing : List ProtocolEvent) (other : Meaning) (read : Read) (sequence : BitVec 32) :
    scopeView (cached case ports leading).2 = (Caller.CacheStream.Tests.logical case leading trailing).2 := by
  have returned := congrArg (fun result => result.2.1) (cache_returned case ports leading)
  exact returned.trans (Caller.ProtocolTrace.Tests.cache_scope case
    (ports (source case) CacheTests.address (input (request case).item CacheTests.debug)) leading trailing other read sequence)

theorem cache_composed (case : Case)
    (ports : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → GraphObservations (Publication.Effects Nat))
    (leading trailing : List ProtocolEvent) (other : Meaning) (read : Read) (sequence : BitVec 32) :
    (cached case ports leading).1 = .ok 17 ∧
      (cached case ports leading).2.native = (CacheTests.observed case).2 ∧
      Good (source case) (request case).arguments (cached case ports leading).2.native.world ∧
      Closed (cached case ports leading).2.native.scope ∧
      (Caller.CacheStream.Tests.logical case leading trailing).2.heap.allocationCursor = (cached case ports leading).2.events.length := by
  have erased := item_erases cacheContext ports (source case) (request case) CacheTests.debug (CacheTests.before case) leading
  change CacheTests.observed case = ((cached case ports leading).1, (cached case ports leading).2.native) at erased
  have native := CacheTests.completed case (fun _ _ => CacheTests.poison)
  have replayed :=  Caller.CacheStream.Tests.existing_family case leading trailing other read sequence
  have reached : (cached case ports leading).2.native = (CacheTests.observed case).2 := (congrArg Prod.snd erased).symm
  refine ⟨(congrArg Prod.fst erased).symm.trans native.1, reached, ?_, ?_, ?_⟩
  · rw [reached]; exact native.2.1
  · rw [reached]; exact native.2.2.1
  · rw [replayed.2.2.2.2.2.2, (cache_events case ports leading).1]
    simp only [Caller.CacheStream.Tests.events, List.append_nil]

/-- Semantic rejection retains the reached native locals and all metadata.
Ordinary OOM is deliberately excluded by the same source guard. -/
theorem rejected_retirement (mark : Nat) (ran : Except Fault NodeId × Recorded σ)
    (rejected : ordinary ran.1 = false) : retire mark ran = ran := by
  simp only [retire, TemporaryArguments.unwind, rejected, Bool.false_eq_true, ↓reduceIte]

theorem failed_literal (context : PairInput.Context σ) (ports)
    (opcode : Opcode) (values : List NodeId) (debug : AssemblyItem.Fields.Values)
    (before reached : World σ) (fault : Fault) (leading : List ProtocolEvent)
    (failed : Arguments.prepare values before = (.error fault, reached)) :
    literal context ports opcode values debug before leading = (.error fault, start reached leading) := by
  simp only [literal, failed]

theorem failed_local (context : PairInput.Context σ) (ports) (opcode : Opcode) (source : View)
    (left right repeated : NodeId) (selected : Nat) (first : Bool) (debug : AssemblyItem.Fields.Values)
    (before reached : World σ) (fault : Fault) (leading : List ProtocolEvent)
    (failed : LocalArguments.zigLocal source selected repeated first before = (.error fault, reached)) :
    namedLocal context ports opcode source left right repeated selected first debug before leading = (.error fault, start reached leading) := by
  simp only [namedLocal, failed]

/-- The existing offset-source copy discharges preparation for every unused
slot, including out-of-range values; no write occurs on this branch. -/
theorem local_unused_slot (selected : Nat) :
    Arguments.Prepared [1, 2] Semantic.Tests.caller LocalArguments.Tests.target
      (LocalArguments.zigLocal LocalArguments.Tests.source selected 99 false Semantic.Tests.caller).2 :=
  ViewInput.local_input_optional _ _ 1 2 99 selected false _ _
    ⟨Normalization.Tests.original_valid, LocalArguments.Tests.source_represented⟩
    (by intro impossible; contradiction) (by rfl)

/-- Enabling the same out-of-range slot retains the initialized copy and the
original history, as in the existing native rejection fixture. No item runs. -/
theorem rejected_local_slot (context : PairInput.Context Nat) (ports)
    (debug : AssemblyItem.Fields.Values) (leading : List ProtocolEvent) :
    namedLocal context ports 20 LocalArguments.Tests.source 1 2 99 2 true debug Semantic.Tests.caller leading =
      (.error (.memory (.preparation (.memory .memoryValidity))), start LocalArguments.Tests.copied leading) :=
  failed_local context ports 20 LocalArguments.Tests.source 1 2 99 2 true debug _ _ _ leading
    (Prod.ext LocalArguments.Tests.invalid_overwrite_keeps_initialized_copy.1
      LocalArguments.Tests.invalid_overwrite_keeps_initialized_copy.2)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace.Tests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ProtocolTrace.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray Caller.ProtocolTrace

/-- Reuse the initialized owner and refused backing allocator from the existing
recursive caller corpus. The parent literal now makes the complete child call. -/
def family (depth : Nat) := unfold (CallerTraceTests.ops false) (fun _ _ _ effects => (none, effects)) false 3
  Insertion.Tests.model (EffectTests.base Publication.Tests.host) none 64 depth
def parent (depth : Nat) (leading : List ProtocolEvent) :=
  (family depth).operation 24 [1, 1] AssemblyItem.Initializers.Tests.debug EffectTests.initial leading

/-- A test-only order check. Native insertion's existing recorder proves the
owner payloads; this regression checks which operations the wrapper executes. -/
def appendFailure : List ProtocolEvent → Bool
  | [.normalization (.allocate .duplicate true),
      .insertion (.attempt .arguments _ (.ok true)), .insertion (.attempt .item _ (.ok true)),
      .insertion (.attempt .clone _ (.ok true)), .insertion (.attempt .append _ (.ok false)),
      .insertion (.release .value _ (.ok ())), .insertion (.release .allocation _ (.ok ())),
      .insertion (.release .arguments _ (.ok ())), .insertion (.release .normalized _ (.ok ()))] => true
  | _ => false

def nestedFailure : List ProtocolEvent → Bool
  | .normalization (.prepare lookup (.ok ())) :: .normalization (.allocate .duplicate true) :: rest =>
    lookup == { origin := .scratch } &&
      match rest.getLast?, rest.dropLast with
      | some (.normalization (.release lookup)), child =>
        lookup == { origin := .scratch, owner := .caller } && appendFailure child
      | _, _ => false
  | _ => false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem recursive_oom :
    (parent 2 []).1 = .error (.language .outOfMemory) ∧
      nestedFailure (parent 2 []).2.events = true ∧
      (parent 2 []).2.tokens.incomplete = false ∧
      (parent 2 []).2.native.scope = ⟨none, none, false⟩ := by
  exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem recursive_prefix (depth : Nat) (leading : List ProtocolEvent) :
    parent depth leading = ((parent depth []).1, prepend leading (parent depth []).2) := by
  have bound := unfold_prefix (CallerTraceTests.ops false) (fun _ _ _ effects => (none, effects)) false 3
    Insertion.Tests.model (EffectTests.base Publication.Tests.host) none 64 depth leading []
  have entry := congrArg (fun c => c.operation 24 [1, 1] AssemblyItem.Initializers.Tests.debug EffectTests.initial) bound
  simpa only [ConstructorItem.ProtocolTrace.mapConstructors, ConstructorItem.ProtocolTrace.prefixCapture, List.append_nil] using entry

theorem exhausted (leading : List ProtocolEvent) :
    parent 0 leading = (.error (.language .unsupported), ConstructorItem.ProtocolTrace.start EffectTests.initial leading) := rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ProtocolTrace.Tests
