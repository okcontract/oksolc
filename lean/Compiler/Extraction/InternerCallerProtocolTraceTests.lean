/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerNativeProtocol
import Compiler.Extraction.InternerCallerProtocolCache
import Compiler.Extraction.InternerCallerProtocolFailure
import Compiler.Extraction.InternerCallerCacheStreamTests
import Compiler.Extraction.InternerPublicationTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray Interner.InvocationTrace
open ConstructorItem
open Publication.OriginTests (Case source request key sorted)

/-- Graph callbacks are unreachable in this family; quantify over every
observation implementation rather than installing an empty successful trace. -/
def cached (case : Case) (observations : GraphObservations (Publication.Effects Nat)) (leading : List ProtocolEvent) :=
  find CacheStream.Tests.host 160 11 CacheTests.poison Interner.Queries.queries observations (source case)
    ⟨(CacheTests.constructed case).memory.memory.nextId, 0, 2⟩ (request case)
    ⟨⟨CacheStream.Tests.start case, { lookup := none }⟩, {}, leading⟩

/-- All six existing ownership cases consume the general source caller proof.
Their event lists are now computed by execution instead of supplied externally. -/
theorem cache_observed (case : Case) (observations : GraphObservations (Publication.Effects Nat)) (leading : List ProtocolEvent) :
    (cached case observations leading).2.events = CacheStream.Tests.events case leading [] ∧
      (cached case observations leading).2.tokens.incomplete = false ∧
      (cached case observations leading).2.tokens.toScope = ⟨some (CacheStream.Tests.close case).1, sorted case, .lookup⟩ := by
  have observed := CacheTests.prefix_observed case
  have initialized : Caller.initLookup CacheStream.Tests.host 160 11 (source case)
      ⟨(CacheTests.constructed case).memory.memory.nextId, 0, 2⟩ (request case)
      ⟨CacheStream.Tests.start case, { lookup := none }⟩ =
      (.ok (sorted case), (CacheTests.prepared case Normalization.Tests.success 160).2) := by
    rw [observed.2.1]
    exact Prod.ext observed.2.2.2.1 rfl
  obtain ⟨lookup, captured, events, complete, _, localScope⟩ := cached_events CacheStream.Tests.host 160 11
    (CacheStream.Tests.commutes case) CacheTests.poison Interner.Queries.queries observations (source case)
    ⟨(CacheTests.constructed case).memory.memory.nextId, 0, 2⟩ (request case) (CacheStream.Tests.start case)
    (sorted case) (CacheTests.prepared case Normalization.Tests.success 160).2 (key case) 17 leading
    (by cases case <;> rfl) initialized observed.2.2.2.2.1 observed.2.2.2.2.2.1
    observed.2.2.2.2.2.2.1 observed.2.2.2.2.2.2.2
  have same := Option.some.inj (Except.ok.inj (captured.symm.trans (CacheStream.Tests.trace_layout case).1))
  subst lookup
  exact ⟨by simpa only [CacheStream.Tests.events, List.append_nil] using events, complete, localScope⟩

theorem cache_events (case : Case) (observations : GraphObservations (Publication.Effects Nat)) (leading : List ProtocolEvent) :
    (cached case observations leading).2.events = CacheStream.Tests.events case leading [] ∧
      (cached case observations leading).2.tokens.incomplete = false :=
  ⟨(cache_observed case observations leading).1, (cache_observed case observations leading).2.1⟩

/-- The existing six cache cases now compare the complete scoped session after
cleanup, including normalized values, ownership phase and cursor. -/
theorem cache_scope (case : Case) (observations : GraphObservations (Publication.Effects Nat))
    (leading trailing : List ProtocolEvent) (other : Meaning) (read : Read) (sequence : BitVec 32) :
    scopeView (cached case observations leading).2 = (CacheStream.Tests.logical case leading trailing).2 := by
  have native := CacheStream.Tests.existing_family case leading trailing other read sequence
  have erased := find_erases CacheStream.Tests.host 160 11 CacheTests.poison Interner.Queries.queries observations
    (source case) ⟨(CacheTests.constructed case).memory.memory.nextId, 0, 2⟩ (request case) (CacheStream.Tests.start case) leading
  change CacheStream.Tests.actual case = ((cached case observations leading).1, (cached case observations leading).2.native) at erased
  have observed := cache_observed case observations leading
  rw [native.2.2.2.2.2.2]
  simp only [scopeView, observed.1, observed.2.2, CacheStream.Tests.events, List.append_nil]
  exact congrArg (fun after => (⟨⟨some (CacheStream.Tests.close case).1, sorted case, .lookup⟩,
    { after.world.graph with allocationCursor :=
      (leading ++ (CacheStream.Tests.initialization case).2.events.map Event.normalization ++
        (CacheStream.Tests.close case).2.events.map Event.normalization).length }⟩ : Interner.Scoped.Session))
    (congrArg Prod.snd erased).symm

/-- The computed complete leaf is immediately consumed by the existing checked
scoped/word proof. The native caller and logical cursor use that same stream. -/
theorem cache_composed (case : Case) (observations : GraphObservations (Publication.Effects Nat))
    (leading trailing : List ProtocolEvent) (other : Meaning) (read : Read) (sequence : BitVec 32) :
    (cached case observations leading).1 = .ok 17 ∧
      (cached case observations leading).2.native = (CacheStream.Tests.actual case).2 ∧
      Good (source case) (request case).arguments (cached case observations leading).2.native.world ∧
      (CacheStream.Tests.logical case leading trailing).1 = .ok 17 ∧
      (CacheStream.Tests.logical case leading trailing).2.heap.allocationCursor = (cached case observations leading).2.events.length := by
  have native := CacheStream.Tests.existing_family case leading trailing other read sequence
  have erased := find_erases CacheStream.Tests.host 160 11 CacheTests.poison Interner.Queries.queries observations
    (source case) ⟨(CacheTests.constructed case).memory.memory.nextId, 0, 2⟩ (request case) (CacheStream.Tests.start case) leading
  change CacheStream.Tests.actual case = ((cached case observations leading).1, (cached case observations leading).2.native) at erased
  refine ⟨(congrArg Prod.fst erased).symm.trans native.1, (congrArg Prod.snd erased).symm, ?_, native.2.2.2.2.2.1, ?_⟩
  · exact (congrArg (fun after => Good (source case) (request case).arguments after.world)
      (congrArg Prod.snd erased)).mp native.2.1
  · rw [native.2.2.2.2.2.2, (cache_events case observations leading).1]
    simp only [CacheStream.Tests.events, List.append_nil]

/-- Earlier capacity failure emits no protocol operation, even with arbitrary
host callbacks and graph observers. Its native caller scope is closed. -/
theorem capacity_no_events (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (observations : GraphObservations σ) (source buffer : View) (request : Interner.Request)
    (before : World σ) (leading : List ProtocolEvent) (full : q.atCapacity before.graph = true) :
    find external budget allocator p q observations source buffer request ⟨⟨before, { lookup := none }⟩, {}, leading⟩ =
      (.error (.language .capacity), ⟨⟨before, { lookup := none }⟩, {}, leading⟩) :=
  capacity_recorded external budget allocator p q observations source buffer request before leading full

theorem semantic_retention (external : External σ) (allocator : Nat) (fault : Fault) (before : Recorded σ)
    (semantic : fault.recoverable = false) :
    finish external allocator (.error fault : Except Fault NodeId) before = (.error fault, before) := by
  simp only [finish, ordinary, semantic, Bool.false_eq_true, ↓reduceIte]

/-- Missing local protocol tokens remain visible, even though erasure retains
the actual native take/cleanup result. They cannot certify an empty stream. -/
theorem missing_token (external : External σ) (allocator : Nat) (before : World σ) (handle : Handle)
    (slice : ArgumentSlice) :
    (taking external allocator ⟨before, { lookup := some handle }⟩ {}).1.incomplete = true ∧
    (closing external allocator ⟨before, { lookup := some handle }⟩ {}).1.incomplete = true ∧
    (closing external allocator ⟨before, ⟨none, some slice, false⟩⟩ {}).1.incomplete = true := by
  exact ⟨rfl, rfl, rfl⟩

/-- Reuse the existing physical publication/force fixture. Force has no child
dispatcher; its admitted probe is the only graph observation on this path. -/
def publicationPorts (fail : Bool) : GraphObservations (Publication.Effects Nat) where
  simplify := fun _ _ _ => []
  publish := fun key _ _ before => [.publicationProbe key (Publication.Tests.attempt fail key (Publication.forget before.memory)).1]
  insert := fun _ _ _ _ => []

def forced (fail : Bool) := force (Publication.external Publication.Tests.host) 160 7
  (Publication.Tests.actual fail) Caller.Tests.queries (publicationPorts fail)
  Publication.Tests.source Publication.Tests.buffer 42 Publication.Tests.request.item Publication.Tests.request.arguments
  ⟨⟨Publication.Tests.world, { lookup := none }⟩, {}, []⟩

attribute [local irreducible] force Caller.force

theorem force_publication (fail : Bool) :
    (forced fail).1 = (if fail then .error (.language .outOfMemory) else .ok ()) ∧
      (forced fail).2.native = (Publication.Tests.forced fail).2 ∧
      (forced fail).2.events =
        [.normalization (.prepare { origin := .scratch } (.ok ())), .normalization (.allocate .duplicate true),
          .publicationProbe Publication.Tests.forceKey (!fail)] ++
        (if fail then [.normalization (.release { origin := .scratch, owner := .caller })] else []) ∧
      (forced fail).2.tokens.incomplete = false := by
  have erased := force_erases (Publication.external Publication.Tests.host) 160 7 (Publication.Tests.actual fail)
    Caller.Tests.queries (publicationPorts fail) Publication.Tests.source Publication.Tests.buffer 42
    Publication.Tests.request.item Publication.Tests.request.arguments Publication.Tests.world []
  change Publication.Tests.forced fail = ((forced fail).1, (forced fail).2.native) at erased
  refine ⟨?_, (congrArg Prod.snd erased).symm, ?_, ?_⟩
  all_goals cases fail <;> insertion_kernel_rfl

/-- Publication refusal closes the caller-owned slice; success retains the
transfer phase. Both retain sorted values after native lookup retirement. -/
theorem force_scope (fail : Bool) :
    (forced fail).2.tokens.toScope =
      ⟨some { origin := .scratch, owner := if fail then .released else .caller, dead := true }, [1, 3],
        if fail then .cleanup else .transfer⟩ ∧ (forced fail).2.native.scope.lookup = none := by
  cases fail <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl⟩

def refusedTake := find (Publication.external (Normalization.Tests.external (fun site => site == .duplicate)))
  160 7 (Publication.Tests.actual false) Caller.Tests.queries (publicationPorts false)
  Publication.Tests.source Publication.Tests.buffer Publication.Tests.request
  ⟨⟨Publication.Tests.world, { lookup := none }⟩, {}, []⟩

theorem take_oom :
    refusedTake.1 = .error (.language .outOfMemory) ∧ refusedTake.2.native.scope = ⟨none, none, false⟩ ∧
      refusedTake.2.events = [.normalization (.prepare { origin := .scratch } (.ok ())),
        .normalization (.allocate .duplicate false)] ∧ refusedTake.2.tokens.incomplete = false := by
  exact ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem take_oom_scope :
    refusedTake.2.tokens.toScope = ⟨some { origin := .scratch, dead := true }, [1, 3], .lookup⟩ := by rfl'

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Tests
