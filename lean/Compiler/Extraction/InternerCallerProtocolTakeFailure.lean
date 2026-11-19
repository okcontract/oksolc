/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerProtocolTaken
import Compiler.Extraction.NormalizationEffects

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray ResourceAdapter Interner.InvocationTrace

attribute [local irreducible] Initialization.capture Take.capture Close.capture
attribute [local irreducible] Interner.Scoped.initScope Interner.Scoped.take

/-- Refused borrowing retains the original lookup token and the actual reached
native memory. General take admission derives the OOM outcome and readiness for
lookup cleanup; neither a new owner nor a successful allocation is assumed. -/
theorem take_refused_recorded (external : External σ) (allocator : Nat) (origin : NormalizationOwnership.Origin)
    (source : View) (original : List NodeId) (handle : Handle) (before : World σ)
    (fault : Fault) (reached : OwnedCall.State σ) (leading : List ProtocolEvent)
    (ready : Ready allocator source original handle before.memory) (admitted : Admitted external)
    (failed : OwnedCall.take external allocator ⟨before, { lookup := some handle }⟩ = (.error fault, reached)) :
    let input : Recorded σ := ⟨⟨before, { lookup := some handle }⟩,
      { lookup := some (token origin handle), items := handle.values }, leading⟩
    let captured := Take.capture external allocator origin handle before.memory
    let entry : Recorded σ := ⟨reached, input.tokens, leading ++ captured.2.events.map Event.normalization⟩
    fault = .language .outOfMemory ∧ reached.scope = { lookup := some handle } ∧
      Ready allocator source original handle reached.world.memory ∧
      captured.1.1 = false ∧ captured.1.2 = token origin handle ∧
      record (OwnedCall.take external allocator) (taking external allocator) input = (.error fault, entry) ∧
      ∀ suffix : List ProtocolEvent,
        Interner.Scoped.take (resources (entry.events ++ suffix) (.preparation .incomplete)) (scopeView input) =
          (.error .outOfMemory, scopeView entry) := by
  intro input captured entry
  have known := take_projected external allocator origin source original handle before leading [] ready admitted
  have relation := known.2.1
  simp only [record, failed] at relation
  obtain ⟨oom, locals, reachedReady⟩ := relation.2.2.2.2.2
  have checked := Take.checked_scope external allocator origin handle before.memory (normalizations leading) []
    (scopeView input).heap _ (by simp only [scopeView, input, normalizations_length]) known.1
  have refused : captured.1.1 = false := by
    have result := known.2.1.1
    rw [checked.2] at result
    simp only [record, failed] at result
    change (.error fault : Except Fault Unit) =
      (if captured.1.1 then .ok () else .error .outOfMemory : Except Interner.Error Unit).mapError Fault.language at result
    cases success : captured.1.1 with
    | false => rfl
    | true => simp only [success, ↓reduceIte, Except.mapError] at result; cases result
  have kept := NormalizationOwnership.take_with_failure normalizationOwnershipCode
    ((NormalizationOwnership.Trace.record (primitives external 0 allocator handle.items handle.items handle.values)).allocate .duplicate)
    (⟨⟨before.memory, handle, none, none⟩, []⟩ : NormalizationOwnership.Trace.Recorded (ResourceAdapter.State σ) Failure)
    captured.2 (token origin handle) captured.1.2 (by rw [← Take.capture]; change captured = ((false, captured.1.2), captured.2); rw [← refused])
  change (Take.capture external allocator origin handle before.memory).1.1 = false at refused
  change (Take.capture external allocator origin handle before.memory).1.2 = token origin handle at kept
  have recorded : record (OwnedCall.take external allocator) (taking external allocator) input = (.error fault, entry) := by
    have originEq : (token origin handle).origin = origin := rfl
    simp only [record, input, taking, originEq, failed, refused, kept, Bool.false_eq_true, ↓reduceIte]
    rfl
  refine ⟨oom, locals, reachedReady, refused, kept, recorded, ?_⟩
  intro suffix
  have projected := (take_projected external allocator origin source original handle before leading suffix ready admitted).2.2.1
  rw [recorded] at projected
  let logical := Interner.Scoped.take (resources (entry.events ++ suffix) (.preparation .incomplete)) (scopeView input)
  change (.error fault, scopeView entry) = (logical.1.mapError Fault.language, logical.2) at projected
  have result : logical.1 = .error .outOfMemory := by
    have same := congrArg Prod.fst projected
    rw [oom] at same
    cases selected : logical.1 with
    | ok value => rw [selected] at same; cases same
    | error error =>
      rw [selected] at same
      exact congrArg Except.error (Fault.language.inj (Except.error.inj same)).symm
  exact Prod.ext result (congrArg Prod.snd projected).symm

/-- The complete recorded caller returns ordinary OOM after refused borrowing.
Initialization and source routing are shared with successful paths. The reached
lookup readiness derives cleanup, and every scoped step consumes the same actual
history, including the refused allocation and final close. -/
theorem take_failed_projected (external : External σ) (budget allocator : Nat) (commutative : Bool)
    (p : Primitives σ) (q : Queries) (observations : GraphObservations σ) (model : Interner.Primitives)
    (source : View) (request : Interner.Request) (before : World σ)
    (memory : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (values : List NodeId) (prepared reached : OwnedCall.State σ) (fault : Fault) (key : Key) (deterministic : Bool)
    (leading trailing : List ProtocolEvent) (other : Meaning) (read : Read) (sequence : BitVec 32)
    (valid : Valid before.memory) (represented : Represents before.memory.memory source request.arguments)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (decoded : Interner.Scoped.commutative request.item = .ok commutative) (admitted : Admitted external)
    (initialized : Caller.initLookup external budget allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (room : q.atCapacity before.graph = false) (classified : q.deterministic request.item = .ok deterministic)
    (made : Interner.makeKey request values = .ok key) (absent : deterministic = true → before.graph.table key = none)
    (failed : OwnedCall.take external allocator prepared = (.error fault, reached))
    (capacityQuery : model.atCapacity { before.graph with allocationCursor := leading.length } = q.atCapacity before.graph)
    (classificationQuery : model.deterministic request.item = q.deterministic request.item) :
    let input := { before with memory := { before.memory with memory } }
    let actual := find external budget allocator p q observations source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨⟨input, { lookup := none }⟩, {}, leading⟩
    let logical := Interner.Scoped.findDetailed (resources (actual.2.events ++ trailing) (.preparation .incomplete)) model request
      { before.graph with allocationCursor := leading.length }
    fault = .language .outOfMemory ∧ actual.1 = .error fault ∧
      Good source request.arguments actual.2.native.world ∧ Closed actual.2.native.scope ∧
      (actual.1, scopeView actual.2) = (logical.1.mapError Fault.language, logical.2) ∧ actual.2.tokens.incomplete = false := by
  intro input actual logical
  let buffer : View := ⟨before.memory.memory.nextId, 0, 2⟩
  let init := Initialization.capture external budget allocator commutative source buffer request.arguments input.memory
  obtain ⟨lookup, captured, locals, tokenEq, _, ready, _, normalized, prefixProof⟩ := initialized_recorded external budget allocator
    commutative source request before memory pointer values prepared leading other read sequence
    valid represented allocated decoded admitted initialized
  let handle := init.2.effects.handle
  let initLeading := leading ++ init.2.events.map Event.normalization
  let initEntry : Recorded σ := ⟨prepared, { lookup := some lookup, items := handle.values }, initLeading⟩
  change ∀ suffix : List ProtocolEvent,
    Interner.Scoped.initScope (resources (initEntry.events ++ suffix) (.preparation .incomplete)) request
      ⟨{}, { before.graph with allocationCursor := leading.length }⟩ = (.ok values, scopeView initEntry) at prefixProof
  have entryEq : initEntry = ⟨⟨prepared.world, { lookup := some handle }⟩,
      { lookup := some (token lookup.origin handle), items := handle.values }, initLeading⟩ := by
    dsimp only [initEntry]
    rw [tokenEq]
    congr 2
    change (⟨prepared.world, prepared.scope⟩ : OwnedCall.State σ) = _
    rw [locals]
  have preparedShape : (⟨prepared.world, { lookup := some handle }⟩ : OwnedCall.State σ) = prepared := by rw [← locals]
  obtain ⟨oom, reachedLocals, reachedReady, _, _, takenRecord, takeProof⟩ := take_refused_recorded external allocator lookup.origin
    source request.arguments handle prepared.world fault reached initLeading ready admitted (by rw [preparedShape]; exact failed)
  rw [← entryEq] at takenRecord takeProof
  have tokensEq : initEntry.tokens = { lookup := some (token lookup.origin handle), items := handle.values } := by
    change ({ lookup := some lookup, items := handle.values } : Tokens) = _
    rw [tokenEq]
    rfl
  rw [tokensEq] at takenRecord takeProof
  subst fault
  let taken := Take.capture external allocator lookup.origin handle prepared.world.memory
  let closeLeading := initLeading ++ taken.2.events.map Event.normalization
  let closeEntry : Recorded σ := ⟨reached,
    { lookup := some (token lookup.origin handle), items := handle.values }, closeLeading⟩
  change record (OwnedCall.take external allocator) (taking external allocator) initEntry =
    (.error (.language .outOfMemory), closeEntry) at takenRecord
  have closeEntryEq : closeEntry = ⟨⟨reached.world, { lookup := some handle }⟩,
      { lookup := some (token lookup.origin handle), items := handle.values }, closeLeading⟩ := by
    dsimp only [closeEntry]
    congr 1
    change (⟨reached.world, reached.scope⟩ : OwnedCall.State σ) = _
    rw [reachedLocals]
  let closed := record (cleanup external allocator) (closing external allocator) closeEntry
  have closeProof := lookup_close_projected external allocator lookup.origin source request.arguments handle reached.world
    closeLeading trailing reachedReady
  rw [← closeEntryEq] at closeProof
  change closed.1 = .ok () ∧ _ at closeProof
  have body := findBody_after_take external budget allocator p q observations source buffer request key deterministic values
    ⟨⟨input, { lookup := none }⟩, {}, leading⟩ initEntry closeEntry (.error (.language .outOfMemory))
    room normalized classified made absent takenRecord
  have actualEq : actual = (.error (.language .outOfMemory), closed.2) := by
    change finish external allocator (findBody external budget allocator p q observations source buffer request _).1
      (findBody external budget allocator p q observations source buffer request _).2 = _
    rw [body]
    change finish external allocator (.error (.language .outOfMemory) : Except Fault NodeId) closeEntry = _
    simp only [finish, ordinary, Fault.recoverable, ↓reduceIte]
    change ((match closed.1 with | .error fault => Except.error fault | .ok () => .error (.language .outOfMemory)), closed.2) = _
    rw [closeProof.1]
  let closeEvents : List ProtocolEvent :=
    (Close.capture external allocator (token lookup.origin handle) .lookup handle reached).2.events.map Event.normalization
  have events : closed.2.events = closeLeading ++ closeEvents := by
    simp only [closed, record, closeEntry, closing, reachedLocals]
    rfl
  let r := resources (closed.2.events ++ trailing) (.preparation .incomplete)
  have initializedScope : Interner.Scoped.initScope r request ⟨{}, { before.graph with allocationCursor := leading.length }⟩ =
      (.ok values, scopeView initEntry) := by
    simpa only [r, events, closeLeading, initEntry, List.append_assoc] using
      prefixProof (taken.2.events.map Event.normalization ++ (closeEvents ++ trailing))
  have takenScope : Interner.Scoped.take r (scopeView initEntry) = (.error .outOfMemory, scopeView closeEntry) := by
    simpa only [r, events, closeLeading, closeEntry, List.append_assoc] using takeProof (closeEvents ++ trailing)
  have modelRun := scoped_after_take r model request key deterministic values
    { before.graph with allocationCursor := leading.length } (scopeView initEntry) (scopeView closeEntry) (.error .outOfMemory)
    (capacityQuery.trans room) initializedScope (classificationQuery.trans classified) made absent takenScope
  have logicalEq : logical = (.error .outOfMemory, Interner.Scoped.close r (scopeView closeEntry)) := by
    simpa only [logical, actualEq, r] using modelRun
  rw [actualEq, logicalEq]
  exact ⟨rfl, rfl, closeProof.2.1, closeProof.2.2.1, Prod.ext rfl closeProof.2.2.2.2.1, closeProof.2.2.2.2.2⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace
