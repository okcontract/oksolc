/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeAllocationTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Recursive Caller.ProtocolTrace
open ConstructorItem.ProtocolTrace (Capture eraseCapture)

/-- Replay has its own caller prefix. Raw child history before the miss is
removed once; every subsequent event retains its relative position. -/
def rebase (leading : List ProtocolEvent) (origin : Nat) (stream : List ProtocolEvent) : List ProtocolEvent :=
  leading ++ stream.drop origin

theorem rebase_slot (leading stream : List ProtocolEvent) (origin position : Nat) (reached : origin ≤ position) :
    (rebase leading origin stream)[leading.length + position - origin]? = stream[position]? := by
  unfold rebase
  rw [List.getElem?_append_right (by omega), List.getElem?_drop]
  congr 1
  omega

/-- The native entry is selected from the raw stream, while logical replay
uses the caller's actual prefix and the existing relative child cursor. -/
theorem enter_relative_admitted (action : Capture (Publication.Effects σ) NodeId) (marked : Begins action)
    (leading stream : List ProtocolEvent) (root before : ChildTrace.TracedWorld σ ProtocolEvent)
    (reached : (ChildTrace.history root).length ≤ (ChildTrace.history before).length)
    (admitted : Resource.Admitted ChildTrace.history stream
      (ChildTrace.record (eraseCapture [] action) (fun world => (action world []).2.events)) before) :
    enter (rebase leading (ChildTrace.history root).length stream)
      (cursorGraph (MissStream.childCursor leading.length root) before) =
      (.ok (before.memory.memory.nextId, before.memory.memory.nextAddress),
        { before.graph with allocationCursor := MissStream.childCursor leading.length root before + 1 }) := by
  simp only [enter, cursorGraph, MissStream.childCursor,
    rebase_slot leading stream _ _ reached, admitted_entry action marked stream before admitted, entry]

def record (action : Capture (Publication.Effects σ) NodeId) : GraphAction (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)) NodeId :=
  ChildTrace.record (eraseCapture [] action) (fun before => (action before []).2.events)

/-- A native instrumentation step changes only history. The allocation cursors
are read before any constructor preparation or allocation occurs. -/
def enterNative : GraphAction (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)) (Nat × Nat) :=
  ChildTrace.record (fun before => (.ok (before.memory.memory.nextId, before.memory.memory.nextAddress), before))
    (fun before => [entry before])

theorem record_grows (action : GraphAction (Publication.Effects σ) α)
    (observe : World (Publication.Effects σ) → List ProtocolEvent) :
    Resource.Grows ChildTrace.history (ChildTrace.record action observe) :=
  fun before => ⟨observe (ChildTrace.erase before), rfl⟩

def Prefixed (action : Capture (Publication.Effects σ) NodeId) : Prop :=
  ∀ before earlier leading, action before (earlier ++ leading) =
    (let called := action before leading
     (called.1, Caller.ProtocolTrace.prepend earlier called.2))

/-- Factor the actual marked capture into its entry and existing body. This
uses the whole capture prefix law, including native result, tokens and state. -/
theorem record_mark (action : Capture (Publication.Effects σ) NodeId) (prefixed : Prefixed action) :
    record (mark action) = (enterNative >>= fun _ => record action) := by
  funext before
  have same := prefixed (ChildTrace.erase before) [entry (ChildTrace.erase before)] []
  simp only [List.append_nil] at same
  simp only [record, ChildTrace.record, eraseCapture, mark, List.nil_append, same, enterNative,
    Bind.bind, Effect.bind, Caller.ProtocolTrace.prepend, ChildTrace.erase_restore]
  simp only [ChildTrace.history, ChildTrace.restore, ChildTrace.erase, World.mapEffects, Session.mapEffects,
    Publication.Effects.mapAllocator, List.append_assoc]

/-- A parent predicate on native state is unaffected by entry instrumentation.
The original raw-history prefix also survives, fixing the relative cursor's
domain rather than relying on truncated subtraction. -/
def Frame (root : ChildTrace.TracedWorld σ ProtocolEvent) (predicate : World (Publication.Effects σ) → Prop)
    (before : ChildTrace.TracedWorld σ ProtocolEvent) : Prop :=
  predicate (ChildTrace.erase before) ∧ ChildTrace.history root <+: ChildTrace.history before

theorem enter_native_keeps (root : ChildTrace.TracedWorld σ ProtocolEvent)
    (predicate : World (Publication.Effects σ) → Prop) (before : ChildTrace.TracedWorld σ ProtocolEvent)
    (held : Frame root predicate before) : Frame root predicate (enterNative before).2 := by
  refine ⟨?_, held.2.trans (record_grows _ _ before)⟩
  simpa only [enterNative, ChildTrace.record, ChildTrace.erase_restore] using held.1

/-- The entry prefix satisfies the same resource relation used by the full
native dispatcher. Both its stream position and native identities are derived
from admission; its native frame follows from exact instrumentation erasure. -/
theorem enter_projects (leading stream : List ProtocolEvent) (root : ChildTrace.TracedWorld σ ProtocolEvent)
    (predicate : World (Publication.Effects σ) → Prop) :
    Resource.Projects ChildTrace.history stream (cursorGraph (MissStream.childCursor leading.length root))
      (Frame root predicate) enterNative (enter (rebase leading (ChildTrace.history root).length stream)) := by
  refine ⟨record_grows _ _, ?_⟩
  intro before held admitted _
  have position : (ChildTrace.history root).length ≤ (ChildTrace.history before).length := held.2.length_le
  have slot : stream[(ChildTrace.history before).length]? = some (entry before) := by
    change ChildTrace.history before ++ [entry (ChildTrace.erase before)] <+: stream at admitted
    obtain ⟨tail, rfl⟩ := admitted
    simp only [List.append_assoc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.singleton_append, List.getElem?_cons_zero]
    rfl
  have logical : enter (rebase leading (ChildTrace.history root).length stream)
      (cursorGraph (MissStream.childCursor leading.length root) before) =
      (.ok (before.memory.memory.nextId, before.memory.memory.nextAddress),
        { before.graph with allocationCursor := MissStream.childCursor leading.length root before + 1 }) := by
    simp only [enter, cursorGraph, MissStream.childCursor, rebase_slot leading stream _ _ position, slot, entry]
  refine ⟨enter_native_keeps root predicate before held, ?_, ?_⟩
  · rw [logical]
    rfl
  · rw [logical]
    simp only [cursorGraph, MissStream.childCursor, enterNative, ChildTrace.record, ChildTrace.history,
      ChildTrace.restore, ChildTrace.erase, World.mapEffects, Session.mapEffects, Publication.Effects.mapAllocator,
      List.length_append, List.length_singleton]
    congr 1
    simp only [ChildTrace.history] at position
    omega

/-- The body receives the allocation identities of its actual starting state.
Its native result/frame and graph correspondence remain the local recursive
obligation; history growth is supplied by the recorder, not by this premise. -/
def BodyReplay (leading stream : List ProtocolEvent) (root : ChildTrace.TracedWorld σ ProtocolEvent)
    (predicate : World (Publication.Effects σ) → Prop) (action : Capture (Publication.Effects σ) NodeId)
    (model : Nat × Nat → Interner.Action NodeId) : Prop :=
  ∀ before, Frame root predicate before → Resource.Admitted ChildTrace.history stream (record action) before →
      ordinary (record action before).1 = true →
      predicate (ChildTrace.erase (record action before).2) ∧
      (record action before).1 =
        (model (before.memory.memory.nextId, before.memory.memory.nextAddress)
          (cursorGraph (MissStream.childCursor leading.length root) before)).1.mapError Fault.language ∧
      cursorGraph (MissStream.childCursor leading.length root) (record action before).2 =
        (model (before.memory.memory.nextId, before.memory.memory.nextAddress)
          (cursorGraph (MissStream.childCursor leading.length root) before)).2

/-- Replaying a marked constructor reduces to replaying its existing body
from the state after entry. The body model receives the native cursors read at
that entry, rather than arbitrary or caller-supplied identities. Its actual
admission and the entry's exact correspondence are derived by resource bind. -/
theorem marked_projects (action : Capture (Publication.Effects σ) NodeId) (prefixed : Prefixed action)
    (leading stream : List ProtocolEvent) (root : ChildTrace.TracedWorld σ ProtocolEvent)
    (predicate : World (Publication.Effects σ) → Prop) (model : Nat × Nat → Interner.Action NodeId)
    (body : BodyReplay leading stream root predicate action model) :
    Resource.Projects ChildTrace.history stream (cursorGraph (MissStream.childCursor leading.length root))
      (Frame root predicate) (record (mark action))
      (enter (rebase leading (ChildTrace.history root).length stream) >>= model) := by
  refine ⟨record_grows _ _, ?_⟩
  intro before held admitted completed
  rw [record_mark action prefixed] at admitted completed ⊢
  let ids := (before.memory.memory.nextId, before.memory.memory.nextAddress)
  let middle := (enterNative before).2
  have ran : enterNative before = (.ok ids, middle) := rfl
  have firstIn := Resource.Admitted.first ChildTrace.history stream enterNative (fun _ => record action)
    (fun _ => record_grows _ _) before admitted
  have first := (enter_projects leading stream root predicate).run before held firstIn (by rw [ran]; rfl)
  have tailIn := Resource.Admitted.next ChildTrace.history stream enterNative (fun _ => record action)
    before middle ids ran admitted
  have last := body middle first.1 tailIn (by simpa only [Bind.bind, Effect.bind, ran] using completed)
  have same : (middle.memory.memory.nextId, middle.memory.memory.nextAddress) = ids := rfl
  rw [same] at last
  cases logical : enter (rebase leading (ChildTrace.history root).length stream)
      (cursorGraph (MissStream.childCursor leading.length root) before) with
  | mk result after =>
    rw [ran, logical] at first
    cases result with
    | error fault => cases first.2.1
    | ok value =>
      have equal : ids = value := Except.ok.inj first.2.1
      subst value
      have framed : Frame root predicate (record action middle).2 :=
        ⟨last.1, (enter_native_keeps root predicate before held).2.trans (record_grows _ _ middle)⟩
      simpa only [Bind.bind, Effect.bind, ran, logical, first.2.2] using And.intro framed last.2

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
