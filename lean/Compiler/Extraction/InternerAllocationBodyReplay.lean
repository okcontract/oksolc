/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorProtocolPreparedEntry
import Compiler.Extraction.InternerNativeAllocationEntry
import Compiler.Extraction.InternerConstructorProtocolEffects

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Recursive Caller.ProtocolTrace Interner.InvocationTrace
open ConstructorItem.ProtocolTrace (Capture eraseCapture EntryProjected)

theorem body_replay_from_entry (action : Capture (Publication.Effects σ) NodeId) (prefixed : Prefixed action)
    (leading stream : List ProtocolEvent) (root : ChildTrace.TracedWorld σ ProtocolEvent)
    (predicate : World (Publication.Effects σ) → Prop) (request : Interner.Request)
    (primitives : Nat × Nat → Interner.Primitives)
    (kept : ∀ before, predicate before → ordinary (action before []).1 = true → predicate (action before []).2.native.world)
    (projected : ∀ (before : ChildTrace.TracedWorld σ ProtocolEvent) (earlier trailing : List ProtocolEvent),
      Frame root predicate before → ChildTrace.history root ++ earlier = ChildTrace.history before →
      ChildTrace.history (record action before).2 ++ trailing = stream → ordinary (record action before).1 = true →
      EntryProjected (primitives (before.memory.memory.nextId, before.memory.memory.nextAddress)) request before.graph
        (leading ++ earlier) trailing (action (ChildTrace.erase before) (leading ++ earlier))) :
    BodyReplay leading stream root predicate action (fun ids =>
      Interner.Scoped.find (resources (rebase leading (ChildTrace.history root).length stream) (.preparation .incomplete))
        (primitives ids) request) := by
  intro before held admitted completed
  obtain ⟨earlier, historyBefore⟩ := held.2
  obtain ⟨trailing, historyAfter⟩ := admitted
  have actual := prefixed (ChildTrace.erase before) (leading ++ earlier) []
  simp only [List.append_nil] at actual
  have checked := projected before earlier trailing held historyBefore historyAfter completed
  rw [actual] at checked
  have completed' : ordinary (action (ChildTrace.erase before) []).1 = true := completed
  have same := checked completed'
  have streamSame : rebase leading (ChildTrace.history root).length stream =
      (leading ++ earlier) ++ (action (ChildTrace.erase before) []).2.events ++ trailing := by
    rw [← historyAfter]
    change rebase leading (ChildTrace.history root).length
      ((ChildTrace.history before ++ (action (ChildTrace.erase before) []).2.events) ++ trailing) = _
    rw [← historyBefore]
    simp only [rebase, List.append_assoc, List.drop_left]
  have beforeCursor : MissStream.childCursor leading.length root before = (leading ++ earlier).length := by
    simp only [MissStream.childCursor, ← historyBefore, List.length_append]
    omega
  have afterCursor : MissStream.childCursor leading.length root (record action before).2 =
      ((leading ++ earlier) ++ (action (ChildTrace.erase before) []).2.events).length := by
    change leading.length + (ChildTrace.history before ++ (action (ChildTrace.erase before) []).2.events).length -
      (ChildTrace.history root).length = _
    simp only [← historyBefore, List.length_append]
    omega
  refine ⟨?_, ?_, ?_⟩
  · simpa only [record, ChildTrace.record, ChildTrace.erase_restore, eraseCapture] using kept (ChildTrace.erase before) held.1 completed'
  · have result := congrArg (fun pair => pair.1) same.1
    simpa only [Interner.Scoped.find, streamSame, Caller.ProtocolTrace.prepend, cursorGraph, beforeCursor] using result
  · have graph := congrArg (fun pair => pair.2.heap) same.1
    simp only [cursorGraph, afterCursor, beforeCursor]
    simpa only [Interner.Scoped.find, streamSame, Caller.ProtocolTrace.prepend, scopeView, cursorGraph, beforeCursor,
      record, ChildTrace.record, eraseCapture, ChildTrace.restore, World.mapEffects, Session.mapEffects,
      Publication.Effects.mapAllocator] using graph

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Recursive Caller.ProtocolTrace Interner.InvocationTrace
open ConstructorItem.ProtocolTrace

/-- Transport a complete traced entry through the existing capture erasure.
The same native capture derives its rebased full stream for every entry route. -/
theorem body_replay_from_traced_entry
    {action : Capture (Publication.Effects σ) NodeId}
    {outerAction : Capture (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)) NodeId}
    (prefixed : Prefixed action)
    (mapped : ∀ before leading, action (ChildTrace.erase before) leading =
      mapReturn (Publication.Effects.mapAllocator Prod.fst) (outerAction before leading))
    {leading stream : List ProtocolEvent} {root : ChildTrace.TracedWorld σ ProtocolEvent}
    {predicate : World (Publication.Effects σ) → Prop} {request : Interner.Request}
    {primitives : Nat × Nat → Interner.Primitives}
    (kept : ∀ before, predicate before → ordinary (action before []).1 = true → predicate (action before []).2.native.world)
    (projected : ∀ (before : ChildTrace.TracedWorld σ ProtocolEvent) (earlier trailing : List ProtocolEvent),
      Frame root predicate before →
      (outerAction before (leading ++ earlier)).2.events ++ trailing = rebase leading (ChildTrace.history root).length stream →
      EntryProjected (primitives (before.memory.memory.nextId, before.memory.memory.nextAddress)) request before.graph
        (leading ++ earlier) trailing (outerAction before (leading ++ earlier))) :
    BodyReplay leading stream root predicate action (fun ids =>
      Interner.Scoped.find (resources (rebase leading (ChildTrace.history root).length stream) (.preparation .incomplete))
        (primitives ids) request) := by
  apply body_replay_from_entry action prefixed leading stream root predicate request primitives kept
  intro before earlier trailing held historyBefore historyAfter completed
  have capture := prefixed (ChildTrace.erase before) (leading ++ earlier) []
  simp only [List.append_nil] at capture
  have joined : (outerAction before (leading ++ earlier)).2.events ++ trailing =
      rebase leading (ChildTrace.history root).length stream := by
    have events := congrArg (fun ran => ran.2.events) (mapped before (leading ++ earlier))
    change (action (ChildTrace.erase before) (leading ++ earlier)).2.events = (outerAction before (leading ++ earlier)).2.events at events
    rw [← events, capture, ← historyAfter]
    change (leading ++ earlier) ++ (action (ChildTrace.erase before) []).2.events ++ trailing =
      rebase leading (ChildTrace.history root).length
        ((ChildTrace.history before ++ (action (ChildTrace.erase before) []).2.events) ++ trailing)
    rw [← historyBefore]
    simp only [rebase, List.append_assoc, List.drop_left]
  apply EntryProjected.of_outcome _ (projected before earlier trailing held joined)
  exact (congrArg outcome (mapped before (leading ++ earlier))).trans (mapReturn_outcome _ _)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
