/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPublicationEffects

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication.Recording
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open Normalization.HostTrace

/-- Record the actual probe request and response in the same stream as native
normalization allocation/free calls. The probe's inner bucket implementation
remains opaque; this event does not claim to record its internal allocations. -/
def recordProbe (host : OwnedKeys.Physical.Probe σ) : OwnedKeys.Physical.Probe (Recorded σ) := fun key before =>
  let (result, reached) := host key (before.mapEffects Recorded.effects)
  (result, ⟨reached, before.effects.events ++ [.publicationProbe key result]⟩)

theorem probe_observation (host : OwnedKeys.Physical.Probe σ) (key : Key) (before : Session (Recorded σ)) :
    let original := host key (before.mapEffects Recorded.effects)
    let recorded := recordProbe host key before
    recorded.1 = original.1 ∧ recorded.2.effects = original.2 ∧
      recorded.2.events = before.effects.events ++ [.publicationProbe key original.1] := ⟨rfl, rfl, rfl⟩

theorem probe_transport (host : OwnedKeys.Physical.Probe σ) :
    OwnedKeys.Physical.Probe.Transport (recordProbe host) host Recorded.effects := fun _ _ => rfl

theorem probe_prefix (host : OwnedKeys.Physical.Probe σ) (leading : List Event) :
    OwnedKeys.Physical.Probe.Transport (recordProbe host) (recordProbe host) (prepend leading) := by
  intro key before
  simp [recordProbe, prepend, Session.mapEffects, List.append_assoc]

/-- The complete publication callback erases, including exact key ownership,
cache values, physical lifetime release and rejected states. No publication
correspondence conclusion is assumed in addition to the original host functions. -/
theorem publish_erases (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ)
    (allocator : Nat) (source : View) (key : Key) (owned : ArgumentSlice) (id : NodeId) :
    Effect.Transport (World.mapEffects (Effects.mapAllocator Recorded.effects))
      (Publication.publish (recordProbe hostProbe) (record host) allocator source key owned id)
      (Publication.publish hostProbe host allocator source key owned id) :=
  EffectTransport.publish (transport host) (probe_transport hostProbe) allocator source key owned id

theorem publish_prefix (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ)
    (allocator : Nat) (source : View) (key : Key) (owned : ArgumentSlice) (id : NodeId) (leading : List Event) :
    Effect.Transport (World.mapEffects (Effects.mapAllocator (prepend leading)))
      (Publication.publish (recordProbe hostProbe) (record host) allocator source key owned id)
      (Publication.publish (recordProbe hostProbe) (record host) allocator source key owned id) :=
  EffectTransport.publish (prefix_transport host leading) (probe_prefix hostProbe leading) allocator source key owned id

/-- Publication instrumentation is derived. Only the remaining simplification
and insertion callbacks need erasure, and their complete recording remains a
separate obligation. The original publication seed is replaced on both sides. -/
theorem find_erases (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ)
    (budget allocator : Nat) (source buffer : View)
    {p : Primitives (Effects (Recorded σ))} {q : Primitives (Effects σ)}
    (simplify : ∀ key slice, Effect.Transport (World.mapEffects (Effects.mapAllocator Recorded.effects))
      (p.simplify key slice) (q.simplify key slice))
    (insert : ∀ key slice deterministic, Effect.Transport (World.mapEffects (Effects.mapAllocator Recorded.effects))
      (p.insert key slice deterministic) (q.insert key slice deterministic))
    (queries : Caller.Queries) (request : Interner.Request) (before : World (Effects (Recorded σ))) :
    Caller.find (external host) budget allocator (callbacks hostProbe host allocator source q)
        queries source buffer request (before.mapEffects (Effects.mapAllocator Recorded.effects)) =
      ((Caller.find (external (record host)) budget allocator (callbacks (recordProbe hostProbe) (record host) allocator source p)
          queries source buffer request before).1,
       (Caller.find (external (record host)) budget allocator (callbacks (recordProbe hostProbe) (record host) allocator source p)
          queries source buffer request before).2.mapEffects (Effects.mapAllocator Recorded.effects)) :=
  EffectTransport.find (transport host) (probe_transport hostProbe) budget allocator source buffer
    simplify insert queries request before

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication.Recording
