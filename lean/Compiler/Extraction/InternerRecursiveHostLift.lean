/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionProtocolEffects
import Compiler.Extraction.InternerInvocationChildTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ChildTrace.HostLift
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Forward the reached native session and preserve its unrelated child history.
Protocol events are supplied by the existing child recorder, not by host calls. -/
def request (host : α → Session σ → β × σ) (argument : α) (before : Session (Recorded σ ε)) :=
  let ran := host argument (before.mapEffects Prod.fst)
  (ran.1, (ran.2, before.effects.2))

def release (host : α → Session σ → σ) (argument : α) (before : Session (Recorded σ ε)) :=
  (host argument (before.mapEffects Prod.fst), before.effects.2)

def external (host : External σ) : External (Recorded σ ε) where
  allocate := fun site before bytes effects =>
    let ran := host.allocate site (before.mapEffects Prod.fst) bytes effects.1
    (ran.1, (ran.2, effects.2))
  free := release host.free

def operations (ops : Insertion.Operations σ) : Insertion.Operations (Recorded σ ε) where
  arguments := external ops.arguments
  create := request ops.create
  copy := request ops.copy
  bytes := release ops.bytes
  objects := release ops.objects
  append := request ops.append
  probe := request ops.probe

def backing (allocate : Backing.Registry.Allocate σ) : Backing.Registry.Allocate (Recorded σ ε) :=
  fun allocator bytes alignment effects =>
    let ran := allocate allocator bytes alignment effects.1
    (ran.1, (ran.2, effects.2))

def growth (calls : Growth.Registered.Callbacks σ) : Growth.Registered.Callbacks (Recorded σ ε) where
  remap := calls.remap
  release := fun allocator base bytes alignment effects =>
    (calls.release allocator base bytes alignment effects.1, effects.2)

/-- All host requests, responses and reached private effects commute with
erasure, including absent growth and the exact remap callback when present. -/
theorem hosts (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (calls : Option (Growth.Registered.Callbacks σ)) :
    Insertion.Native.HostBindings (operations (ε := ε) ops) ops (backing allocate) allocate (calls.map growth) calls Prod.fst := by
  refine ⟨⟨fun _ _ _ _ => rfl, fun _ _ => rfl⟩, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl, ?_⟩
  cases calls with
  | none => trivial
  | some calls =>
    exact (show Growth.Registered.Callbacks.Transport Prod.fst (growth (ε := ε) calls) calls from
      ⟨rfl, fun _ _ _ _ _ => rfl⟩)

/-- Preserve the seed context's static inputs and forward its effects. The
native caller subsequently replaces its seed host and graph callbacks as usual. -/
def base (original : PairInput.Context (Publication.Effects σ)) : PairInput.Context (Publication.Effects (Recorded σ ε)) where
  budget := original.budget
  allocator := original.allocator
  queries := original.queries
  external := {
    allocate := fun site before bytes effects =>
      let ran := original.external.allocate site (before.mapEffects (Publication.Effects.mapAllocator Prod.fst)) bytes
        (effects.mapAllocator Prod.fst)
      (ran.1, ran.2.mapAllocator (fun effect => (effect, effects.allocator.2)))
    free := fun slice before =>
      (original.external.free slice (before.mapEffects (Publication.Effects.mapAllocator Prod.fst))).mapAllocator
        (fun effect => (effect, before.effects.allocator.2)) }
  primitives := fun source address input => {
    simplify := fun key slice => record ((original.primitives source address input).simplify key slice) (fun _ => [])
    insert := fun key slice deterministic => record ((original.primitives source address input).insert key slice deterministic) (fun _ => [])
    publish := fun key slice id => record ((original.primitives source address input).publish key slice id) (fun _ => []) }

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ChildTrace.HostLift
