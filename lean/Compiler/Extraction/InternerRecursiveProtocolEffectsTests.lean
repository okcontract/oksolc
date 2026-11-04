/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursiveProtocolBoundReturn
import Compiler.Extraction.InternerRecursiveHostLift
import Compiler.Extraction.InternerConstructorProtocolTraceTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ProtocolTrace.EffectsTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Caller.ProtocolTrace ConstructorItem.ProtocolTrace

/-- Existing recursive regressions specialize the shared native host lift. -/
def request (host : α → Session σ → β × σ) (argument : α) (before : Session (ChildTrace.Recorded σ ProtocolEvent)) :=
  ChildTrace.HostLift.request host argument before

def release (host : α → Session σ → σ) (argument : α) (before : Session (ChildTrace.Recorded σ ProtocolEvent)) :=
  ChildTrace.HostLift.release host argument before

def external (host : External σ) : External (ChildTrace.Recorded σ ProtocolEvent) :=
  ChildTrace.HostLift.external host

def operations (ops : Insertion.Operations σ) : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent) :=
  ChildTrace.HostLift.operations ops

def backing (allocate : Backing.Registry.Allocate σ) : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent) :=
  ChildTrace.HostLift.backing allocate

theorem hosts (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ) :
    Insertion.Native.HostBindings (operations ops) ops (backing allocate) allocate none none Prod.fst :=
  ChildTrace.HostLift.hosts ops allocate none

def liftedParent (depth : Nat) (history leading : List ProtocolEvent) :=
  (step (operations (CallerTraceTests.ops false)) (backing (fun _ _ _ effects => (none, effects))) false 3
    Insertion.Tests.model (EffectTests.base (external Publication.Tests.host)) none 64
    (children (CallerTraceTests.ops false) (fun _ _ _ effects => (none, effects)) false 3 Insertion.Tests.model
      (EffectTests.base Publication.Tests.host) none 64 depth)
    (ChildTrace.liftObservations (observe (Tests.family depth)))).operation
      24 [1, 1] AssemblyItem.Initializers.Tests.debug (ChildTrace.restore history EffectTests.initial) leading

attribute [local irreducible] unfold step Tests.parent Tests.family liftedParent

/-- The existing recursive OOM family instantiates the real host bindings, with
independent earlier child and parent histories, at every finite child depth. -/
theorem parent_binding (depth : Nat) (history leading : List ProtocolEvent) :
    Tests.parent (depth + 1) leading = mapReturn (Publication.Effects.mapAllocator Prod.fst) (liftedParent depth history leading) := by
  have bound := unfold_step_traced (hosts (CallerTraceTests.ops false) (fun _ _ _ effects => (none, effects))) false 3 Insertion.Tests.model
    (outerBase := EffectTests.base (external Publication.Tests.host)) (base := EffectTests.base Publication.Tests.host)
    rfl 64 rfl rfl depth
  simpa only [Tests.parent, Tests.family, liftedParent, mapConstructors, ChildTrace.erase_restore] using
    congrArg (fun family => family.operation 24 [1, 1] AssemblyItem.Initializers.Tests.debug
      (ChildTrace.restore history EffectTests.initial) leading) bound

/-- Reuse the existing native OOM and cleanup evidence through the new binding;
the projection cannot replace its event sequence or parent cleanup metadata. -/
theorem recursive_oom (history : List ProtocolEvent) :
    (liftedParent 1 history []).1 = .error (.language .outOfMemory) ∧
      Tests.nestedFailure (liftedParent 1 history []).2.events = true ∧
      (liftedParent 1 history []).2.tokens.incomplete = false ∧
      (liftedParent 1 history []).2.native.scope = ⟨none, none, false⟩ := by
  have original := Tests.recursive_oom
  rw [parent_binding 1 history []] at original
  exact original

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ProtocolTrace.EffectsTests
