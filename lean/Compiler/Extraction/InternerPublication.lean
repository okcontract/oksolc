/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.OwnedKeysPhysical
import Compiler.Extraction.InternerPhysicalDispatchProduction

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray

/-- The physical cache retains allocation identities; `World.graph.table` is
its existing semantic ID projection. Native cache binding remains an obligation.
Allocator effects cannot overwrite this ownership metadata. -/
structure Effects (σ : Type) where
  keys : OwnedKeys.Table
  allocator : σ

def forget (state : Session (Effects σ)) : Session σ :=
  ⟨state.heap, state.memory, state.effects.allocator⟩

def external (host : External σ) : External (Effects σ) where
  allocate site state bytes effects :=
    let (result, reached) := host.allocate site (forget state) bytes effects.allocator
    (result, ⟨effects.keys, reached⟩)
  free owned state := ⟨state.effects.keys, host.free owned (forget state)⟩

def probe (host : OwnedKeys.Physical.Probe σ) : OwnedKeys.Physical.Probe (Effects σ) :=
  fun key state => let (ok, reached) := host key (forget state); (ok, ⟨state.effects.keys, reached⟩)

def physical (world : World (Effects σ)) : OwnedKeys.Physical.State (Effects σ) :=
  ⟨world.memory.effects.keys, world.memory⟩

inductive Rejection where
  | descriptor | oldOwnership | sourceAlias | incomingAlias
  deriving DecidableEq, Repr

/-- An executable admission check on the exact reached descriptors. It checks
only the entry publication may release, not an unbounded table invariant. A
rejection is a semantic observation outside the accepted model, not native OOM.
This check is not inserted into the compiler or assumed to accept every call. -/
def admit (allocator : Nat) (source : View) (key : Key) (owned : ArgumentSlice)
    (before : World (Effects σ)) : Except Rejection Unit :=
  if key.arguments != owned.items then .error .descriptor else
  match before.memory.effects.keys key with
  | none => .ok ()
  | some old =>
    if key.arguments.isEmpty then .ok ()
    else if old.address = owned.address then .error .incomingAlias
    else if source.length ≠ 0 ∧ old.address = source.allocation then .error .sourceAlias
    else match before.memory.heap old.address with
      | some ⟨owner, .arguments values⟩ =>
        if owner == allocator && values == key.arguments then .ok () else .error .oldOwnership
      | _ => .error .oldOwnership

def commit (key : Key) (id : NodeId) (before : World (Effects σ))
    (execution : Except Failure Unit × OwnedKeys.Physical.State (Effects σ)) :
    Except Fault Unit × World (Effects σ) :=
  let memory := { execution.2.memory with effects := { execution.2.memory.effects with keys := execution.2.table } }
  let graph := match execution.1 with
    | .ok () => { before.graph with table := Cache.put equalityFields before.graph.table key id }
    | .error _ => before.graph
  (execution.1.mapError memoryFault, ⟨graph, memory⟩)

/-- The admitted source body. The cache-ID update is the proved value projection
of physical key publication; it is not a second native cache operation. -/
def body (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ) (allocator : Nat)
    (key : Key) (owned : ArgumentSlice) (id : NodeId) : GraphAction (Effects σ) Unit := fun before =>
  commit key id before (OwnedKeys.Physical.run (probe hostProbe) (external host) allocator key
    ⟨owned.address, id⟩ (physical before))

def publish (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ) (allocator : Nat)
    (source : View) (key : Key) (owned : ArgumentSlice) (id : NodeId) : GraphAction (Effects σ) Unit := fun before =>
  match admit allocator source key owned before with
  | .error _ => (.error (.language .safetyFault), before)
  | .ok () => body hostProbe host allocator key owned id before

def callbacks (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ) (allocator : Nat)
    (source : View) (p : Primitives (Effects σ)) : Primitives (Effects σ) :=
  { p with publish := publish hostProbe host allocator source }

theorem accepted_body (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ) (allocator : Nat)
    (source : View) (key : Key) (owned : ArgumentSlice) (id : NodeId) (before : World (Effects σ))
    (accepted : admit allocator source key owned before = .ok ()) :
    publish hostProbe host allocator source key owned id before = body hostProbe host allocator key owned id before := by
  simp only [publish, accepted]

theorem ordinary_admitted (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ) (allocator : Nat)
    (source : View) (key : Key) (owned : ArgumentSlice) (id : NodeId) (before : World (Effects σ))
    (completed : ordinary (publish hostProbe host allocator source key owned id before).1 = true) :
    admit allocator source key owned before = .ok () := by
  cases admitted : admit allocator source key owned before with
  | error reason => simp [publish, admitted, ordinary, Fault.recoverable] at completed
  | ok value => cases value; rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication
