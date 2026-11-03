/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationResourcesInit
import Compiler.Extraction.NormalizationTrace
import Compiler.Extraction.NormalizationHostTrace
import Compiler.Extraction.InternerCallerMemory

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Initialization
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open ResourceAdapter NormalizationOwnership.Trace

/-- The existing protocol recorder observes the live prefix. No exit is run:
the caller retains the native handle while graph/recursive operations execute. -/
def capture (external : External σ) (budget allocator : Nat) (commutative : Bool) (source buffer : View)
    (values : List NodeId) (before : Session σ) :=
  normalizationOwnershipCode.initPrepared commutative source.length buffer.length
    (record (primitives external budget allocator source buffer values)) ⟨initial source values before, []⟩

theorem capture_spec (external : External σ) (budget allocator : Nat) (commutative : Bool) (source buffer : View)
    (values : List NodeId) (before : Session σ) :
    let execution := capture external budget allocator commutative source buffer values before
    let native := Normalization.init normalizationOwnershipCode external budget allocator commutative source buffer values before
    (observeInit execution.1 execution.2.effects, execution.2.effects.session) = (some native.1, native.2) ∧
      InitAligned execution.1 execution.2.effects := by
  have erased := NormalizationOwnership.init_prepared_transport normalizationOwnershipCode
    (record (primitives external budget allocator source buffer values))
    (primitives external budget allocator source buffer values) Recorded.effects
    (record_transport _) commutative source.length buffer.length ⟨initial source values before, []⟩
  have spec := init_spec external budget allocator commutative source buffer values before
  dsimp only [initialized] at spec
  rw [erased] at spec
  exact spec

/-- Host responses and their reached private effects erase to the original
native prefix. Host and protocol event sequences remain distinct. -/
theorem recorded_erases (external : External σ) (budget allocator : Nat) (commutative : Bool) (source buffer : View)
    (values : List NodeId) (before : Session (HostTrace.Recorded σ)) :
    let execution := capture (HostTrace.record external) budget allocator commutative source buffer values before
    let native := Normalization.init normalizationOwnershipCode external budget allocator commutative source buffer values
      (before.mapEffects HostTrace.Recorded.effects)
    (some native.1, native.2) =
      (observeInit execution.1 execution.2.effects, execution.2.effects.session.mapEffects HostTrace.Recorded.effects) := by
  have erased := (HostTrace.transport external).init normalizationOwnershipCode budget allocator commutative source buffer values before
  have captured := (capture_spec (HostTrace.record external) budget allocator commutative source buffer values before).1
  rw [erased]
  exact (congrArg (fun pair => (pair.1, pair.2.mapEffects HostTrace.Recorded.effects)) captured).symm

/-- The actual caller consumes the observed live result and exact reached
memory. Failure keeps its prior scope; success installs the native handle.
No validity, allocator success or completed-preparation premise is assumed. -/
theorem caller (external : External σ) (budget allocator : Nat) (commutative : Bool) (source buffer : View)
    (request : Interner.Request) (before : OwnedCall.State σ)
    (decoded : Interner.Scoped.commutative request.item = .ok commutative) :
    let execution := capture external budget allocator commutative source buffer request.arguments before.world.memory
    (observeInit execution.1 execution.2.effects).map (fun result =>
      let world := { before.world with memory := execution.2.effects.session }
      match result with
      | .error failure => (.error (memoryFault failure), { before with world })
      | .ok handle => (.ok handle.values, ⟨world, { lookup := some handle }⟩)) =
      some (Caller.initLookup external budget allocator source buffer request before) := by
  have captured := (capture_spec external budget allocator commutative source buffer request.arguments before.world.memory).1
  have mapped := congrArg (fun pair : Option (Except Failure Handle) × Session σ =>
    (pair.1.map (fun result =>
      let world := { before.world with memory := pair.2 }
      match result with
      | .error failure => (.error (memoryFault failure), { before with world })
      | .ok handle => (.ok handle.values, ⟨world, { lookup := some handle }⟩)) : Option (Except Fault (List NodeId) × OwnedCall.State σ))) captured
  simpa only [Caller.initLookup, decoded, Option.map] using mapped

/-- Successful caller initialization identifies the recorded token, handle and
reached state before a later segment is selected. No scoped result or arbitrary
origin is supplied by the client. -/
theorem capture_success (external : External σ) (budget allocator : Nat) (commutative : Bool)
    (source buffer : View) (request : Interner.Request) (before : World σ)
    (values : List NodeId) (prepared : OwnedCall.State σ)
    (decoded : Interner.Scoped.commutative request.item = .ok commutative)
    (succeeded : Caller.initLookup external budget allocator source buffer request
      ⟨before, { lookup := none }⟩ = (.ok values, prepared)) :
    let execution := capture external budget allocator commutative source buffer request.arguments before.memory
    ∃ lookup, execution.1 = .ok (some lookup) ∧
      prepared = ⟨⟨before.graph, execution.2.effects.session⟩, { lookup := some execution.2.effects.handle }⟩ ∧
      execution.2.effects.handle.values = values ∧ lookup = token lookup.origin execution.2.effects.handle := by
  let execution := capture external budget allocator commutative source buffer request.arguments before.memory
  have called := (caller external budget allocator commutative source buffer request ⟨before, { lookup := none }⟩ decoded).trans
    (congrArg some succeeded)
  change (observeInit execution.1 execution.2.effects).map _ = _ at called
  cases rejected : execution.2.effects.rejected with
  | some reason => cases reason <;> simp [observeInit, rejected] at called
  | none =>
    cases result : execution.1 with
    | error failure => cases failure; simp [observeInit, rejected, result] at called
    | ok lookup =>
      cases lookup with
      | none => simp [observeInit, rejected, result] at called
      | some lookup =>
        simp only [observeInit, rejected, result, Option.map_some, Option.some.injEq, Prod.mk.injEq, Except.ok.injEq] at called
        exact ⟨lookup, result, called.2.symm, called.1,
          ((capture_spec external budget allocator commutative source buffer request.arguments before.memory).2 lookup result).2.2⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Initialization
