/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationTraceScope
import Compiler.Extraction.NormalizationResourcesProofs

namespace Compiler.Extraction.Memory.Arguments.Normalization.ResourceAdapter.TraceBridge
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open NormalizationOwnership.Trace

/-- The transcript is produced by the actual physical adapter operations. Its
private world is kept intact; the trace cursor is only an observation index. -/
def captured (external : External σ) (budget allocator : Nat) (commutative : Bool) (source buffer : View)
    (values : List NodeId) (exit : NormalizationOwnership.Exit) (before : Session σ) :=
  normalizationOwnershipCode.runPrepared commutative source.length buffer.length
    (record (primitives external budget allocator source buffer values)) exit ⟨initial source values before, []⟩

theorem capture_erases (external : External σ) (budget allocator : Nat) (commutative : Bool) (source buffer : View)
    (values : List NodeId) (exit : NormalizationOwnership.Exit) (before : Session σ) :
    ResourceAdapter.run external budget allocator commutative source buffer values exit before =
      let execution := captured external budget allocator commutative source buffer values exit before
      (ResourceAdapter.observe execution.1 execution.2.effects, execution.2.effects.session) := by
  have erased := record_erases normalizationOwnershipCode (primitives external budget allocator source buffer values)
    commutative source.length buffer.length exit (initial source values before)
  unfold ResourceAdapter.run
  rw [erased]
  rfl

/-- The protocol recorder and the native lifecycle describe one execution,
including semantic rejection and its reached memory. No replay acceptance or
allocation/normalization success premise is needed for this equality. -/
theorem capture_native (external : External σ) (budget allocator : Nat) (commutative : Bool) (source buffer : View)
    (values : List NodeId) (exit : NormalizationOwnership.Exit) (before : Session σ) :
    let execution := captured external budget allocator commutative source buffer values exit before
    let native := Normalization.run normalizationOwnershipCode external budget allocator commutative source buffer values exit before
    (ResourceAdapter.observe execution.1 execution.2.effects, execution.2.effects.session) = (some native.1, native.2) :=
  (capture_erases external budget allocator commutative source buffer values exit before).symm.trans
    (run_eq external budget allocator commutative source buffer values exit before)

/-- Replay is bound to this exact physical execution; the suffix is not consumed.
No assumption about sorting, allocation decisions or final memory is used. -/
theorem capture_replays (external : External σ) (budget allocator : Nat) (commutative : Bool) (source buffer : View)
    (values : List NodeId) (exit : NormalizationOwnership.Exit) (before : Session σ)
    (suffix : List (Event Failure)) :
    let execution := captured external budget allocator commutative source buffer values exit before
    normalizationOwnershipCode.runPrepared commutative source.length buffer.length
      (replay (execution.2.events ++ suffix) (.preparation .incomplete)) exit 0 =
      (execution.1, execution.2.events.length) :=
  run_replay (primitives external budget allocator source buffer values) (.preparation .incomplete)
    commutative source.length buffer.length exit (initial source values before) suffix

/-- A local physical transcript can be embedded between earlier and later
invocations. Its cursor advances only over its own actual calls. -/
theorem capture_replays_at (external : External σ) (budget allocator : Nat) (commutative : Bool) (source buffer : View)
    (values : List NodeId) (exit : NormalizationOwnership.Exit) (before : Session σ)
    (leading suffix : List (Event Failure)) :
    let execution := captured external budget allocator commutative source buffer values exit before
    normalizationOwnershipCode.runPrepared commutative source.length buffer.length
      (replay (leading ++ (execution.2.events ++ suffix)) (.preparation .incomplete)) exit leading.length =
      (execution.1, leading.length + execution.2.events.length) := by
  have reproduced := capture_replays external budget allocator commutative source buffer values exit before suffix
  have mapped := NormalizationOwnership.run_prepared_transport normalizationOwnershipCode
    (replay ((captured external budget allocator commutative source buffer values exit before).2.events ++ suffix) (.preparation .incomplete))
    (replay (leading ++ ((captured external budget allocator commutative source buffer values exit before).2.events ++ suffix)) (.preparation .incomplete))
    (fun cursor => leading.length + cursor) (replay_prefix _ leading (.preparation .incomplete))
    commutative source.length buffer.length exit 0
  rw [reproduced] at mapped
  simpa only [Nat.add_zero] using mapped

inductive Rejection where
  | physical (reason : ResourceAdapter.Rejection)
  | scope (reason : Scope.Rejection Failure)
  deriving Repr

/-- Shared physical admission for live initialization and complete lifecycles. -/
def checkPhysical (after : ResourceAdapter.State σ) (projection : Except (Scope.Rejection Failure) α) : Except Rejection α :=
  match after.rejected with
  | some reason => .error (.physical reason)
  | none => projection.mapError Rejection.scope

theorem check_physical_sound (after : ResourceAdapter.State σ) (projection : Except (Scope.Rejection Failure) α)
    (output : α) (accepted : checkPhysical after projection = .ok output) :
    after.rejected = none ∧ projection = .ok output := by
  cases clean : after.rejected with
  | some reason => simp [checkPhysical, clean] at accepted
  | none =>
    cases projection <;> simp [checkPhysical, clean, Except.mapError] at accepted
    exact ⟨rfl, congrArg Except.ok accepted⟩

/-- A physical semantic fault is never admitted through the total resource
projection. Ordinary OOM remains an accepted compiler outcome with its reached
memory/effects. -/
def checked (execution : NormalizationOwnership.PreparedResult Failure × Recorded (ResourceAdapter.State σ) Failure)
    (leading suffix : List (Event Failure)) (request : Interner.Request) (exit : NormalizationOwnership.Exit) (graph : Interner.Heap) :
    Except Rejection (Except Interner.Error NormalizationOwnership.Outcome × Interner.Scoped.Session) :=
  checkPhysical execution.2.effects
    (Scope.checked (leading ++ (execution.2.events ++ suffix)) (.preparation .incomplete) request exit graph)

/-- Accepted replay is the same physical ownership protocol and exact event
cursor. Earlier/later invocations retain their positions and events. -/
theorem checked_scope (external : External σ) (budget allocator : Nat) (commutative : Bool) (source buffer : View)
    (request : Interner.Request) (exit : NormalizationOwnership.Exit) (before : Session σ) (graph : Interner.Heap)
    (leading suffix : List (Event Failure)) (scope : Except Interner.Error NormalizationOwnership.Outcome × Interner.Scoped.Session)
    (length : request.arguments.length = source.length) (bufferLength : buffer.length = 2)
    (decoded : Interner.Scoped.commutative request.item = .ok commutative) (start : graph.allocationCursor = leading.length)
    (accepted : checked (captured external budget allocator commutative source buffer request.arguments exit before) leading suffix request exit graph = .ok scope) :
    let execution := captured external budget allocator commutative source buffer request.arguments exit before
    ∃ result, execution.1 = .ok result ∧ execution.2.effects.rejected = none ∧
      Scope.observe scope = (some result, leading.length + execution.2.events.length) ∧
      scope = Scope.run (Scope.resources (leading ++ (execution.2.events ++ suffix)) (.preparation .incomplete)) request exit graph := by
  let execution := captured external budget allocator commutative source buffer request.arguments exit before
  change checked execution leading suffix request exit graph = .ok scope at accepted
  obtain ⟨clean, replayed⟩ := check_physical_sound _ _ _ accepted
  obtain ⟨decision, result, cursor, agreed, protocol, _, observed, ran⟩ := Scope.checked_sound _ _ _ _ _ _ replayed
  have decision_eq : decision = commutative := by rw [decoded] at agreed; exact Except.ok.inj agreed.symm
  subst decision
  have physical := capture_replays_at external budget allocator commutative source buffer request.arguments exit before leading suffix
  change normalizationOwnershipCode.runPrepared commutative source.length buffer.length
    (replay (leading ++ (execution.2.events ++ suffix)) (.preparation .incomplete)) exit leading.length = _ at physical
  simp only [bufferLength] at physical
  rw [length, start] at protocol
  have same := Prod.mk.inj (physical.symm.trans protocol)
  exact ⟨result, same.1, clean, by simpa only [same.2] using observed, ran⟩

end Compiler.Extraction.Memory.Arguments.Normalization.ResourceAdapter.TraceBridge
