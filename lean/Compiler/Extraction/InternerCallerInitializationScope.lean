/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInitialization
import Compiler.Extraction.NormalizationTraceMemory

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Initialization
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.Extraction.InsertionSort Compiler.ZigAir.Memory.WordArray
open ResourceAdapter NormalizationOwnership.Trace

def checked (execution : NormalizationOwnership.PreparedInit Failure × Recorded (ResourceAdapter.State σ) Failure)
    (leading suffix : List (Event Failure)) (request : Interner.Request) (graph : Interner.Heap) :
    Except TraceBridge.Rejection (Except Interner.Error (List NodeId) × Interner.Scoped.Session) :=
  TraceBridge.checkPhysical execution.2.effects
    (Scope.checkedInit (leading ++ (execution.2.events ++ suffix)) (.preparation .incomplete) request graph)

/-- The actual live transcript replays between arbitrary earlier/later events.
The cursor counts protocol operations, not native host calls. -/
theorem capture_replays_at (external : External σ) (budget allocator : Nat) (commutative : Bool) (source buffer : View)
    (values : List NodeId) (before : Session σ) (leading suffix : List (Event Failure)) :
    let execution := capture external budget allocator commutative source buffer values before
    normalizationOwnershipCode.initPrepared commutative source.length buffer.length
      (replay (leading ++ (execution.2.events ++ suffix)) (.preparation .incomplete)) leading.length =
      (execution.1, leading.length + execution.2.events.length) :=
  init_replay_at (primitives external budget allocator source buffer values) (.preparation .incomplete)
    commutative source.length buffer.length (initial source values before) leading suffix

/-- Admission binds the live scoped session to this exact physical producer.
Semantic failure cannot disappear through Resources.prepare's cursor projection. -/
theorem checked_scope (external : External σ) (budget allocator : Nat) (commutative : Bool) (source buffer : View)
    (request : Interner.Request) (before : Session σ) (graph : Interner.Heap) (leading suffix : List (Event Failure))
    (scope : Except Interner.Error (List NodeId) × Interner.Scoped.Session)
    (length : request.arguments.length = source.length) (bufferLength : buffer.length = 2)
    (decoded : Interner.Scoped.commutative request.item = .ok commutative) (start : graph.allocationCursor = leading.length)
    (accepted : checked (capture external budget allocator commutative source buffer request.arguments before)
      leading suffix request graph = .ok scope) :
    let execution := capture external budget allocator commutative source buffer request.arguments before
    ∃ lookup, execution.1 = .ok lookup ∧ execution.2.effects.rejected = none ∧
      scope.2.scope.lookup = lookup ∧
      scope.1 = (match lookup with | none => .error .outOfMemory | some _ => .ok (normalized commutative source request.arguments)) ∧
      scope.2.heap = { graph with allocationCursor := leading.length + execution.2.events.length } ∧
      scope = Interner.Scoped.initScope (Scope.resources (leading ++ (execution.2.events ++ suffix)) (.preparation .incomplete)) request ⟨{}, graph⟩ := by
  let execution := capture external budget allocator commutative source buffer request.arguments before
  obtain ⟨clean, replayed⟩ := TraceBridge.check_physical_sound _ _ _ accepted
  obtain ⟨decision, lookup, cursor, agreed, protocol, _, ran⟩ := Scope.checked_init_sound _ _ _ _ _ replayed
  have decision_eq : decision = commutative := by rw [decoded] at agreed; exact Except.ok.inj agreed.symm
  subst decision
  have physical := capture_replays_at external budget allocator commutative source buffer request.arguments before leading suffix
  change normalizationOwnershipCode.initPrepared commutative source.length buffer.length
    (replay (leading ++ (execution.2.events ++ suffix)) (.preparation .incomplete)) leading.length = _ at physical
  have projected := Scope.init_projection _ _ request graph commutative lookup cursor decoded protocol
  simp only [bufferLength] at physical
  rw [length, start] at protocol
  have same := Prod.mk.inj (physical.symm.trans protocol)
  refine ⟨lookup, same.1, clean, ?_, ?_, ?_, ran⟩
  · rw [ran, projected]; cases lookup <;> rfl
  · rw [ran, projected]
    cases lookup with
    | none => rfl
    | some lookup =>
      have contents := Interner.Scoped.initialize_projection _ request _ _ _ projected
      have normalized := normalized_projection request.item commutative source request.arguments length decoded
      exact congrArg Except.ok (Option.some.inj (contents.symm.trans normalized))
  · rw [ran, projected]
    cases lookup <;> exact congrArg (fun cursor => { graph with allocationCursor := cursor }) same.2.symm

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Initialization
