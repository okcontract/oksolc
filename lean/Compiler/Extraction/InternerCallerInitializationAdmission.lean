/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInitializationScope

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Initialization
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open ResourceAdapter NormalizationOwnership.Trace

/-- An ordinary native initialization has no hidden adapter rejection or
preparation fault. Refused allocation remains an ordinary, recorded outcome;
incomplete preparation and malformed memory responses cannot satisfy this guard. -/
theorem capture_ordinary (external : External σ) (budget allocator : Nat) (commutative : Bool)
    (source buffer : View) (values : List NodeId) (before : Session σ)
    (completed : ordinary ((Normalization.init normalizationOwnershipCode external budget allocator commutative
      source buffer values before).1.mapError memoryFault) = true) :
    let execution := capture external budget allocator commutative source buffer values before
    execution.2.effects.rejected = none ∧ ∃ lookup, execution.1 = .ok lookup := by
  cases needed : !commutative || decide (source.length < normalizationOwnershipCode.threshold) with
  | true =>
    simp [capture, NormalizationOwnership.Code.initPrepared, NormalizationOwnership.Code.initWith,
      initial, needed]
  | false =>
    by_cases fits : source.length ≤ buffer.length
    · have choice : normalizationOwnershipCode.useScratch.test source.length buffer.length = true := by
        simp [normalizationOwnershipCode, NormalizationOwnership.Comparison.test, fits]
      have own : normalizationOwnershipCode.ownTemporary.test source.length buffer.length = false := by
        simp [normalizationOwnershipCode, NormalizationOwnership.Comparison.test, Nat.not_lt.mpr fits]
      cases copied : Compiler.Extraction.InsertionSort.Copied.run budget before.memory source (bufferPrefix buffer source.length) with
      | mk result memory =>
        cases result <;>
          simp [capture, NormalizationOwnership.Code.initPrepared, NormalizationOwnership.Code.initWith,
            record, primitives, initial, ResourceAdapter.prepare, Normalization.prepare, Normalization.init,
            needed, choice, own, copied, Except.mapError, ordinary, memoryFault, Fault.recoverable] at completed ⊢
    · have choice : normalizationOwnershipCode.useScratch.test source.length buffer.length = false := by
        simp [normalizationOwnershipCode, NormalizationOwnership.Comparison.test, fits]
      have own : normalizationOwnershipCode.ownTemporary.test source.length buffer.length = true := by
        simp [normalizationOwnershipCode, NormalizationOwnership.Comparison.test, Nat.lt_of_not_ge fits]
      cases reserved : Normalization.reserve external allocator values before with
      | mk result selected =>
        cases result with
        | error failure =>
          cases failure <;>
            simp [capture, NormalizationOwnership.Code.initPrepared, NormalizationOwnership.Code.initWith,
              record, primitives, initial, ResourceAdapter.allocate, failed, Normalization.init,
              needed, choice, reserved, Except.mapError, ordinary, memoryFault, Fault.recoverable] at completed ⊢
        | ok slice =>
          cases copied : Compiler.Extraction.InsertionSort.Copied.run budget selected.memory source (view slice) with
          | mk result memory =>
            cases result <;>
              simp [capture, NormalizationOwnership.Code.initPrepared, NormalizationOwnership.Code.initWith,
                record, primitives, initial, ResourceAdapter.allocate, ResourceAdapter.prepare, Normalization.prepare,
                Normalization.init, needed, choice, own, reserved, copied, Except.mapError, ordinary, memoryFault, Fault.recoverable] at completed ⊢

/-- Derive admission from this caller's actual ordinary result and transcript.
No expected checked result or successful allocation is supplied. -/
theorem checked_ordinary (external : External σ) (budget allocator : Nat) (commutative : Bool)
    (source buffer : View) (request : Interner.Request) (before : World σ)
    (leading suffix : List (Event Failure)) (graph : Interner.Heap)
    (length : request.arguments.length = source.length) (bufferLength : buffer.length = 2)
    (decoded : Interner.Scoped.commutative request.item = .ok commutative)
    (completed : ordinary (Caller.initLookup external budget allocator source buffer request
      ⟨before, { lookup := none }⟩).1 = true)
    (start : graph.allocationCursor = leading.length) :
    let execution := capture external budget allocator commutative source buffer request.arguments before.memory
    checked execution leading suffix request graph = .ok
      (Interner.Scoped.initScope (Scope.resources (leading ++ (execution.2.events ++ suffix)) (.preparation .incomplete))
        request ⟨{}, graph⟩) := by
  have native : ordinary ((Normalization.init normalizationOwnershipCode external budget allocator commutative
      source buffer request.arguments before.memory).1.mapError memoryFault) = true := by
    cases ran : Normalization.init normalizationOwnershipCode external budget allocator commutative
        source buffer request.arguments before.memory with
    | mk result reached =>
      cases result <;> simpa [Caller.initLookup, decoded, ran] using completed
  obtain ⟨clean, lookup, result⟩ := capture_ordinary external budget allocator commutative source buffer request.arguments before.memory native
  have replayed := capture_replays_at external budget allocator commutative source buffer request.arguments before.memory leading suffix
  rw [bufferLength, ← length] at replayed
  have within : ¬ (leading ++ ((capture external budget allocator commutative source buffer request.arguments before.memory).2.events ++ suffix)).length <
      leading.length + (capture external budget allocator commutative source buffer request.arguments before.memory).2.events.length := by
    simp only [List.length_append]
    omega
  simp only [checked, TraceBridge.checkPhysical, clean, Scope.checkedInit, decoded, start, replayed,
    Scope.admit, if_neg within, result, Except.mapError]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Initialization
