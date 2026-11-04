/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerAllocationRecursiveReplay
import Compiler.Extraction.InternerNativeAllocationTraceTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.AllocationRecursiveReplayTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open NativeRecursion Recursive NativeAllocationTraceTests
open Caller.ProtocolTrace (ProtocolEvent)
open RecursiveTests (debug)

def seed : Interner.Primitives where
  atCapacity := Interner.Queries.queries.atCapacity
  normalize := fun _ => pure []
  deterministic := Interner.Queries.queries.deterministic
  takeOwned := fun _ => pure ()
  simplify := fun _ => pure none
  insert := fun _ _ => pure 0
  publish := fun _ _ => pure ()

def constantModel (safety permitted : Bool) :=
  let before := NativeAllocationAdmissionTests.before safety permitted
  let stream := events safety permitted
  let model := AllocationTrace.streamReplay stream
    (AllocationTrace.recursiveModels Insertion.Tests.model 64 seed stream (.base .missingArguments) 1)
  model.constant 1 debug {before.graph with allocationCursor := 0}

/-- Both native allocator outcomes replay at the exact completed cursor, in
both admitted layouts. The seed supplies no constructor result oracle. -/
theorem constant_outcomes (safety permitted : Bool) :
    ((constantModel safety permitted).1, (constantModel safety permitted).2.allocationCursor) =
      (if permitted then .ok 5 else .error .outOfMemory, (events safety permitted).length) := by
  cases safety <;> cases permitted <;> insertion_kernel_rfl

def nested (safety permitted : Bool) :=
  (captures safety 2).operation (Interner.buildOpcode .ISZERO) [4] debug (NativeAllocationAdmissionTests.before safety permitted) []

def nestedModel (safety permitted : Bool) :=
  let before := NativeAllocationAdmissionTests.before safety permitted
  let stream := (nested safety permitted).2.events
  let model := AllocationTrace.streamReplay stream
    (AllocationTrace.recursiveModels Insertion.Tests.model 64 seed stream (.base .missingArguments) 2)
  model.operation (Interner.buildOpcode .ISZERO) [4] debug {before.graph with allocationCursor := 0}

/-- The existing ISZERO family reaches a real constant child. Recursive replay
retains the child failure/success and consumes the complete event stream. -/
theorem nested_outcomes (safety permitted : Bool) :
    ((nested safety permitted).1, (nested safety permitted).2.events.length) =
      ((nestedModel safety permitted).1.mapError Fault.language, (nestedModel safety permitted).2.allocationCursor) := by
  cases safety <;> cases permitted <;> insertion_kernel_rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.AllocationRecursiveReplayTests
