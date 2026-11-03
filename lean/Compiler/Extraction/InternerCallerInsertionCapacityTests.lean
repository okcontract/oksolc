/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionCapacity
import Compiler.Extraction.InternerCallerTransferredPreparationFailureTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.CapacityTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open AssemblyItem.Creation.NativeFields.Tests (input source)
open CallerInputTests (values request key)

/-- The five-row initialized graph supplies the header before the actual caller
prefix. Arbitrary callbacks, growth and determinism share its reached check. -/
theorem initialized_entry (safety empty deterministic : Bool) (actions : Operations Nat)
    (reserve : Backing.Registry.Allocate Nat) (growth : Option (Growth.Registered.Callbacks Nat)) :
    checkedExecution actions reserve safety 7 6 (parent empty) source Insertion.Tests.model input (key empty)
      (normalized safety empty 4) deterministic (cells safety empty 4) (taken safety empty 4).2.world growth =
    .ok (execution actions reserve safety 7 6 (parent empty) source Insertion.Tests.model input (key empty)
      (normalized safety empty 4) deterministic (cells safety empty 4) (taken safety empty 4).2.world growth) := by
  have prior := initialized_prefix safety empty 4 (by decide)
  have entry := prior.caller_input (by decide)
  obtain ⟨owner, found, _, _⟩ := prior.facts.owner
  exact entry.checked_execution actions reserve safety 7 6 (parent empty) source Insertion.Tests.model (request empty)
    (values empty) input (key empty) (normalized safety empty 4) (lookup empty) (before safety empty 4)
    (taken safety empty 4).2 deterministic (cells safety empty 4) growth owner ⟨lifetime empty, 0⟩ found
    (readHeader_items _ _ _ _ prior.facts.header)

/-- Actual creation and clone OOM remain ordinary OOM after the checked native
entry. Cleanup owners still come from the caller theorem, not final evaluation. -/
theorem checked_preparation_oom (safety empty clone : Bool) : ∃ after,
    checkedExecution (TransferredPreparationFailureTests.actions clone) allocate safety 7 6 (parent empty) source
      Insertion.Tests.model input (key empty) (normalized safety empty 4) false (cells safety empty 4)
      (taken safety empty 4).2.world (some growth) =
      .ok ((.ok (some .allocationFailure), TransferredPreparationFailureTests.closed clone), after) ∧
    CallerPreparationFailure 7 (normalized safety empty 4) (before safety empty 4)
      (TransferredPreparationFailureTests.failed safety empty clone) after := by
  obtain ⟨after, ran, post, _⟩ := TransferredPreparationFailureTests.native_contract safety empty clone
  have checked := initialized_entry safety empty false (TransferredPreparationFailureTests.actions clone) allocate (some growth)
  rw [show execution (TransferredPreparationFailureTests.actions clone) allocate safety 7 6 (parent empty) source
    Insertion.Tests.model input (key empty) (normalized safety empty 4) false (cells safety empty 4)
    (taken safety empty 4).2.world (some growth) = _ from ran] at checked
  exact ⟨after, checked, post⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.CapacityTests
