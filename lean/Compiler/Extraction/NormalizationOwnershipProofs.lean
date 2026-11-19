/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.CacheProgram

namespace Compiler.Extraction.Cache.NormalizationOwnership
set_option linter.unusedSimpArgs false

/-- All lengths, commutativity decisions and independent allocation outcomes.
The source lifecycle ends with no leak, double free or scratch-buffer release;
a successfully transferred allocation remains owned by its caller. -/
theorem run_safe (commutative : Bool) (length bufferLength : Nat)
    (allocationSucceeds duplicateSucceeds : Bool) (exit : Exit) :
    Safe (normalizationOwnershipCode.run commutative length bufferLength
      allocationSucceeds duplicateSucceeds exit) := by
  by_cases small : length < 2
  · cases commutative <;> cases allocationSucceeds <;> cases duplicateSucceeds <;> cases exit <;>
      simp [normalizationOwnershipCode, Code.run, Code.runWith, Code.continueWith, Code.finishWith, Code.initWith, Code.takeWith, Code.deinitWith,
        State.move, Safe, Comparison.test, small]
  · by_cases fits : length ≤ bufferLength
    · have large : ¬bufferLength < length := by omega
      cases commutative <;> cases allocationSucceeds <;> cases duplicateSucceeds <;> cases exit <;>
        simp [normalizationOwnershipCode, Code.run, Code.runWith, Code.continueWith, Code.finishWith, Code.initWith, Code.takeWith, Code.deinitWith,
          State.move, Safe, Comparison.test, small, fits, large]
    · have large : bufferLength < length := by omega
      cases commutative <;> cases allocationSucceeds <;> cases duplicateSucceeds <;> cases exit <;>
        simp [normalizationOwnershipCode, Code.run, Code.runWith, Code.continueWith, Code.finishWith, Code.initWith, Code.takeWith, Code.deinitWith,
          State.move, Safe, Comparison.test, small, fits, large]

/-- Exact-fit normalization uses caller-local scratch and never marks it owned. -/
theorem exact_fit (length : Nat) (enough : 2 ≤ length) (succeeds : Bool) :
    normalizationOwnershipCode.init true length length succeeds =
      some { origin := .scratch } := by
  simp [normalizationOwnershipCode, Code.init, Code.initWith, Comparison.test, show ¬length < 2 by omega]

/-- Larger normalized slices allocate once. Taking ownership consumes no new
allocation and clears the lookup's ownership before its deferred cleanup. -/
theorem heap_transfer (length bufferLength : Nat) (enough : 2 ≤ length)
    (large : bufferLength < length) (duplicateSucceeds : Bool) :
    normalizationOwnershipCode.run true length bufferLength true duplicateSucceeds .transfer =
      (.transferred, { origin := .allocation, owner := .caller, dead := true }) := by
  have notFits : ¬length ≤ bufferLength := by omega
  simp [normalizationOwnershipCode, Code.run, Code.runWith, Code.continueWith, Code.finishWith, Code.initWith, Code.takeWith, Code.deinitWith, State.move,
    Comparison.test, show ¬length < 2 by omega, large, notFits]

/-- The source threshold is shared by value normalization and ownership. -/
theorem threshold_agrees : normalizationOwnershipCode.threshold = normalizeCode.threshold := rfl

end Compiler.Extraction.Cache.NormalizationOwnership
