/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.NormalizationOwnershipProofs

namespace Compiler.Extraction.Cache.NormalizationOwnership.Tests

def borrowed := normalizationOwnershipCode.run false 9 2 false true .transfer
def scratch := normalizationOwnershipCode.run true 2 2 false true .transfer
def allocated := normalizationOwnershipCode.run true 3 2 true false .transfer
def hit := normalizationOwnershipCode.run true 3 2 true false .lookup
def cleaned := normalizationOwnershipCode.run true 3 2 true false .cleanup
def duplicateFailure := normalizationOwnershipCode.run true 2 2 false false .transfer
def allocationFailure := normalizationOwnershipCode.run true 3 2 false true .transfer

example : borrowed = (.transferred, { owner := .caller, dead := true }) := by rfl
example : scratch = (.transferred, { origin := .scratch, owner := .caller, dead := true }) := by rfl
example : allocated = (.transferred, { origin := .allocation, owner := .caller, dead := true }) := by rfl
example : hit = (.lookup, { origin := .allocation, owner := .released, owned := true, dead := true }) := by rfl
example : cleaned = (.cleaned, { origin := .allocation, owner := .released, dead := true }) := by rfl
example : duplicateFailure = (.allocationFailure, { origin := .scratch, dead := true }) := by rfl
example : allocationFailure = (.allocationFailure, { dead := true }) := by rfl
example : normalizationOwnershipCode.run false 9 2 true false .transfer =
    (.allocationFailure, { dead := true }) := by rfl
example : normalizationOwnershipCode.run true 1 0 false true .transfer =
    (.transferred, { owner := .caller, dead := true }) := by rfl
example : normalizationOwnershipCode.run true 0 0 false true .cleanup =
    (.cleaned, { owner := .released, dead := true }) := by rfl
example : normalizationOwnershipCode.run false 9 2 false false .lookup =
    (.lookup, { dead := true }) := by rfl

-- These deliberately broken programs are modeled as ownership violations or
-- leaks, never as native allocator errors that could vacuously prove safety.
def noClear := { normalizationOwnershipCode with clearOnTake := false }.run true 3 2 true false .transfer
def noFree := { normalizationOwnershipCode with freeOnDeinit := false }.run true 3 2 true false .lookup
def ownScratch := { normalizationOwnershipCode with ownTemporary := .ge }.run true 2 2 true true .lookup
def outOfBounds := { normalizationOwnershipCode with useScratch := .ge }.run true 3 2 true true .lookup
example : noClear.2.invalid = true := by rfl
example : noFree.2.owner = .lookup := by rfl
example : ownScratch.2.invalid = true := by rfl
example : outOfBounds.2.invalid = true := by rfl
example : ¬Safe noClear := by unfold Safe; decide
example : ¬Safe noFree := by unfold Safe; decide
example : ¬Safe ownScratch := by unfold Safe; decide
example : ¬Safe outOfBounds := by unfold Safe; decide

theorem failure_order : allocationFailure.1 = .allocationFailure ∧ duplicateFailure.1 = .allocationFailure := by
  exact ⟨rfl, rfl⟩
theorem no_reallocation : allocated.1 = .transferred ∧ allocated.2.owner = .caller := by exact ⟨rfl, rfl⟩

end Compiler.Extraction.Cache.NormalizationOwnership.Tests
