/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.NormalizationEffects

namespace Compiler.Extraction.Cache.NormalizationOwnership.EffectTests

inductive Event where
  | allocate (site : Allocation)
  | release (origin : Origin) (owner : Owner) (owned dead : Bool)
  deriving DecidableEq, Repr
structure Trace where
  attempts : Nat := 0
  frees : Nat := 0
  events : List Event := []
  deriving DecidableEq, Repr

-- Controlled allocator witnesses. Empty duplicates/free calls have no allocator
-- effect; their primitive invocation is still recorded. These are fixtures,
-- not a proof of the native allocator implementation or address freshness.
def primitives (length failAt : Nat) : Primitives Trace where
  allocate := fun site before =>
    let skipped := site = .duplicate ∧ length = 0
    (if skipped then true else before.attempts != failAt, {
      before with
      attempts := if skipped then before.attempts else before.attempts + 1,
      events := before.events ++ [.allocate site] })
  release := fun state before => {
    before with
    frees := before.frees + (if length = 0 then 0 else 1),
    events := before.events ++ [.release state.origin state.owner state.owned state.dead]
  }

def run (commutative : Bool) (length bufferLength failAt : Nat) (exit : Exit) (before : Trace := {}) :=
  normalizationOwnershipCode.runWith commutative length bufferLength (primitives length failAt) exit before
theorem safe (commutative : Bool) (length bufferLength failAt : Nat) (exit : Exit) (before : Trace) :
    Safe (run commutative length bufferLength failAt exit before).1 := run_with_safe _ _ _ _ _ _

def allocated := run true 3 2 1 .transfer
def repeated := run true 3 2 1 .transfer allocated.2
def hit := run true 3 2 1 .lookup
def cleaned := run true 3 2 1 .cleanup
def scratch := run true 2 2 1 .cleanup
def borrowed := run false 9 2 1 .transfer
def duplicateFailure := run true 2 2 0 .transfer
def allocationFailure := run true 3 2 0 .transfer
def empty := run true 0 2 0 .cleanup

theorem temporary_transfer : allocated =
    ((.transferred, { origin := .allocation, owner := .caller, dead := true }),
      ⟨1, 0, [.allocate .temporary]⟩) := rfl
theorem repeated_failure : repeated =
    ((.allocationFailure, { dead := true }), ⟨2, 0, [.allocate .temporary, .allocate .temporary]⟩) := rfl
theorem lookup_cleanup : hit =
    ((.lookup, { origin := .allocation, owner := .released, owned := true, dead := true }),
      ⟨1, 1, [.allocate .temporary, .release .allocation .lookup true false]⟩) := rfl
theorem caller_cleanup : cleaned =
    ((.cleaned, { origin := .allocation, owner := .released, dead := true }),
      ⟨1, 1, [.allocate .temporary, .release .allocation .caller false false]⟩) := rfl
theorem scratch_cleanup : scratch =
    ((.cleaned, { origin := .scratch, owner := .released, dead := true }),
      ⟨1, 1, [.allocate .duplicate, .release .scratch .caller false false]⟩) := rfl

example : borrowed.2.events = [.allocate .duplicate] := by rfl
example : duplicateFailure.1 = (.allocationFailure, { origin := .scratch, dead := true }) := by rfl
example : duplicateFailure.2 = ⟨1, 0, [.allocate .duplicate]⟩ := by rfl
example : allocationFailure.2 = ⟨1, 0, [.allocate .temporary]⟩ := by rfl
example : (run false 9 2 0 .lookup).2 = ({} : Trace) := by rfl
example : empty.1.1 = .cleaned := by rfl
example : empty.2 = ⟨0, 0, [.allocate .duplicate, .release .input .caller false false]⟩ := by rfl

def initialized := normalizationOwnershipCode.initWith true 3 2 ((primitives 3 1).allocate .temporary) ({} : Trace)
def live : State := { origin := .allocation, owner := .lookup, owned := true }
theorem live_ready : Ready live :=
  init_with_ready true 3 2 ((primitives 3 1).allocate .temporary) ({} : Trace) initialized.2 live rfl
def transferred := normalizationOwnershipCode.takeWith ((primitives 3 1).allocate .duplicate) live initialized.2
theorem transferred_taken : Taken transferred.1.2 :=
  take_with_success ((primitives 3 1).allocate .duplicate) initialized.2 transferred.2 live transferred.1.2 live_ready rfl
example : transferred.2 = initialized.2 := by rfl
example : normalizationOwnershipCode.deinitWith (primitives 3 1).release transferred.1.2 transferred.2 =
    ({ transferred.1.2 with dead := true }, transferred.2) := deinit_with_taken _ _ _ transferred_taken

-- This witness makes a later allocation depend on retained release effects.
-- Its admission policy is test data, not a model of a particular allocator.
def releaseDependent : Primitives Trace := {
  primitives 3 99 with
  allocate := fun site before => (before.attempts == 0 || before.frees > 0, {
    before with
    attempts := before.attempts + 1, events := before.events ++ [.allocate site] })
}
def released := normalizationOwnershipCode.runWith true 3 2 releaseDependent .lookup ({} : Trace)
def reused := normalizationOwnershipCode.runWith true 3 2 releaseDependent .transfer released.2
theorem reuse_after_release : reused.1.1 = .transferred ∧ reused.2.attempts = 2 ∧ reused.2.frees = 1 :=
  ⟨rfl, rfl, rfl⟩

-- Corrupt ownership flags remain violations, not fabricated allocation errors.
def doubleFree := { normalizationOwnershipCode with clearOnTake := false }.runWith true 3 2
  (primitives 3 1) .cleanup ({} : Trace)
def leaked := { normalizationOwnershipCode with freeOnDeinit := false }.runWith true 3 2
  (primitives 3 1) .lookup ({} : Trace)
example : doubleFree.1.2.invalid = true := by rfl
example : doubleFree.2.frees = 2 := by rfl
example : leaked.1.2.owner = .lookup := by rfl
example : leaked.2.frees = 0 := by rfl

end Compiler.Extraction.Cache.NormalizationOwnership.EffectTests
