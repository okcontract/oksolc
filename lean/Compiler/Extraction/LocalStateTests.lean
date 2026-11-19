/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.LocalState
import Compiler.Extraction.ObservedHeapTests

namespace Compiler.Extraction.Interner.LocalTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Recursive Contract.Yul
open Recursive.Tests (model env base pushes reads reads_sound initial request)

/-- A controlled stream for local callback witnesses: the first non-empty
transfer succeeds, subsequent ones fail. Other allocation sites use the already
proved fixture primitives. This does not claim native allocator event coverage. -/
def attempt : Local Unit := fun cursor =>
  (if cursor = 0 then .ok () else .error .outOfMemory, cursor + 1)
def transfer (ids : List NodeId) : Local Unit :=
  if ids.isEmpty then Local.fromExcept (.ok ()) else attempt
def primitives : Primitives := { Recursive.Tests.primitives with takeOwned := transfer }

theorem contracts : PrimitiveContracts model primitives :=
  ⟨Recursive.Tests.primitive_contracts.normalize, Recursive.Tests.primitive_contracts.insert,
    Recursive.Tests.primitive_contracts.publish⟩
theorem all_depths (depth : Nat) : FindSound model (unfold primitives reads 64 depth) :=
  unfold_safe env base pushes primitives contracts reads (fun heap _ => reads_sound heap) 64 depth

def first := unfold primitives reads 64 2 request initial
def secondRequest := { request with sequence := 78 }
def second := unfold primitives reads 64 2 secondRequest first.2
def cached := unfold primitives reads 64 1 request first.2

theorem first_preserved : Invariant model first.2 ∧ Stable initial first.2 ∧ first.2.read 7 = some 42 :=
  all_depths 2 request initial 42 ⟨(by intro key id found; cases found), trivial⟩ rfl (.ok 7) first.2 rfl

theorem second_preserved : Invariant model second.2 ∧ Stable first.2 second.2 := by
  have checked := all_depths 2 secondRequest first.2 42 first_preserved.1 rfl (.error .outOfMemory) second.2 rfl
  exact ⟨checked.1, checked.2.1⟩

example : first.1 = .ok 7 := by rfl
example : first.2.allocationCursor = 1 := by rfl
example : second.1 = .error .outOfMemory := by rfl
example : second.2.allocationCursor = 2 := by rfl
example : second.2.read = first.2.read := by rfl
example : second.2.table = first.2.table := by rfl
example : second.2.table ⟨1, 1, 0, [0, 1], 78⟩ = none := by rfl
example : second.2.table ⟨1, 1, 0, [0, 1], 77⟩ = some 7 := by rfl
example : cached = (.ok 7, first.2) := by rfl
example : transfer [] 1 = (.ok (), 1) := by rfl

-- The very same transfer input has different results at successive cursors;
-- a state-independent Except callback cannot represent this execution.
theorem transfer_success : transfer [0, 1] 0 = (.ok (), 1) := rfl
theorem transfer_failure : transfer [0, 1] 1 = (.error .outOfMemory, 2) := rfl
theorem no_stateless_transfer : ¬∃ result : Except Error Unit,
    (transfer [0, 1] 0).1 = result ∧ (transfer [0, 1] 1).1 = result := by
  rintro ⟨result, first, second⟩
  have impossible : (Except.ok () : Except Error Unit) = .error .outOfMemory := first.trans second.symm
  cases impossible

-- An allocating-normalization callback witnesses the source's error ordering:
-- normalization precedes the cache lookup. Its allocation policy is explicit
-- test data; native scratch/owned-buffer branch refinement remains separate.
def allocatingNormalize (request : Request) : Local (List NodeId) := do
  let _ ← attempt
  return request.arguments
def normalizationFailure := unfold { primitives with normalize := allocatingNormalize } reads 64 1 request first.2
example : normalizationFailure.1 = .error .outOfMemory := by rfl
example : normalizationFailure.2.allocationCursor = 2 := by rfl
example : normalizationFailure.2.table = first.2.table := by rfl
def capacityFirst := unfold { primitives with
  atCapacity := fun _ => true, normalize := allocatingNormalize } reads 64 1 request first.2
example : capacityFirst.1 = .error .capacity := by rfl
example : capacityFirst.2.allocationCursor = 1 := by rfl

def forceFailure := forceCode.run primitives (fun _ _ => .ok ()) 7 request.item request.arguments first.2
theorem force_preserved : Safe model
    (forceCode.run primitives (fun _ _ => .ok ()) 7 request.item request.arguments) first.2 (fun _ _ => True) :=
  force_safe model primitives contracts.normalize contracts.publish (fun _ _ => .ok ())
    7 request.item request.arguments first.2 42 first_preserved.1 rfl rfl
example : forceFailure.1 = .error .outOfMemory := by rfl
example : forceFailure.2.allocationCursor = 2 := by rfl
example : forceFailure.2.table ⟨1, 1, 0, [0, 1], 0⟩ = none := by rfl
def validationFailure := forceCode.run { primitives with normalize := allocatingNormalize }
  (fun _ _ => .error .invalidId) 7 request.item request.arguments first.2
example : validationFailure.1 = .error .invalidId := by rfl
example : validationFailure.2.allocationCursor = 1 := by rfl

def represented := { ObservedTests.callerHeap with allocationCursor := 5 }
example : (liftLocal attempt represented).2.representatives = some [ObservedTests.caller] := by rfl
example : (liftLocal attempt represented).2.allocationCursor = 6 := by rfl
example : (representativeReads (liftLocal attempt represented).2).operation 0 0x33 = .ok (some ⟨0, []⟩) := by rfl

def inserted := observedInsert ObservedTests.constant ⟨2, 0, 3, [], 0⟩ true (fun _ => true) represented
theorem represented_insert_safe : Safe model
    (observedInsert ObservedTests.constant ⟨2, 0, 3, [], 0⟩ true (fun _ => true)) represented
    (fun id after => after.read id = some 3) :=
  observed_insert_safe model _ _ _ _ represented (ObservedTests.caller_valid.with_cursor 5) rfl rfl
example : inserted.1 = .ok 1 := by rfl
example : inserted.2.allocationCursor = 5 := by rfl
example : inserted.2.representatives = some [ObservedTests.caller, ObservedTests.constant] := by rfl

def twoAttempts := (liftLocal attempt >>= fun _ => liftLocal attempt) ObservedTests.callerHeap
example : twoAttempts.1 = .error .outOfMemory := by rfl
example : twoAttempts.2.allocationCursor = 2 := by rfl
example : twoAttempts.2.representatives = some [ObservedTests.caller] := by rfl

end Compiler.Extraction.Interner.LocalTests
