/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerAllocationNativeWords
import Compiler.Extraction.StorageExecutionTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.AllocationWordTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open NativeRecursion Recursive
open Interner.ObservedTests (model caller callerHeap caller_valid)
open Interner.ObservedStorageTests (cell key binding denotation)

/-- Exercise the generalized graph proof on the existing callback-fault fixture,
including the publication failure whose pop callback rejects after value cleanup. -/
theorem fault_prefix_preserved (failure : Option Storage.Allocation) (attemptFault : Bool) (releaseFault : Option Release) :
    let state := (ExecutionTests.run true true failure attemptFault releaseFault).1.2
    let heap := Interner.InsertionExecution.project [caller] (fun _ => none) cell key state
    Interner.Invariant model heap ∧ Interner.Stable callerHeap heap := by
  have prefixed := insert_execution_prefix ⟨true, true, fun _ => false⟩
    (ExecutionTests.operations failure attemptFault releaseFault) []
  exact Interner.InsertionExecution.project_prefix_safe model [caller] (fun _ => none) cell key _
    (fun published => ⟨(prefixed published).1, by decide⟩) caller_valid binding denotation

/-- Rejected cleanup retains the appended word and old IDs, although the
ownership protocol is unfinished. Word safety must not invent a rollback. -/
theorem rejected_cleanup_retains_append :
    let state := (ExecutionTests.run true true (some .publish) false (some .pop)).1.2
    let heap := Interner.InsertionExecution.project [caller] (fun _ => none) cell key state
    heap.representatives = some [caller, cell] ∧ heap.read 0 = some 3 ∧
      heap.read 1 = some cell.value ∧ heap.table key = none := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The interpretation premises have a concrete witness, for arbitrary streams,
seeds, debug data and depth; no successful replay is assumed. -/
theorem closed_words (env : AddressMask.Environment) (other : Meaning) (usizeBits depth : Nat)
    (seed : Interner.Primitives) (stream : List Caller.ProtocolTrace.ProtocolEvent) (mismatch : Insertion.Native.Fault) :
    AllocationTrace.Words env (Interner.constructorMeaning other)
      (AllocationTrace.streamReplay stream (AllocationTrace.recursiveModels
        (Dispatch.wordDispatchMeaning env (Interner.constructorMeaning other)) usizeBits seed stream mismatch depth)) :=
  AllocationTrace.recursive_words env (Interner.constructorMeaning other) usizeBits seed stream mismatch
    (Associative.constructor_meaning_pushes other) (Insertion.Native.constructor_push_values other) depth

def wrongLiteral : Meaning where
  operation := fun _ _ _ => none
  atom := fun _ _ _ _ => some 0

theorem wrong_literal_rejected : ¬ Insertion.Native.PushValues wrongLiteral := by
  intro law
  have wrong := law 1 0 [] 0 rfl
  contradiction

theorem unrelated_key_rejected :
    ¬ AllocationTrace.RequestKey (Interner.constructorCode.constantRequest 1) ⟨2, 0, 0, [], 0⟩ := by
  intro made
  have values := congrArg (fun result => result.map Key.data) made
  have different : (1 : Word) ≠ 0 := by decide
  exact different (Option.some.inj values)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.AllocationWordTests
