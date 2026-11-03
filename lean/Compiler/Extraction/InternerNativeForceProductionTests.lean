/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeForceProduction
import Compiler.Extraction.InternerBorrowedQueryTests
import Compiler.Extraction.InternerTerminalTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ForceTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion.CallerTests (source request original world buffer)
open Insertion.Tests (ops)

abbrev env := Compiler.Extraction.Recursive.Tests.env
abbrev other := Compiler.Extraction.Recursive.Tests.base
def meaning := Dispatch.wordDispatchMeaning env other
def debug := AssemblyItem.Initializers.Tests.debug
def base (failure : Option Storage.Allocation) : PairInput.Context (Publication.Effects Nat) :=
  ⟨Publication.external (ops failure).arguments, 160, 7, fun _ _ _ => Terminal.Tests.poison, Interner.Queries.queries⟩
def allocate : Backing.Registry.Allocate Nat := fun _ _ _ effects => (none, effects)
def nativeBase (failure : Option Storage.Allocation) := callerContext (ops failure) allocate false 3 meaning (base failure) none
def actual (failure : Option Storage.Allocation) (depth : Nat) :=
  (context (nativeBase failure) 3 64 (unfold (nativeBase failure) 3 64 depth) debug).primitives
    source ⟨0, 0⟩ (ConstructorItem.input request.item debug)
def body (failure : Option Storage.Allocation) (depth : Nat) :=
  Caller.forceBody (Publication.external (ops failure).arguments) 160 7 (actual failure depth)
    Interner.Queries.queries source buffer 4 request.item request.arguments
def forced (failure : Option Storage.Allocation) (depth : Nat) :=
  Caller.invoke (Publication.external (ops failure).arguments) 7 (body failure depth) world

theorem graph_valid : Interner.Invariant meaning original.graph := by
  refine ⟨(by intro _ _ impossible; cases impossible), rfl, ?_⟩
  simp [Storage.Coherent, Insertion.CallerTests.cells, Insertion.Tests.push, Cache.Item.eval,
    Cache.readArguments, meaning, Storage.Cell.value,
    Storage.Cell.isPush, Storage.Cell.dataValue]
  decide

theorem force_contract (failure : Option Storage.Allocation) (depth : Nat) :
    Semantic.Verified (Publication.external (ops failure).arguments) 7 source request.arguments meaning
      (body failure depth) world (fun _ _ => True) :=
  production_force_verified (ops failure) allocate false 3 64 env other (base failure) none debug depth
    source ⟨0, 0⟩ (ConstructorItem.input request.item debug) request.item request.arguments 4 original
    Normalization.Tests.before.memory _ 42 Insertion.CallerTests.original_good Normalization.Tests.actual_caller_allocation
    (Insertion.Tests.admitted failure) graph_valid (by rfl') (by rfl')

attribute [local irreducible] Caller.forceBody

/-- Retain the existing complete success/failure observations, including their
allocator effects and cleanup. Native depth does not add a force callback. -/
theorem matches_terminal (failure : Option Storage.Allocation) (depth : Nat) :
    forced failure depth = Terminal.Tests.forced failure := by
  have same := Caller.forceBody_publish_congr (Publication.external (ops failure).arguments) 160 7
    (actual failure depth) (Terminal.Tests.actual source failure) Interner.Queries.queries source buffer
    4 request.item request.arguments rfl
  have unwrapped : Terminal.Tests.forced failure =
      Caller.invoke (Publication.external (ops failure).arguments) 7
        (Caller.forceBody (Publication.external (ops failure).arguments) 160 7 (Terminal.Tests.actual source failure)
          Interner.Queries.queries source buffer 4 request.item request.arguments) world := by
    simp only [Terminal.Tests.forced, Terminal.Tests.forceBody, Caller.invoke, Query.forceBody,
      Interner.Queries.admit, show world.graph.representatives.isSome = true from rfl, if_true]
  exact (congrArg (fun action => Caller.invoke (Publication.external (ops failure).arguments) 7 action world) same).trans unwrapped.symm

theorem success (depth : Nat) : (forced none depth).1 = .ok () ∧
    (forced none depth).2.world.graph.table ⟨1, 1, 0, [1, 3], 0⟩ = some 4 ∧
    (forced none depth).2.world.memory.effects.allocator = 18 ∧ Closed (forced none depth).2.scope := by
  rw [matches_terminal]
  exact Terminal.Tests.force_publishes_without_recursion

theorem publication_failure (depth : Nat) : (forced (some .publish) depth).1 = .error (.language .outOfMemory) ∧
    (forced (some .publish) depth).2.world.memory.effects.allocator = 184 ∧
    (forced (some .publish) depth).2.world.memory.heap 5 = none ∧ Closed (forced (some .publish) depth).2.scope := by
  rw [matches_terminal]
  exact Terminal.Tests.force_failure_cleanup

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ForceTests
