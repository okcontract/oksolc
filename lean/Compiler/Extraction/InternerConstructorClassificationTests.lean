/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeClassificationFailure
import Compiler.Extraction.InternerNativeCacheHitTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ClassificationTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open Publication.OriginTests (Case source request sorted)
open CacheTests (before constructed address stack prepared debug poison prefix_observed)

/-- Override only the classification observation to exercise ordinary and
rejected cleanup for every existing ownership case, including a temporary.
These overrides do not claim native query correspondence. -/
def queries (error : Interner.Error) : Caller.Queries :=
  { Interner.Queries.queries with deterministic := fun _ => .error error }
def actual (case : Case) (error : Interner.Error)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives (Publication.Effects Nat)) :=
  invoke (Publication.external Normalization.Tests.success) 160 11 p (queries error) (source case) (request case) debug (before case)

theorem initialized (case : Case) :
    Caller.initLookup (Publication.external Normalization.Tests.success) 160 11 (source case)
      ⟨(constructed case).memory.memory.nextId, 0, 2⟩ (request case)
      ⟨{ constructed case with memory := { (constructed case).memory with memory := stack case } }, { lookup := none }⟩ =
        (.ok (sorted case), (prepared case Normalization.Tests.success 160).2) := by
  have observed := prefix_observed case
  rw [observed.2.1]
  exact Prod.ext observed.2.2.2.1 rfl

theorem ordinary_contract (case : Case) (error : Interner.Error)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives (Publication.Effects Nat))
    (completed : ordinary (.error (.language error) : Except Fault NodeId) = true) :
    let ran := actual case error p
    ran.1 = .error (.language error) ∧ Good (source case) (request case).arguments ran.2.world ∧ Closed ran.2.scope ∧
      ran.2.world.graph = (before case).graph ∧
      (∀ id cell, (before case).memory.memory.heap.lookup id = some cell → ran.2.world.memory.memory.heap.lookup id = some cell) ∧
      (∀ id block, (before case).memory.heap id = some block → ran.2.world.memory.heap id = some block) ∧
      normalizeCode.run InsertionSort.sortIds (request case).item (request case).arguments = some (sorted case) := by
  dsimp only [actual]
  have observed := prefix_observed case
  exact invoke_classification_failed _ _ _ p _ _ _ _ _ _ _ _ _ _ _ error
    (Publication.OriginTests.initial_good case)
    (Publication.external_admitted _ (Normalization.Tests.external_admitted _))
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) AssemblyItem.Initializers.Tests.debug_valid
    observed.1 observed.2.2.2.2.1 observed.2.2.1 (initialized case) rfl completed

theorem rejected_contract (case : Case) (error : Interner.Error)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives (Publication.Effects Nat))
    (rejected : ordinary (.error (.language error) : Except Fault NodeId) = false) :
    actual case error p = (.error (.language error), (prepared case Normalization.Tests.success 160).2) :=
  invoke_classification_rejected _ _ _ p _ _ _ _ _ _ _ _ _ _ _ error
    (prefix_observed case).1 (prefix_observed case).2.2.2.2.1 (prefix_observed case).2.2.1 (initialized case) rfl rejected

theorem ordinary_observed (case : Case) :
    (actual case .assemblyException (fun _ _ => poison)).1 = .error (.language .assemblyException) ∧
    (actual case .assemblyException (fun _ _ => poison)).2.scope = ⟨none, none, false⟩ ∧
    (actual case .assemblyException (fun _ _ => poison)).2.world.memory.effects.allocator = (if case = .temporary then 120 else 5) ∧
    (actual case .assemblyException (fun _ _ => poison)).2.world.memory.memory.heap.lookup 3 = none ∧
    (actual case .assemblyException (fun _ _ => poison)).2.world.memory.memory.heap.lookup 4 = none ∧
    (actual case .assemblyException (fun _ _ => poison)).2.world.memory.memory.heap.lookup 5 = none ∧
    (actual case .assemblyException (fun _ _ => poison)).2.world.memory.heap 5 = none := by
  cases case <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl,
    by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem rejected_temporary :
    (actual .temporary .safetyFault (fun _ _ => poison)).1 = .error (.language .safetyFault) ∧
    (actual .temporary .safetyFault (fun _ _ => poison)).2.scope.lookup =
      some ⟨⟨5, 0, 3⟩, [1, 2, 3], some ⟨5, [1, 2, 3]⟩⟩ ∧
    (actual .temporary .safetyFault (fun _ _ => poison)).2.world.memory.effects.allocator = 17 ∧
    ((actual .temporary .safetyFault (fun _ _ => poison)).2.world.memory.memory.heap.lookup 3).isSome = true ∧
    ((actual .temporary .safetyFault (fun _ _ => poison)).2.world.memory.memory.heap.lookup 4).isSome = true ∧
    (actual .temporary .safetyFault (fun _ _ => poison)).2.world.memory.heap 5 = some ⟨11, .arguments [1, 2, 3]⟩ := by
  exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl,
    by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

/-- Actual query classification: assembly errors clean the locals; a malformed
non-operation optional opcode retains the initialized borrowed scope. -/
def nativeRequest (kind : Kind) (instruction : Option Opcode) : Interner.Request :=
  { request .temporary with item := ⟨kind, instruction, 0⟩ }
def native (kind : Kind) (instruction : Option Opcode) :=
  invoke (Publication.external Normalization.Tests.success) 160 11 (fun _ _ => poison) Interner.Queries.queries
    (source .temporary) (nativeRequest kind instruction) debug (before .temporary)

theorem native_observed :
    (native 13 none).1 = .error (.language .assemblyException) ∧
    (native 13 (some 1)).1 = .error (.language .assemblyException) ∧
    (native 13 none).2.scope.lookup = none ∧
    (native 13 none).2.world.memory.memory.heap.lookup 3 = none ∧
    (native 13 none).2.world.memory.memory.heap.lookup 4 = none ∧
    (native 2 (some 1)).1 = .error (.language .safetyFault) ∧
    (native 2 (some 1)).2.scope.lookup = some ⟨source .temporary, [3, 1, 2], none⟩ ∧
    ((native 2 (some 1)).2.world.memory.memory.heap.lookup 3).isSome = true ∧
    ((native 2 (some 1)).2.world.memory.memory.heap.lookup 4).isSome = true := by
  exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl,
    by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl,
    by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ClassificationTests
