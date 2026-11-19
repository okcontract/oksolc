/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeEntryFailure
import Compiler.Extraction.InternerNativeCacheHitTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.EntryFailureTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open Publication.OriginTests (Case source request)
open CacheTests (before constructed address stack prepared actual debug poison prefix_observed)

theorem failed_prefix : Caller.initLookup (Publication.external (Normalization.Tests.external (fun _ => true))) 160 11 (source .temporary)
      ⟨(constructed .temporary).memory.memory.nextId, 0, 2⟩ (request .temporary)
      ⟨{ constructed .temporary with memory := { (constructed .temporary).memory with memory := stack .temporary } }, { lookup := none }⟩ =
        (.error (.language .outOfMemory), (prepared .temporary (Normalization.Tests.external (fun _ => true)) 160).2) := by
  insertion_kernel_rfl

/-- Reuse the existing temporary-allocation OOM execution with arbitrary
callbacks. Its original native/registry frame comes from the general theorem. -/
theorem initialization_oom_contract
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives (Publication.Effects Nat)) :
    let ran := actual .temporary (Normalization.Tests.external (fun _ => true)) 160 p
    ran.1 = .error (.language .outOfMemory) ∧ Good (source .temporary) (request .temporary).arguments ran.2.world ∧
      Closed ran.2.scope ∧ ran.2.world.graph = (before .temporary).graph ∧
      (∀ id cell, (before .temporary).memory.memory.heap.lookup id = some cell → ran.2.world.memory.memory.heap.lookup id = some cell) ∧
      (∀ id block, (before .temporary).memory.heap id = some block → ran.2.world.memory.heap id = some block) := by
  dsimp only [actual]
  have observed := prefix_observed .temporary
  have checked := invoke_init_failed (Publication.external (Normalization.Tests.external (fun _ => true))) 160 11 p
    Interner.Queries.queries (source .temporary) (request .temporary) debug (before .temporary) (constructed .temporary)
    address _ (stack .temporary) (.language .outOfMemory) (prepared .temporary (Normalization.Tests.external (fun _ => true)) 160).2
    (Publication.OriginTests.initial_good .temporary)
    (Publication.external_admitted _ (Normalization.Tests.external_admitted _))
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) AssemblyItem.Initializers.Tests.debug_valid
    observed.1 observed.2.2.2.2.1 observed.2.2.1 failed_prefix rfl
  exact ⟨checked.1, checked.2.2⟩

theorem incomplete_route
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives (Publication.Effects Nat)) :
    actual .temporary Normalization.Tests.success 0 p =
      (.error (.memory (.preparation .incomplete)), (prepared .temporary Normalization.Tests.success 0).2) := by
  have observed := prefix_observed .temporary
  apply invoke_init_rejected _ _ _ p _ _ _ _ _ _ _ _ _ _ _ observed.1 observed.2.2.2.2.1 observed.2.2.1
  · insertion_kernel_rfl
  · rfl

/-- The query override tests the capacity control/cleanup branch, not a native
representation of a graph with 2^32-1 rows. Initializer callbacks cannot run. -/
def fullQueries : Caller.Queries := { Interner.Queries.queries with atCapacity := fun _ => true }
def full (case : Case)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives (Publication.Effects Nat)) :=
  invoke (Publication.external Normalization.Tests.success) 0 11 p fullQueries (source case) (request case) debug (before case)

theorem capacity_contract (case : Case)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives (Publication.Effects Nat)) :
    let ran := full case p
    ran.1 = .error (.language .capacity) ∧ Good (source case) (request case).arguments ran.2.world ∧ Closed ran.2.scope ∧
      ran.2.world.graph = (before case).graph ∧ ran.2.world.memory.effects = (before case).memory.effects ∧
      (∀ id cell, (before case).memory.memory.heap.lookup id = some cell → ran.2.world.memory.memory.heap.lookup id = some cell) ∧
      (∀ id block, (before case).memory.heap id = some block → ran.2.world.memory.heap id = some block) := by
  have checked := invoke_capacity_failed (Publication.external Normalization.Tests.success) 0 11 p fullQueries
    (source case) (request case) debug (before case) (constructed case) address
    (Publication.OriginTests.initial_good case)
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) AssemblyItem.Initializers.Tests.debug_valid
    (prefix_observed case).1 rfl
  exact ⟨congrArg Prod.fst checked.1, checked.2⟩

theorem capacity_observed (case : Case) :
    (full case (fun _ _ => poison)).1 = .error (.language .capacity) ∧
    (full case (fun _ _ => poison)).2.world.memory.effects.allocator = 5 ∧
    (full case (fun _ _ => poison)).2.world.memory.memory.nextId = 4 ∧
    (full case (fun _ _ => poison)).2.world.memory.memory.heap.lookup 3 = none ∧
    (full case (fun _ _ => poison)).2.world.memory.memory.heap.lookup 4 = none := by
  cases case <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

/-- The closest permitted item allocation leaves sixteen bytes, so the actual
eight-byte scratch allocation succeeds. Four words at that boundary reject. -/
def boundaryBefore := { before .temporary with memory := { (before .temporary).memory with memory :=
  { (before .temporary).memory.memory with nextAddress := Compiler.ZigAir.Memory.addressLimit - 240 } } }
def boundaryItem := prepare (request .temporary).item debug boundaryBefore

theorem boundary_observed : boundaryItem.1 = .ok address ∧
    boundaryItem.2.memory.memory.nextAddress = Compiler.ZigAir.Memory.addressLimit - 16 ∧
    (Compiler.ZigAir.Memory.allocate boundaryItem.2.memory.memory (.array 2 word)).isOk = true ∧
    Compiler.ZigAir.Memory.allocate boundaryItem.2.memory.memory (.array 4 word) = .error .outOfMemory := by
  exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem scratch_contract (case : Case) : ∃ memory,
    Compiler.ZigAir.Memory.allocate (constructed case).memory.memory (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨(constructed case).memory.memory.nextId, 0⟩, memory) :=
  prepare_scratch (request case).item debug (before case) (constructed case) address
    (Publication.OriginTests.initial_good case).1
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) AssemblyItem.Initializers.Tests.debug_valid
    (prefix_observed case).1

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.EntryFailureTests
