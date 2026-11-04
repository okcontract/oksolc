/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeCacheHit
import Compiler.Extraction.InternerCallerOriginTests
import Compiler.Extraction.AssemblyItemInitializationTests
import Compiler.Extraction.InsertionKernelTestSupport
namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.CacheTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open Publication.OriginTests (Case source request key sorted)

/-- Reuse the native normalization corpus. The three-element case tests the
physical lookup/cleanup contract only; it does not claim opcode word semantics. -/
def before (case : Case) : World (Publication.Effects Nat) :=
  { Publication.OriginTests.before case with graph :=
    { (Publication.OriginTests.before case).graph with table := fun query => if query == key case then some 17 else none } }
abbrev debug := AssemblyItem.Initializers.Tests.debug
def constructed (case : Case) := (prepare (request case).item debug (before case)).2
def address : Compiler.ZigAir.Memory.Address := ⟨3, 0⟩
def stack (case : Case) :=
  ((Compiler.ZigAir.Memory.allocate (constructed case).memory.memory (.array 2 word)).toOption.map Prod.snd).getD
    (constructed case).memory.memory
def prepared (case : Case) (host : External Nat) (budget : Nat) :=
  Caller.initLookup (Publication.external host) budget 11 (source case) ⟨4, 0, 2⟩ (request case)
    ⟨{ constructed case with memory := { (constructed case).memory with memory := stack case } }, { lookup := none }⟩
def actual (case : Case) (host : External Nat) (budget : Nat)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives (Publication.Effects Nat)) :=
  invoke (Publication.external host) budget 11 p Interner.Queries.queries (source case) (request case) debug (before case)

theorem prefix_observed (case : Case) :
    prepare (request case).item debug (before case) = (.ok address, constructed case) ∧
    (constructed case).memory.memory.nextId = 4 ∧
    Compiler.ZigAir.Memory.allocate (constructed case).memory.memory (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨4, 0⟩, stack case) ∧
    (prepared case Normalization.Tests.success 160).1 = .ok (sorted case) ∧
    Interner.Queries.queries.atCapacity (constructed case).graph = false ∧
    Interner.Queries.queries.deterministic (request case).item = .ok true ∧
    Interner.makeKey (request case) (sorted case) = .ok (key case) ∧
    (constructed case).graph.table (key case) = some 17 := by
  cases case <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem completed (case : Case)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives (Publication.Effects Nat)) :
    let ran := actual case Normalization.Tests.success 160 p
    ran.1 = .ok 17 ∧ Good (source case) (request case).arguments ran.2.world ∧ Closed ran.2.scope ∧
      ran.2.world.graph = (before case).graph ∧
      (∀ id cell, (before case).memory.memory.heap.lookup id = some cell → ran.2.world.memory.memory.heap.lookup id = some cell) ∧
      (∀ id block, (before case).memory.heap id = some block → ran.2.world.memory.heap id = some block) ∧
      normalizeCode.run InsertionSort.sortIds (request case).item (request case).arguments = some (sorted case) := by
  have observed := prefix_observed case
  have initialized : Caller.initLookup (Publication.external Normalization.Tests.success) 160 11 (source case)
      ⟨(constructed case).memory.memory.nextId, 0, 2⟩ (request case)
      ⟨{ constructed case with memory := { (constructed case).memory with memory := stack case } }, { lookup := none }⟩ =
        (.ok (sorted case), (prepared case Normalization.Tests.success 160).2) := by
    rw [observed.2.1]; exact Prod.ext observed.2.2.2.1 rfl
  exact invoke_cached_verified _ _ _ p _ _ _ _ _ _ _ _ _ _ _ _ _
    (Publication.OriginTests.initial_good case)
    (Publication.external_admitted _ (Normalization.Tests.external_admitted _))
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) AssemblyItem.Initializers.Tests.debug_valid
    observed.1 observed.2.2.2.2.1 observed.2.2.1 initialized observed.2.2.2.2.2.1 observed.2.2.2.2.2.2.1 observed.2.2.2.2.2.2.2

/-- A reached callback would reject; cache-hit completion is independent of it. -/
def poison : Primitives (Publication.Effects Nat) where
  simplify := fun _ _ before => (.error .outsideOwnedContinuation, before)
  publish := fun _ _ _ before => (.error .outsideOwnedContinuation, before)
  insert := fun _ _ _ before => (.error .outsideOwnedContinuation, before)

def observed (case : Case) := actual case Normalization.Tests.success 160 (fun _ _ => poison)

theorem cleanup_observed (case : Case) :
    (observed case).1 = .ok 17 ∧ (observed case).2.scope = ⟨none, none, false⟩ ∧
    (observed case).2.world.memory.effects.allocator = (if case = .temporary then 120 else 5) ∧
    (observed case).2.world.memory.memory.heap.lookup 3 = none ∧
    (observed case).2.world.memory.memory.heap.lookup 4 = none ∧
    (observed case).2.world.memory.memory.heap.lookup 5 = none ∧
    (observed case).2.world.memory.heap 5 = none := by
  cases case <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem owned_temporary :
    (prepared .temporary Normalization.Tests.success 160).2.scope.lookup =
      some ⟨⟨5, 0, 3⟩, [1, 2, 3], some ⟨5, [1, 2, 3]⟩⟩ ∧
    (prepared .temporary Normalization.Tests.success 160).2.world.memory.effects.allocator = 17 ∧
    (observed .temporary).2.world.memory.effects.allocator = 120 := by
  exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

def oom := actual .temporary (Normalization.Tests.external (fun _ => true)) 160 (fun _ _ => poison)
def suspended := actual .temporary Normalization.Tests.success 0 (fun _ _ => poison)

theorem initialization_oom :
    oom.1 = .error (.language .outOfMemory) ∧ oom.2.scope = ⟨none, none, false⟩ ∧
    oom.2.world.memory.effects.allocator = 17 ∧
    oom.2.world.memory.memory.heap.lookup 3 = none ∧ oom.2.world.memory.memory.heap.lookup 4 = none := by
  exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem incomplete_retained :
    suspended.1 = .error (.memory (.preparation .incomplete)) ∧ ordinary suspended.1 = false ∧
    suspended.2.world.memory.effects.allocator = 17 ∧
    (suspended.2.world.memory.memory.heap.lookup 3).isSome = true ∧
    (suspended.2.world.memory.memory.heap.lookup 4).isSome = true ∧
    suspended.2.world.memory.heap 5 = some ⟨11, .arguments [3, 1, 2]⟩ := by
  exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.CacheTests
