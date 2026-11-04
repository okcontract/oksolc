/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeTakeFailure
import Compiler.Extraction.InternerConstructorClassificationTests
import Compiler.Extraction.InternerConstructorEntryFailureTests
import Compiler.Extraction.InternerNativeLocalTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.TakeFailureTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open Publication.OriginTests (Case source request key sorted)
open CacheTests (debug address stack poison)

/-- Reuse the normalization corpus; only duplication is denied. The true
branch uses the actual queries with an empty cache. The false branch overrides
classification to check that a populated cache is bypassed before failed take.
The corpus's physical argument-shape cases do not claim opcode word semantics. -/
def host := Normalization.Tests.external (fun site => match site with | .duplicate => true | _ => false)
def queries (deterministic : Bool) : Caller.Queries :=
  if deterministic then Interner.Queries.queries
  else { Interner.Queries.queries with deterministic := fun _ => .ok false }
def before (case : Case) (deterministic : Bool) : World (Publication.Effects Nat) :=
  if deterministic then { CacheTests.before case with graph := { (CacheTests.before case).graph with table := fun _ => none } }
  else CacheTests.before case
def constructed (case : Case) (deterministic : Bool) := (prepare (request case).item debug (before case deterministic)).2
def prepared (case : Case) (deterministic : Bool) :=
  Caller.initLookup (Publication.external host) 160 11 (source case)
    ⟨(constructed case deterministic).memory.memory.nextId, 0, 2⟩ (request case)
    ⟨{ constructed case deterministic with memory := { (constructed case deterministic).memory with memory := stack case } }, { lookup := none }⟩
def taken (case : Case) (deterministic : Bool) := take (Publication.external host) 11 (prepared case deterministic).2
def actual (case : Case) (deterministic : Bool)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives (Publication.Effects Nat)) :=
  invoke (Publication.external host) 160 11 p (queries deterministic) (source case) (request case) debug (before case deterministic)

theorem prefix_observed (case : Case) (deterministic : Bool) :
    prepare (request case).item debug (before case deterministic) = (.ok address, constructed case deterministic) ∧
    Compiler.ZigAir.Memory.allocate (constructed case deterministic).memory.memory (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨4, 0⟩, stack case) ∧
    (prepared case deterministic).1 = .ok (sorted case) ∧
    (queries deterministic).atCapacity (constructed case deterministic).graph = false ∧
    (queries deterministic).deterministic (request case).item = .ok deterministic ∧
    Interner.makeKey (request case) (sorted case) = .ok (key case) := by
  cases case <;> cases deterministic <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl,
    by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem missed (case : Case) (deterministic : Bool) (selected : deterministic = true) :
    (constructed case deterministic).graph.table (key case) = none := by
  subst deterministic
  cases case <;> insertion_kernel_rfl

/-- The scratch initializer has already advanced its native allocation counter
to six. Failed duplication preserves that reached counter as well as the heap. -/
theorem failed_observed (case : Case) (deterministic : Bool)
    (borrowed : case = .scratch ∨ case = .offsetBorrow ∨ case = .replacement) :
    (taken case deterministic).1 = .error (.language .outOfMemory) ∧
    (taken case deterministic).2.world.memory.effects.allocator = 5 + (sorted case).length * 4 ∧
    (prepared case deterministic).2.world.memory.memory.nextId = (if case = .scratch then 6 else 5) ∧
    (taken case deterministic).2.world.memory.memory.nextId = (prepared case deterministic).2.world.memory.memory.nextId := by
  rcases borrowed with rfl | rfl | rfl <;> cases deterministic <;>
    exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem failed_contract (case : Case) (deterministic : Bool)
    (borrowed : case = .scratch ∨ case = .offsetBorrow ∨ case = .replacement)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives (Publication.Effects Nat)) :
    let ran := actual case deterministic p
    ran.1 = .error (.language .outOfMemory) ∧
      ran.2.world = returnWorld (before case deterministic).memory.memory.nextId
        (constructed case deterministic).memory.memory.nextId (taken case deterministic).2.world ∧
      Good (source case) (request case).arguments ran.2.world ∧ Closed ran.2.scope ∧
      ran.2.world.graph = (before case deterministic).graph ∧
      (∀ id cell, (before case deterministic).memory.memory.heap.lookup id = some cell → ran.2.world.memory.memory.heap.lookup id = some cell) ∧
      (∀ id block, (before case deterministic).memory.heap id = some block → ran.2.world.memory.heap id = some block) ∧
      normalizeCode.run InsertionSort.sortIds (request case).item (request case).arguments = some (sorted case) := by
  dsimp only [actual]
  have observed := prefix_observed case deterministic
  have checked := invoke_take_failed (Publication.external host) 160 11 p (queries deterministic) (source case) (request case) debug
    (before case deterministic) (constructed case deterministic) address _ (stack case) (sorted case)
    (prepared case deterministic).2 (taken case deterministic).2 (.language .outOfMemory) (key case) deterministic
    (by cases deterministic <;> exact Publication.OriginTests.initial_good case)
    (Publication.external_admitted _ (Normalization.Tests.external_admitted _))
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) AssemblyItem.Initializers.Tests.debug_valid
    observed.1 observed.2.2.2.1 observed.2.1 (Prod.ext observed.2.2.1 rfl) observed.2.2.2.2.1 observed.2.2.2.2.2
    (missed case deterministic) (Prod.ext (failed_observed case deterministic borrowed).1 rfl)
  exact checked.2

theorem cleanup_observed (case : Case) (deterministic : Bool)
    (borrowed : case = .scratch ∨ case = .offsetBorrow ∨ case = .replacement) :
    (actual case deterministic (fun _ _ => poison)).1 = .error (.language .outOfMemory) ∧
    (actual case deterministic (fun _ _ => poison)).2.scope = ⟨none, none, false⟩ ∧
    (actual case deterministic (fun _ _ => poison)).2.world.memory.effects.allocator = 5 + (sorted case).length * 4 ∧
    (actual case deterministic (fun _ _ => poison)).2.world.memory.memory.nextId = (if case = .scratch then 6 else 5) ∧
    (actual case deterministic (fun _ _ => poison)).2.world.memory.memory.heap.lookup 3 = none ∧
    (actual case deterministic (fun _ _ => poison)).2.world.memory.memory.heap.lookup 4 = none ∧
    (actual case deterministic (fun _ _ => poison)).2.world.memory.memory.heap.lookup 5 = none := by
  rcases borrowed with rfl | rfl | rfl <;> cases deterministic <;>
    exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl,
      by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

/-- An owned temporary transfers without a duplication call; an empty borrow
also needs no backing allocation. Neither acquires a spurious OOM outcome. -/
theorem allocation_boundaries (deterministic : Bool) :
    (taken .temporary deterministic).1 = .ok () ∧
    (taken .temporary deterministic).2.world.memory.effects.allocator = 17 ∧
    (taken .temporary deterministic).2.scope.slice = some ⟨5, [1, 2, 3]⟩ ∧
    (taken .empty deterministic).1 = .ok () ∧
    (taken .empty deterministic).2.world.memory.effects.allocator = 5 ∧
    (taken .emptyAlias deterministic).1 = .ok () ∧
    (taken .emptyAlias deterministic).2.world.memory.effects.allocator = 5 := by
  cases deterministic <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl,
    by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.TakeFailureTests
