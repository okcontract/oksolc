/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerCacheStream
import Compiler.Extraction.InternerNativeCacheHitTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.CacheStream.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray ResourceAdapter Interner.InvocationTrace
open ConstructorItem
open Publication.OriginTests (Case source request key sorted)

abbrev host := Publication.external Normalization.Tests.success
abbrev commutes (case : Case) := decide (case ≠ .offsetBorrow)
def start (case : Case) :=
  { CacheTests.constructed case with memory := { (CacheTests.constructed case).memory with memory := CacheTests.stack case } }
def initialization (case : Case) := Initialization.capture host 160 11 (commutes case) (source case)
  ⟨(CacheTests.constructed case).memory.memory.nextId, 0, 2⟩ (request case).arguments (start case).memory
def lookup : Case → NormalizationOwnership.State
  | .temporary => { origin := .allocation, owned := true, owner := .lookup }
  | .scratch => { origin := .scratch }
  | _ => {}
def close (case : Case) := Close.capture host 11 (lookup case) .lookup (initialization case).2.effects.handle
  (CacheTests.prepared case Normalization.Tests.success 160).2

def model : Interner.Primitives where
  atCapacity := Interner.Queries.queries.atCapacity
  deterministic := Interner.Queries.queries.deterministic
  normalize := fun _ before => (.error .unsupported, before)
  takeOwned := fun _ before => (.error .unsupported, before)
  simplify := fun _ before => (.error .unsupported, before)
  insert := fun _ _ before => (.error .unsupported, before)
  publish := fun _ _ before => (.error .unsupported, before)

def events (case : Case) (leading trailing : List (Event Failure Insertion.Native.Fault)) :=
  leading ++ (initialization case).2.events.map Event.normalization ++ (close case).2.events.map Event.normalization ++ trailing

def actual (case : Case) := Caller.find host 160 11 CacheTests.poison Interner.Queries.queries (source case)
  ⟨(CacheTests.constructed case).memory.memory.nextId, 0, 2⟩ (request case) (start case)
def logical (case : Case) (leading trailing : List (Event Failure Insertion.Native.Fault)) :=
  Interner.Scoped.findDetailed (resources (events case leading trailing) (.preparation .incomplete)) model (request case)
    { (CacheTests.constructed case).graph with allocationCursor := leading.length }

/-- Reuse all six cache/normalization inputs. Preparation and release are
protocol slots even when no host allocation occurs; no take slot is recorded. -/
theorem trace_layout (case : Case) :
    (initialization case).1 = .ok (some (lookup case)) ∧
    (initialization case).2.events = (match case with
      | .temporary => [.allocate .temporary true, .prepare (lookup case) (.ok ())]
      | .scratch => [.prepare (lookup case) (.ok ())]
      | _ => []) ∧
    (close case).2.events = (if case = .temporary then [.release (lookup case)] else []) := by
  cases case <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

attribute [local irreducible] Initialization.capture Close.capture

/-- The actual source caller and checked scoped caller consume the same complete
cache-leaf stream. Every graph callback would reject if reached. -/
theorem existing_family (case : Case) (leading trailing : List (Event Failure Insertion.Native.Fault))
    (other : Meaning) (read : Read) (sequence : BitVec 32) :
    (actual case).1 = .ok 17 ∧ Good (source case) (request case).arguments (actual case).2.world ∧
    Closed (actual case).2.scope ∧ (actual case).2.world.graph = (CacheTests.constructed case).graph ∧
    (actual case).2.world.memory = (close case).2.effects.session ∧
    (logical case leading trailing).1 = .ok 17 ∧
    (logical case leading trailing).2 = ⟨⟨some (close case).1, sorted case, .lookup⟩,
      { (actual case).2.world.graph with allocationCursor :=
        (leading ++ (initialization case).2.events.map Event.normalization ++ (close case).2.events.map Event.normalization).length }⟩ := by
  have observed := CacheTests.prefix_observed case
  have good : Good (source case) (request case).arguments (CacheTests.before case) := Publication.OriginTests.initial_good case
  have item := (ConstructorItem.prepare_success (request case).item CacheTests.debug (CacheTests.before case)
    (CacheTests.constructed case) CacheTests.address good.1
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) AssemblyItem.Initializers.Tests.debug_valid observed.1).2
  have ready := good_frame _ _ (source case) (request case).arguments good item.valid item.memory
  have initialized : Caller.initLookup host 160 11 (source case) ⟨(CacheTests.constructed case).memory.memory.nextId, 0, 2⟩
      (request case) ⟨start case, { lookup := none }⟩ =
      (.ok (sorted case), (CacheTests.prepared case Normalization.Tests.success 160).2) := by
    rw [observed.2.1]
    exact Prod.ext observed.2.2.2.1 rfl
  obtain ⟨token, recorded, composed⟩ := cached host 160 11 (commutes case) CacheTests.poison Interner.Queries.queries model
    (source case) (request case) (CacheTests.constructed case) (CacheTests.stack case) _ (sorted case)
    (CacheTests.prepared case Normalization.Tests.success 160).2 (key case) 17 leading trailing other read sequence
    ready.1 ready.2 observed.2.2.1 (by cases case <;> rfl)
    (Publication.external_admitted _ (Normalization.Tests.external_admitted _)) initialized
    observed.2.2.2.2.1 observed.2.2.2.2.2.1 observed.2.2.2.2.2.2.1 observed.2.2.2.2.2.2.2 rfl rfl
  have same := Option.some.inj (Except.ok.inj (recorded.symm.trans (trace_layout case).1))
  subst token
  obtain ⟨after, ran, valid, locals, graph, memory, _, _, result, state⟩ := composed
  change actual case = (.ok 17, after) at ran
  rw [ran]
  exact ⟨rfl, valid, locals, graph, memory, result, state⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.CacheStream.Tests
