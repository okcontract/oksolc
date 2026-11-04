/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerQueryProduction
import Compiler.Extraction.InternerInsertionCallerTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Query.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open Interner.Queries (queries)

abbrev model := Compiler.Extraction.Recursive.Tests.model
def cells := Insertion.CallerTests.cells ++ [Insertion.Tests.push 0, Insertion.Tests.push 0, Insertion.Tests.push 42]
def heap := Interner.observedHeap cells (fun _ => none)
def source := Insertion.CallerTests.source
def buffer := Insertion.CallerTests.buffer
def request := Insertion.CallerTests.request
def original : World (Publication.Effects Nat) := { Insertion.CallerTests.original with graph := heap }
def world : World (Publication.Effects Nat) := { Insertion.CallerTests.world with graph := heap }
def ops := Insertion.CallerTests.ops
def actual := Recursive.callbacks
  (Insertion.graphCallbacks ops 7 source model Insertion.CallerTests.select Insertion.CallerTests.seed)
  Interner.representativeReads 64 Publication.Tests.physicalFind
def found := Caller.invoke (Publication.external ops.arguments) 7
  (findBody (Publication.external ops.arguments) 160 7 actual source buffer request) world
def forced := Caller.invoke (Publication.external ops.arguments) 7
  (forceBody (Publication.external ops.arguments) 160 7 actual source buffer 7 request.item request.arguments) world

theorem graph_valid : Interner.Invariant model heap := by
  refine ⟨?_, rfl, ?_⟩
  · intro _ _ impossible; cases impossible
  · simp [Storage.Coherent, cells, Insertion.CallerTests.cells, Insertion.Tests.push, Cache.Item.eval,
      Cache.readArguments, model, Compiler.Extraction.Recursive.Tests.model, Storage.Cell.value,
      Storage.Cell.isPush, Storage.Cell.dataValue]
    decide

theorem production_contract :
    Semantic.Verified (Publication.external ops.arguments) 7 source request.arguments model
      (findBody (Publication.external ops.arguments) 160 7 actual source buffer request) world
      (fun id after => after.read id = some 42) ∧
    Semantic.Verified (Publication.external ops.arguments) 7 source request.arguments model
      (forceBody (Publication.external ops.arguments) 160 7 actual source buffer 7 request.item request.arguments) world
      (fun _ _ => True) := by
  have words := Compiler.Extraction.Recursive.constructors_sound
    (Dispatch.wordBaseMeaning Compiler.Extraction.Recursive.Tests.env Compiler.Extraction.Recursive.Tests.base)
    Compiler.Extraction.Recursive.Tests.pushes Publication.Tests.logical Publication.Tests.logical_sound (Debug := Unit)
  have addresses := Compiler.Extraction.Recursive.constructors_address Compiler.Extraction.Recursive.Tests.env
    (ArithmeticShift.shiftMeaning Compiler.Extraction.Recursive.Tests.base) Publication.Tests.logical
    (by simpa only [Compiler.Extraction.Recursive.Tests.model, Dispatch.word_dispatch_address_model] using Publication.Tests.logical_sound) (Debug := Unit)
  have shifts := Compiler.Extraction.Recursive.constructors_sar
    (AddressMask.addressMeaning Compiler.Extraction.Recursive.Tests.env Compiler.Extraction.Recursive.Tests.base)
    Publication.Tests.logical Publication.Tests.logical_sound (Debug := Unit)
  have checked := production_verified ops Insertion.CallerTests.select 160 7 Insertion.CallerTests.seed 64
    Publication.Tests.physicalFind source request 7 original Normalization.Tests.before.memory _
    Compiler.Extraction.Recursive.Tests.env Compiler.Extraction.Recursive.Tests.base 42
    Insertion.CallerTests.original_good (by rfl) Normalization.Tests.actual_caller_allocation
    (Insertion.Tests.admitted none) _ (Publication.Tests.coupled 7 source request.arguments) words addresses shifts
    graph_valid (by rfl')
  exact ⟨checked.1, checked.2 (by rfl') (by rfl')⟩

theorem found_from_representatives : found.1 = .ok 7 ∧ found.2.world.graph.read 7 = some 42 ∧
    found.2.world.graph.table ⟨1, 1, 0, [1, 3], 77⟩ = some 7 ∧ found.2.scope.lookup = none :=
  ⟨by rfl', by rfl', by rfl', by rfl'⟩
theorem force_validated : forced.1 = .ok () ∧ forced.2.world.graph.table ⟨1, 1, 0, [1, 3], 0⟩ = some 7 :=
  ⟨by rfl', by rfl'⟩

def invalid := Caller.invoke (Publication.external ops.arguments) 7
  (forceBody (Publication.external ops.arguments) 160 7 actual source buffer 99 request.item request.arguments) world
theorem invalid_before_normalization : invalid.1 = .error (.language .invalidId) ∧ invalid.2.world = world ∧
    invalid.2.scope.lookup = none := ⟨by rfl', by rfl', by rfl'⟩

def classified (kind : Kind) (instruction : Option Opcode) := Caller.invoke (Publication.external ops.arguments) 7
  (findBody (Publication.external ops.arguments) 160 7 actual source buffer
    { request with item := ⟨kind, instruction, 0⟩ }) world
theorem assembly_error_cleanup : (classified 13 none).1 = .error (.language .assemblyException) ∧
    (classified 13 none).2.world = world ∧ (classified 13 none).2.scope.lookup = none :=
  ⟨by rfl', by rfl', by rfl'⟩
theorem early_assembly_error : (classified 13 (some 1)).1 = .error (.language .assemblyException) ∧
    (classified 13 (some 1)).2.scope.lookup = none := ⟨by rfl', by rfl'⟩
theorem malformed_retains_scope : (classified 2 (some 1)).1 = .error (.language .safetyFault) ∧
    (classified 2 (some 1)).2.scope.lookup.isSome = true := ⟨by rfl', by rfl'⟩

def absent := Caller.invoke (Publication.external ops.arguments) 7
  (findBody (Publication.external ops.arguments) 160 7 actual source buffer request)
  { world with graph := { heap with representatives := none } }
theorem absent_rejected : absent.1 = .error (.language .safetyFault) ∧
    absent.2.scope.lookup = none ∧ absent.2.world.memory = world.memory := ⟨by rfl', by rfl', by rfl'⟩

/-- Poison the unused branches so a cache hit cannot accidentally simplify or
insert. For GAS, a populated table must be ignored and insertion sees `false`. -/
def branches : Primitives (Publication.Effects Nat) where
  simplify := fun _ _ before => (.error (.language .invalidId), before)
  publish := fun _ _ _ before => (.error (.language .invalidId), before)
  insert := fun _ _ deterministic before =>
    (.error (.language (if deterministic then .invalidId else .capacity)), before)
def cachedWorld := { world with graph := { heap with table := fun _ => some 7 } }
def cached := Caller.invoke (Publication.external ops.arguments) 7
  (findBody (Publication.external ops.arguments) 160 7 branches source buffer request) cachedWorld
def nondeterministic := Caller.invoke (Publication.external ops.arguments) 7
  (findBody (Publication.external ops.arguments) 160 7 branches source buffer
    { request with item := ⟨1, some 0x5a, 0⟩ }) cachedWorld
theorem deterministic_cache_hit : cached.1 = .ok 7 ∧ cached.2.world.graph = cachedWorld.graph ∧
    cached.2.scope.lookup = none := ⟨by rfl', by rfl', by rfl'⟩
theorem nondeterministic_skips_cache_and_simplifier :
    nondeterministic.1 = .error (.language .capacity) ∧ nondeterministic.2.scope.lookup = none :=
  ⟨by rfl', by rfl'⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Query.Tests
