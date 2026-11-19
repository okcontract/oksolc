/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPhysicalDispatchProduction
import Compiler.Extraction.InternerPhysicalDispatchPreservationTests
import Compiler.Extraction.InternerConstructorFrameTests
import Compiler.Extraction.InternerBorrowedConstructorTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Recursive.ProductionTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open Normalization.Tests

abbrev model := Compiler.Extraction.Recursive.Tests.model

def seed (publishFails : Bool) : Primitives Nat :=
  { Semantic.Tests.callbacks model 7 with
    simplify := fun _ _ before => (.ok (some 1), before)
    publish := (OwnedCall.Tests.callbacks .unchanged publishFails true).publish }

theorem graph_ownership (fail : Bool) (source : View) (values : List NodeId) :
    OwnedCall.GraphContracts 7 source values (seed fail) := by
  have previous := OwnedCall.Tests.callbacks_contracts .unchanged fail true source values
  exact ⟨previous.publish, previous.insert⟩

theorem graph_semantics (fail : Bool) (source : View) (values : List NodeId) :
    Semantic.GraphContracts 7 source values model (seed fail) := by
  have previous := Semantic.Tests.semantics model 7 source values
  refine ⟨previous.insert, ?_⟩
  intro key slice id before value _aligned _held valid _evaluated _actual
  cases fail with
  | false => exact previous.publish key slice id before value _aligned _held valid _evaluated _actual
  | true => exact Semantic.Ensures.error model before.graph (.language .outOfMemory) _ valid

def heap : Interner.Heap where
  read := fun id => if id = 1 then some 10 else if id = 3 then some 32 else if id = 42 then some 42 else none
  table := fun _ => none

def source : View := ⟨0, 0, 2⟩
def request := Semantic.Tests.request
def caller : World Nat := ⟨heap, original⟩
def buffer : View := ⟨caller.memory.memory.nextId, 0, 2⟩
def world : World Nat := { caller with memory := { caller.memory with memory := before.memory } }
def actual (fail : Bool) (depth : Nat) := callbacks (seed fail) Compiler.Extraction.Recursive.Tests.reads 64 (PreservationTests.physical depth)
def run (external : External Nat) (q : Caller.Queries) (fail : Bool) (depth : Nat) :=
  Caller.find external 160 7 (actual fail depth) q source buffer request world
def forceId : NodeId := 42
def forced := Caller.force success 160 7 (actual false 1) Caller.Tests.queries source buffer forceId request.item request.arguments world

theorem source_represented : Represents original.memory source request.arguments := Semantic.Tests.source_represented

theorem graph_valid : Interner.Invariant model heap := ⟨(by intro _ _ impossible; cases impossible), trivial⟩

/-- Every finite logical unfolding supplies the recursive constructor laws to
one complete physical caller. This fixture does not claim native constructor
simulation: the counted adapter remains explicitly a test implementation. -/
theorem production_contract (external : External Nat) (admitted : Admitted external) (q : Caller.Queries)
    (fail : Bool) (depth : Nat) :
    Semantic.Verified external 7 source request.arguments model
      (Caller.findBody external 160 7 (actual fail depth) q source buffer request) world (fun id after => after.read id = some 42) ∧
    Semantic.Verified external 7 source request.arguments model
      (Caller.forceBody external 160 7 (actual fail depth) q source buffer 42 request.item request.arguments) world (fun _ _ => True) := by
  have words := Compiler.Extraction.Recursive.constructors_sound
    (Dispatch.wordBaseMeaning Compiler.Extraction.Recursive.Tests.env Compiler.Extraction.Recursive.Tests.base)
    Compiler.Extraction.Recursive.Tests.pushes (PreservationTests.logical depth) (PreservationTests.logical_sound depth) (Debug := Unit)
  have addresses := Compiler.Extraction.Recursive.constructors_address Compiler.Extraction.Recursive.Tests.env
    (ArithmeticShift.shiftMeaning Compiler.Extraction.Recursive.Tests.base) (PreservationTests.logical depth)
    (by simpa only [Compiler.Extraction.Recursive.Tests.model, Dispatch.word_dispatch_address_model] using PreservationTests.logical_sound depth) (Debug := Unit)
  have shifts := Compiler.Extraction.Recursive.constructors_sar
    (AddressMask.addressMeaning Compiler.Extraction.Recursive.Tests.env Compiler.Extraction.Recursive.Tests.base)
    (PreservationTests.logical depth) (PreservationTests.logical_sound depth) (Debug := Unit)
  have coupled : ∀ slice, (projection (Held 7 source request.arguments slice)).Constructors
      (constructors (PreservationTests.physical depth)) (Compiler.Extraction.Recursive.constructors (Debug := Unit) (PreservationTests.logical depth)) :=
    fun _ => ⟨fun _ _ _ => PreservationTests.counted_projects _ _ _ _ _,
      fun _ _ => PreservationTests.counted_projects _ _ _ _ _, fun _ _ _ => PreservationTests.counted_projects _ _ _ _ _,
      fun _ _ _ _ => PreservationTests.counted_projects _ _ _ _ _,
      fun _ _ _ _ _ _ => PreservationTests.counted_projects _ _ _ _ _⟩
  have checked := production_verified external 160 7 (seed fail) q Compiler.Extraction.Recursive.Tests.reads 64
    (PreservationTests.physical depth) source request 42 caller before.memory _
    Compiler.Extraction.Recursive.Tests.env Compiler.Extraction.Recursive.Tests.base 42
    ⟨original_valid, source_represented⟩ actual_caller_allocation admitted (graph_ownership fail source request.arguments)
    (graph_semantics fail source request.arguments) _ coupled words addresses shifts
    (fun heap _ => Compiler.Extraction.Recursive.Tests.reads_sound heap) graph_valid (by rfl')
  exact ⟨checked.1, checked.2 (by rfl') (by rfl')⟩

theorem success_observation :
    let found := run success Caller.Tests.queries false 1
    found.1 = .ok 7 ∧ found.2.world.graph.read 7 = some 42 ∧ found.2.world.memory.heap 5 = none ∧
      found.2.world.memory.effects = 116 ∧ found.2.scope.lookup = none ∧ found.2.scope.handedOff = true :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem publication_failure_observation :
    let found := run success Caller.Tests.queries true 1
    found.1 = .error (.language .outOfMemory) ∧ found.2.world.graph.read 7 = some 42 ∧ found.2.world.memory.heap 5 = none ∧
      found.2.world.memory.effects = 116 ∧ found.2.scope = ⟨none, none, false⟩ :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem cutoff_observation :
    let found := run success Caller.Tests.queries false 0
    found.1 = .error (.language .unsupported) ∧ ordinary found.1 = false ∧ found.2.world.memory.effects = 14 ∧
      found.2.world.memory.heap 5 = some ⟨7, .arguments [1, 3]⟩ := ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem normalization_failure_observation :
    let found := run (external (fun _ => true)) Caller.Tests.queries false 1
    found.1 = .error (.language .outOfMemory) ∧ found.2.world.graph.read 7 = none ∧
      found.2.world.memory.effects = 13 ∧ found.2.scope = ⟨none, none, false⟩ := ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem force_observation : forced.1 = .ok () ∧ forced.2.world.memory.heap 5 = none ∧
    forced.2.world.memory.effects = 115 ∧ forced.2.scope.lookup = none ∧ forced.2.scope.handedOff = true ∧
    forced.2.world.graph.read forceId = some 42 := ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem production_closed (external : External Nat) (admitted : Admitted external) (q : Caller.Queries)
    (fail : Bool) (depth : Nat) (completed : ordinary (run external q fail depth).1 = true) :
    let found := run external q fail depth
    Good source request.arguments found.2.world ∧ Closed found.2.scope ∧
      Interner.Invariant model found.2.world.graph ∧ Interner.Stable world.graph found.2.world.graph ∧
      match found.1 with | .error _ => True | .ok id => found.2.world.graph.read id = some 42 := by
  have checked := Semantic.Verified.closed external 7 source request.arguments model _ world _
    (production_contract external admitted q fail depth).1 completed
  generalize executed : Caller.invoke external 7 (Caller.findBody external 160 7 (actual fail depth) q source buffer request) world = outcome at checked
  dsimp only [run, Caller.find]
  rw [executed]
  rcases outcome with ⟨result, after⟩
  cases result <;> exact checked

theorem success_verified :
    let found := run success Caller.Tests.queries false 1
    Good source request.arguments found.2.world ∧ Closed found.2.scope ∧
      Interner.Invariant model found.2.world.graph ∧ Interner.Stable world.graph found.2.world.graph ∧ found.2.world.graph.read 7 = some 42 := by
  have completed : ordinary (run success Caller.Tests.queries false 1).1 = true := by rw [success_observation.1]; rfl
  have checked := production_closed success (external_admitted _) Caller.Tests.queries false 1 completed
  generalize ran : run success Caller.Tests.queries false 1 = outcome at checked ⊢
  rcases outcome with ⟨result, after⟩
  have accepted := success_observation.1
  rw [ran] at accepted
  dsimp only at accepted
  rw [accepted] at checked
  exact checked

/-- Reuse the existing external-cursor refusal fixture in the complete caller.
This checks the endpoint's observation boundary, not native allocator-trace
admission. The old raw-graph projection is disproved by the same fixture. -/
def cursorFailure : Find Nat := fun _ => PreservationTests.advance (.error .outOfMemory)
def cursorFailureModel : Interner.Request → Interner.Action NodeId :=
  fun _ => PreservationTests.advanceModel (.error .outOfMemory)

theorem cursor_failure_sound : Compiler.Extraction.Recursive.FindSound model cursorFailureModel := by
  intro request heap expected valid _evaluated result after ran
  have same : (.error Interner.Error.outOfMemory, { heap with allocationCursor := heap.allocationCursor + 1 }) =
      (result, after) := ran
  cases same
  exact ⟨valid.with_cursor _, fun _ _ found => found, trivial⟩

theorem cursor_production_contract :
    Semantic.Verified success 7 source request.arguments model
      (Caller.findBody success 160 7 (callbacks (seed false) Compiler.Extraction.Recursive.Tests.reads 64 cursorFailure)
        Caller.Tests.queries source buffer request) world (fun id after => after.read id = some 42) := by
  have words := Compiler.Extraction.Recursive.constructors_sound
    (Dispatch.wordBaseMeaning Compiler.Extraction.Recursive.Tests.env Compiler.Extraction.Recursive.Tests.base)
    Compiler.Extraction.Recursive.Tests.pushes cursorFailureModel cursor_failure_sound (Debug := Unit)
  have addresses := Compiler.Extraction.Recursive.constructors_address Compiler.Extraction.Recursive.Tests.env
    (ArithmeticShift.shiftMeaning Compiler.Extraction.Recursive.Tests.base) cursorFailureModel
    (by simpa only [Compiler.Extraction.Recursive.Tests.model, Dispatch.word_dispatch_address_model] using cursor_failure_sound) (Debug := Unit)
  have shifts := Compiler.Extraction.Recursive.constructors_sar
    (AddressMask.addressMeaning Compiler.Extraction.Recursive.Tests.env Compiler.Extraction.Recursive.Tests.base)
    cursorFailureModel cursor_failure_sound (Debug := Unit)
  have coupled : ∀ slice, (projectionAt PreservationTests.observed (Held 7 source request.arguments slice)).Constructors
      (constructors cursorFailure) (Compiler.Extraction.Recursive.constructors (Debug := Unit) cursorFailureModel) :=
    fun _ => ⟨fun _ _ _ => PreservationTests.advance_projects_held _ _ _ _ _,
      fun _ _ => PreservationTests.advance_projects_held _ _ _ _ _, fun _ _ _ => PreservationTests.advance_projects_held _ _ _ _ _,
      fun _ _ _ _ => PreservationTests.advance_projects_held _ _ _ _ _,
      fun _ _ _ _ _ _ => PreservationTests.advance_projects_held _ _ _ _ _⟩
  exact (production_verified_cursor (fun world => world.memory.effects) success 160 7 (seed false) Caller.Tests.queries
    Compiler.Extraction.Recursive.Tests.reads 64 cursorFailure source request 42 caller before.memory _
    Compiler.Extraction.Recursive.Tests.env Compiler.Extraction.Recursive.Tests.base 42
    ⟨original_valid, source_represented⟩ actual_caller_allocation (external_admitted _) (graph_ownership false source request.arguments)
    (graph_semantics false source request.arguments) _ coupled words addresses shifts
    (fun heap _ => Compiler.Extraction.Recursive.Tests.reads_sound heap) graph_valid (by rfl')).1

theorem cursor_failure_observation :
    let called := Caller.find success 160 7 (callbacks (seed false) Compiler.Extraction.Recursive.Tests.reads 64 cursorFailure)
      Caller.Tests.queries source buffer request world
    called.1 = .error (.language .outOfMemory) ∧ called.2.world.graph = world.graph ∧
      called.2.world.memory.effects = 116 ∧ called.2.scope = ⟨none, none, false⟩ :=
  ⟨by rfl', by rfl', by rfl', by rfl'⟩

attribute [local irreducible] Caller.invoke

theorem cursor_failure_closed :
    let called := Caller.find success 160 7 (callbacks (seed false) Compiler.Extraction.Recursive.Tests.reads 64 cursorFailure)
      Caller.Tests.queries source buffer request world
    Good source request.arguments called.2.world ∧ Closed called.2.scope ∧
      Interner.Invariant model called.2.world.graph ∧ Interner.Stable world.graph called.2.world.graph := by
  intro called
  have result : called.1 = .error (.language .outOfMemory) := cursor_failure_observation.1
  have completed : ordinary called.1 = true := by rw [result]; rfl
  have checked := Semantic.Verified.closed success 7 source request.arguments model _ world _ cursor_production_contract completed
  exact ⟨checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Recursive.ProductionTests
