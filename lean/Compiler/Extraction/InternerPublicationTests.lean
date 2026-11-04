/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPublicationProduction
import Compiler.Extraction.InternerPhysicalDispatchProductionTests
import Compiler.Extraction.OwnedKeysPhysicalTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray

abbrev model := Compiler.Extraction.Recursive.Tests.model
def host := Normalization.Tests.success
def attempt (fail : Bool) : OwnedKeys.Physical.Probe Nat := fun _ state => (!fail, state.effects + 1)

/-- Insertion is deliberately unsupported in this fixture. The seed publication
and simplification are deliberately wrong and must both be replaced. -/
def seedFor (σ : Type) : Primitives (Effects σ) where
  simplify := fun _ _ before => (.ok (some 1), before)
  publish := fun _ _ _ before => (.error (.language .outOfMemory), before)
  insert := fun _ _ _ before => (.error (.language .unsupported), before)

def seed := seedFor Nat

theorem insertion_memory (source : View) (values : List NodeId) : InsertionMemory 7 source values seed := by
  intro key slice deterministic before _ _
  change false = true → Good source values before
  intro impossible; cases impossible

theorem insertion_semantics (source : View) (values : List NodeId) : InsertionSemantics 7 source values model seed := by
  intro key slice deterministic before value _ _ valid _
  exact Semantic.Ensures.error model before.graph (.language .unsupported) _ valid

/-- A constructor fixture that validates an existing word and otherwise rejects.
It preserves both cache projections and has no native recursive-construction claim. -/
def logical (request : Interner.Request) : Interner.Action NodeId := fun before =>
  match request.item.eval model before.read request.arguments request.sequence with
  | none => (.error .unsupported, before)
  | some value => if before.read 7 = some value then (.ok 7, before) else (.error .unsupported, before)

theorem logical_sound : Compiler.Extraction.Recursive.FindSound model logical := by
  intro request before value valid evaluated result after ran
  simp only [logical, evaluated] at ran
  split at ran
  · rename_i actual
    cases ran; exact ⟨valid, fun _ _ found => found, actual⟩
  · cases ran; exact ⟨valid, fun _ _ found => found, trivial⟩

def physicalFindWith (advance : σ → σ) : Recursive.Find (Effects σ) := fun request before =>
  let (result, graph) := logical request before.graph
  (result.mapError Fault.language, { before with graph, memory := { before.memory with
    effects := { before.memory.effects with allocator := advance before.memory.effects.allocator } } })

def physicalFind := physicalFindWith (fun effects : Nat => effects + 1)

theorem coupled (allocator : Nat) (source : View) (values : List NodeId) (owned : ArgumentSlice) :
    (Recursive.projection (Held allocator source values owned)).Constructors (Recursive.constructors physicalFind)
      (Compiler.Extraction.Recursive.constructors (Debug := Unit) logical) := by
  have each : ∀ request, Recursive.Projects (Held allocator source values owned) (physicalFind request) (logical request) := by
    intro request before held _
    cases ran : logical request before.graph with
    | mk result graph =>
      simp only [physicalFind, physicalFindWith, ran]
      exact ⟨⟨⟨⟨held.1.1.memory, held.1.1.related, held.1.1.injected⟩, held.1.2⟩, held.2⟩, trivial, trivial⟩
  exact ⟨fun _ _ _ => each _, fun _ _ => each _, fun _ _ _ => each _, fun _ _ _ _ => each _, fun _ _ _ _ _ _ => each _⟩

def heap : Interner.Heap where
  read := fun id => if id = 1 then some 10 else if id = 3 then some 32 else if id = 7 ∨ id = 42 then some 42 else none
  table := fun _ => none
def source : View := ⟨0, 0, 2⟩
def request := Semantic.Tests.request
def caller : World (Effects Nat) := ⟨heap, ⟨Normalization.Tests.original.heap, Normalization.Tests.original.memory,
  ⟨fun _ => none, Normalization.Tests.original.effects⟩⟩⟩
def world : World (Effects Nat) := { caller with memory := { caller.memory with memory := Normalization.Tests.before.memory } }
def buffer : View := ⟨3, 0, 2⟩
def actual (fail : Bool) := Recursive.callbacks (callbacks (attempt fail) host 7 source seed)
  Compiler.Extraction.Recursive.Tests.reads 64 physicalFind
def found (fail := false) := Caller.find (external host) 160 7 (actual fail) Caller.Tests.queries source buffer request world
def forced (fail := false) := Caller.force (external host) 160 7 (actual fail) Caller.Tests.queries source buffer
  42 request.item request.arguments world
def findKey : Key := ⟨1, 1, 0, [1, 3], 77⟩
def forceKey : Key := { findKey with sequence := 0 }

theorem initial_good : Good source request.arguments caller :=
  ⟨⟨Normalization.Tests.original_valid.memory, Normalization.Tests.original_valid.related,
    Normalization.Tests.original_valid.injected⟩, Semantic.Tests.source_represented⟩
theorem graph_valid : Interner.Invariant model heap := ⟨(by intro _ _ impossible; cases impossible), trivial⟩

theorem production_contract (fail : Bool) :
    Semantic.Verified (external host) 7 source request.arguments model
      (Caller.findBody (external host) 160 7 (actual fail) Caller.Tests.queries source buffer request) world
        (fun id after => after.read id = some 42) ∧
    Semantic.Verified (external host) 7 source request.arguments model
      (Caller.forceBody (external host) 160 7 (actual fail) Caller.Tests.queries source buffer
        42 request.item request.arguments) world (fun _ _ => True) := by
  have words := Compiler.Extraction.Recursive.constructors_sound
    (Dispatch.wordBaseMeaning Compiler.Extraction.Recursive.Tests.env Compiler.Extraction.Recursive.Tests.base)
    Compiler.Extraction.Recursive.Tests.pushes logical logical_sound (Debug := Unit)
  have addresses := Compiler.Extraction.Recursive.constructors_address Compiler.Extraction.Recursive.Tests.env
    (ArithmeticShift.shiftMeaning Compiler.Extraction.Recursive.Tests.base) logical
    (by simpa only [Compiler.Extraction.Recursive.Tests.model, Dispatch.word_dispatch_address_model] using logical_sound) (Debug := Unit)
  have shifts := Compiler.Extraction.Recursive.constructors_sar
    (AddressMask.addressMeaning Compiler.Extraction.Recursive.Tests.env Compiler.Extraction.Recursive.Tests.base) logical
    logical_sound (Debug := Unit)
  have checked := production_verified (attempt fail) host 160 7 seed Caller.Tests.queries
    Compiler.Extraction.Recursive.Tests.reads 64 physicalFind source request 42 caller Normalization.Tests.before.memory _
    Compiler.Extraction.Recursive.Tests.env Compiler.Extraction.Recursive.Tests.base 42 initial_good
    Normalization.Tests.actual_caller_allocation (Normalization.Tests.external_admitted _) (insertion_memory _ _)
    (insertion_semantics _ _) _ (coupled 7 source request.arguments) words addresses shifts
    (fun heap _ => Compiler.Extraction.Recursive.Tests.reads_sound heap) graph_valid (by rfl')
  exact ⟨checked.1, checked.2 (by rfl') (by rfl')⟩

theorem find_success : (found).1 = .ok 7 ∧ (found).2.world.graph.table findKey = some 7 ∧
    (found).2.world.memory.effects.keys findKey = some ⟨5, 7⟩ ∧
    (found).2.world.memory.heap 5 = some ⟨7, .arguments [1, 3]⟩ ∧
    (found).2.world.memory.effects.allocator = 15 ∧ (found).2.scope.lookup = none ∧ (found).2.scope.handedOff = true :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem find_oom_cleanup : (found true).1 = .error (.language .outOfMemory) ∧
    (found true).2.world.graph.table findKey = none ∧ (found true).2.world.memory.effects.keys findKey = none ∧
    (found true).2.world.memory.heap 5 = none ∧ (found true).2.world.memory.effects.allocator = 117 ∧
    (found true).2.scope = ⟨none, none, false⟩ := ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem force_success : (forced).1 = .ok () ∧ (forced).2.world.graph.table forceKey = some 42 ∧
    (forced).2.world.memory.effects.keys forceKey = some ⟨5, 42⟩ ∧
    (forced).2.world.memory.heap 5 = some ⟨7, .arguments [1, 3]⟩ ∧
    (forced).2.world.memory.effects.allocator = 14 := ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩

def replacementMemory : Compiler.ZigAir.Memory.State := {
  heap := (6, ⟨84, .array 2 word, [], true, true⟩) :: (forced).2.world.memory.memory.heap
  nextId := 7, nextAddress := 92 }
def replacementWorld : World (Effects Nat) := { (forced).2.world with memory :=
  { (forced).2.world.memory with memory := replacementMemory } }
def cachedForce (fail := false) := Caller.force (external host) 160 7 (actual fail) Caller.Tests.queries source ⟨6, 0, 2⟩
  42 request.item request.arguments replacementWorld

theorem replacement_allocation : Compiler.ZigAir.Memory.allocate (forced).2.world.memory.memory (.array 2 word) =
    .ok (.pointer (.pointer true false (.array 2 word)) ⟨6, 0⟩, replacementMemory) := by rfl'

theorem force_cache_hit (fail : Bool) : (cachedForce fail).1 = .ok () ∧
    (cachedForce fail).2.world.memory.effects.keys forceKey = some ⟨5, 42⟩ ∧
    (cachedForce fail).2.world.memory.heap 5 = some ⟨7, .arguments [1, 3]⟩ ∧
    (cachedForce fail).2.world.memory.heap 8 = none ∧
    (cachedForce fail).2.world.memory.effects.allocator = 14 :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩

/-- A replacement at the publication boundary, after actual normalization and
take. Complete forceEqual instead takes the cache-hit return above. -/
def prepared := Normalization.init normalizationOwnershipCode (external host) 160 7 true source ⟨6, 0, 2⟩
  request.arguments replacementWorld.memory
def preparedHandle : Handle := ⟨⟨6, 0, 2⟩, [1, 3], none⟩
def taken := takeOwned normalizationOwnershipCode (external host) 7 preparedHandle prepared.2
def publicationWorld : World (Effects Nat) := { replacementWorld with memory := taken.2 }
def replacement (fail := false) := publish (attempt fail) host 7 source forceKey ⟨8, [1, 3]⟩ 42 publicationWorld

theorem replacement_prepared : prepared.1 = .ok preparedHandle ∧
    taken.1 = .ok (⟨8, [1, 3]⟩, preparedHandle) := ⟨by rfl', by rfl'⟩
theorem replacement_success : (replacement).1 = .ok () ∧
    (replacement).2.memory.effects.keys forceKey = some ⟨8, 42⟩ ∧
    (replacement).2.memory.heap 5 = none ∧ (replacement).2.memory.memory.heap.lookup 5 = none ∧
    (replacement).2.memory.heap 8 = some ⟨7, .arguments [1, 3]⟩ ∧
    (replacement).2.memory.effects.allocator = 125 := ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem replacement_oom : (replacement true).1 = .error (.language .outOfMemory) ∧
    (replacement true).2.memory.effects.keys forceKey = some ⟨5, 42⟩ ∧
    (replacement true).2.memory.heap 5 = some ⟨7, .arguments [1, 3]⟩ ∧
    (replacement true).2.memory.heap 8 = some ⟨7, .arguments [1, 3]⟩ ∧
    (replacement true).2.memory.effects.allocator = 23 := ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩

def corrupt (address : Nat) : World (Effects Nat) := { world with memory := { world.memory with effects :=
  { world.memory.effects with keys := OwnedKeys.store (fun _ => none) forceKey ⟨address, 42⟩ } } }
def rejected (address : Nat) := Caller.force (external host) 160 7 (actual false) Caller.Tests.queries source buffer
  42 request.item request.arguments (corrupt address)

theorem source_alias_rejected : (rejected 0).1 = .error (.language .safetyFault) ∧
    ordinary (rejected 0).1 = false ∧ (rejected 0).2.world.memory.effects.allocator = 13 ∧
    (rejected 0).2.world.memory.heap 5 = some ⟨7, .arguments [1, 3]⟩ ∧ (rejected 0).2.scope.handedOff = false :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩
theorem incoming_alias_rejected : (rejected 5).1 = .error (.language .safetyFault) ∧
    (rejected 5).2.world.memory.heap 5 = some ⟨7, .arguments [1, 3]⟩ := ⟨by rfl', by rfl'⟩
theorem absent_old_rejected : (rejected 999).1 = .error (.language .safetyFault) ∧
    (rejected 999).2.world.memory.effects.allocator = 13 := ⟨by rfl', by rfl'⟩

/-- An old key must own arguments, even if another live block has the same
allocator and extent. Rejection precedes probing/free and retains the byte block. -/
def byteOwner : World (Effects Nat) := { publicationWorld with memory := { publicationWorld.memory with
  heap := Memory.write publicationWorld.memory.heap 5 (some ⟨7, .bytes 2⟩) } }
theorem byte_owner_rejected : admit 7 source forceKey ⟨8, [1, 3]⟩ byteOwner = .error .oldOwnership ∧
    publish (attempt false) host 7 source forceKey ⟨8, [1, 3]⟩ 42 byteOwner = (.error (.language .safetyFault), byteOwner) :=
  ⟨by rfl', by rfl'⟩

theorem admission_reasons :
    admit 7 source forceKey ⟨5, [1, 3]⟩ (corrupt 0) = .error .sourceAlias ∧
    admit 7 source forceKey ⟨5, [1, 3]⟩ (corrupt 5) = .error .incomingAlias ∧
    admit 7 source forceKey ⟨5, [1, 3]⟩ (corrupt 999) = .error .oldOwnership ∧
    admit 7 source forceKey ⟨5, []⟩ world = .error .descriptor ∧
    admit 7 source forceKey ⟨8, [1, 3]⟩ publicationWorld = .ok () :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩

def emptyKey : Key := { forceKey with arguments := [] }
def emptyWorld : World (Effects Nat) := { world with memory := { world.memory with effects :=
  { world.memory.effects with keys := OwnedKeys.store (fun _ => none) emptyKey ⟨0, 42⟩ } } }
theorem empty_sentinel_admitted : admit 7 source emptyKey ⟨0, []⟩ emptyWorld = .ok () := by rfl'
theorem declared_contract_admitted (allocator : Nat) (source : View) (key : Key) (owned : ArgumentSlice)
    (before : World (Effects Nat)) (input : Input allocator source key owned before) :
    admit allocator source key owned before = .ok () := admit_complete allocator source key owned before input

theorem force_tables :
    (forced).2.world.graph.table = Cache.put equalityFields (fun _ => none) forceKey 42 ∧
    (forced).2.world.memory.effects.keys = OwnedKeys.store (fun _ => none) forceKey ⟨5, 42⟩ := ⟨by rfl', by rfl'⟩

theorem force_projection : (forced).2.world.graph.table = OwnedKeys.view (forced).2.world.memory.effects.keys := by
  rw [force_tables.1, force_tables.2, OwnedKeys.view_store]
  rfl

theorem replacement_tables :
    (replacement).2.graph.table = Cache.put equalityFields (forced).2.world.graph.table forceKey 42 ∧
    (replacement).2.memory.effects.keys = OwnedKeys.store (forced).2.world.memory.effects.keys forceKey ⟨8, 42⟩ := ⟨by rfl', by rfl'⟩

theorem replacement_projection : (replacement).2.graph.table = OwnedKeys.view (replacement).2.memory.effects.keys := by
  rw [replacement_tables.1, replacement_tables.2, OwnedKeys.view_store, force_projection]


theorem source_preserved :
    Compiler.ZigAir.Memory.load (found).2.world.memory.memory (source.pointer 0) = .ok (number 3) ∧
    Compiler.ZigAir.Memory.load (replacement).2.memory.memory (source.pointer 1) = .ok (number 1) := ⟨by rfl', by rfl'⟩

theorem find_closed (fail : Bool) (ordinaryResult : ordinary (found fail).1 = true) :
    let executed := found fail
    Good source request.arguments executed.2.world ∧ Closed executed.2.scope ∧
      Interner.Invariant model executed.2.world.graph ∧ Interner.Stable world.graph executed.2.world.graph ∧
      match executed.1 with | .error _ => True | .ok id => executed.2.world.graph.read id = some 42 := by
  have checked := Semantic.Verified.closed (external host) 7 source request.arguments model _ world _
    (production_contract fail).1 ordinaryResult
  generalize executed : Caller.invoke (external host) 7
    (Caller.findBody (external host) 160 7 (actual fail) Caller.Tests.queries source buffer request) world = result at checked
  dsimp only [found, Caller.find]
  rw [executed]
  rcases result with ⟨result, after⟩
  cases result <;> exact checked

theorem success_verified :
    let executed := found
    Good source request.arguments executed.2.world ∧ Closed executed.2.scope ∧
      Interner.Invariant model executed.2.world.graph ∧ Interner.Stable world.graph executed.2.world.graph ∧
      executed.2.world.graph.read 7 = some 42 := by
  have ordinaryResult : ordinary (found).1 = true := by rw [find_success.1]; rfl
  have checked := find_closed false ordinaryResult
  generalize ran : found = result at checked ⊢
  rcases result with ⟨result, after⟩
  have accepted := find_success.1
  rw [ran] at accepted
  dsimp only at accepted
  rw [accepted] at checked
  exact checked

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication.Tests
