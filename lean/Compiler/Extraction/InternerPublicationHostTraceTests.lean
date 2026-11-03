/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPublicationHostTrace
import Compiler.Extraction.InternerPhysicalDispatchEffects
import Compiler.Extraction.InternerPublicationTests
import Compiler.Extraction.NormalizationHostTraceTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication.Recording.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open Normalization.HostTrace Publication.Tests

def capture (before : World (Effects Nat)) :=
  before.mapEffects (Effects.mapAllocator (fun effects => (⟨effects, []⟩ : Recorded Nat)))

theorem capture_erases (before : World (Effects Nat)) :
    (capture before).mapEffects (Effects.mapAllocator Recorded.effects) = before := rfl

def replacement (fail : Bool) := Publication.publish (recordProbe (attempt fail)) (record host) 7 source
  forceKey ⟨8, [1, 3]⟩ 42 (capture publicationWorld)

theorem replacement_erases (fail : Bool) : Publication.Tests.replacement fail =
    ((replacement fail).1, (replacement fail).2.mapEffects (Effects.mapAllocator Recorded.effects)) := by
  have erased := publish_erases (attempt fail) host 7 source forceKey ⟨8, [1, 3]⟩ 42 (capture publicationWorld)
  rw [capture_erases] at erased
  exact erased

theorem replacement_events : (replacement false).2.memory.effects.allocator.events =
    [.publicationProbe forceKey true, .free ⟨5, [1, 3]⟩] := by rfl'

theorem replacement_reached : (replacement false).1 = .ok () ∧
    (replacement false).2.memory.effects.keys forceKey = some ⟨8, 42⟩ ∧
    (replacement false).2.memory.memory.heap.lookup 5 = none ∧
    (replacement false).2.memory.effects.allocator.effects = 125 := ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem refused_probe : (replacement true).1 = .error (.language .outOfMemory) ∧
    (replacement true).2.memory.effects.allocator = (⟨23, [.publicationProbe forceKey false]⟩ : Recorded Nat) ∧
    (replacement true).2.memory.effects.keys forceKey = some ⟨5, 42⟩ := ⟨by rfl', by rfl', by rfl'⟩

def missing := Publication.publish (recordProbe (attempt false)) (record host) 7 source
  forceKey ⟨8, [1, 3]⟩ 42
    (capture { publicationWorld with memory := { publicationWorld.memory with
      memory := Compiler.ZigAir.Memory.erase publicationWorld.memory.memory 5 } })

theorem release_fault_keeps_probe : missing.1 = .error (.memory (.release (.memory .unallocated))) ∧
    missing.2.memory.effects.allocator = (⟨23, [.publicationProbe forceKey true]⟩ : Recorded Nat) ∧
    missing.2.memory.effects.keys forceKey = some ⟨5, 42⟩ := ⟨by rfl', by rfl', by rfl'⟩

theorem admission_rejects_before_probe :
    (Publication.publish (recordProbe (attempt false)) (record host) 7 source forceKey ⟨8, []⟩ 42
      (capture publicationWorld)) = (.error (.language .safetyFault), capture publicationWorld) := by rfl'

theorem empty_key_skips_native_release :
    let before := OwnedKeys.Physical.Tests.empty.mapEffects (fun effects => (⟨effects, []⟩ : Recorded Nat))
    let execution := OwnedKeys.Physical.run (recordProbe (OwnedKeys.Physical.Tests.probe false))
      (record OwnedKeys.Physical.Tests.external) 7 OwnedKeys.Physical.Tests.emptyKey ⟨2, 5⟩ before
    execution.1 = .ok () ∧ execution.2.memory.effects.events = [.publicationProbe OwnedKeys.Physical.Tests.emptyKey true] :=
  ⟨by rfl', by rfl'⟩

theorem replacement_prefix (leading : List Event) :
    Publication.publish (recordProbe (attempt false)) (record host) 7 source forceKey ⟨8, [1, 3]⟩ 42
        ((capture publicationWorld).mapEffects (Effects.mapAllocator (prepend leading))) =
      ((replacement false).1, (replacement false).2.mapEffects (Effects.mapAllocator (prepend leading))) :=
  publish_prefix (attempt false) host 7 source forceKey ⟨8, [1, 3]⟩ 42 leading (capture publicationWorld)

/-- This generalizes the existing logical-constructor fixture's private effect
update, not its semantics. It remains a fixture and claims no native recursion. -/
theorem fixture_child_transport (project : σ → τ) (left : σ → σ) (right : τ → τ)
    (advances : ∀ effects, right (project effects) = project (left effects)) (request : Interner.Request) :
    Effect.Transport (World.mapEffects (Effects.mapAllocator project))
      (physicalFindWith left request) (physicalFindWith right request) := by
  intro before
  dsimp only [physicalFindWith, World.mapEffects, Session.mapEffects, Effects.mapAllocator]
  rw [advances]

def advance (before : Recorded Nat) : Recorded Nat := { before with effects := before.effects + 1 }
def child := physicalFindWith advance
def recordedSeed := seedFor (Recorded Nat)
def recursiveSeed := Recursive.callbacks recordedSeed Compiler.Extraction.Recursive.Tests.reads 64 child
def ordinarySeed := Recursive.callbacks seed Compiler.Extraction.Recursive.Tests.reads 64 physicalFind

theorem simplify_transport (key : Key) (slice : ArgumentSlice) :
    Effect.Transport (World.mapEffects (Effects.mapAllocator Recorded.effects))
      (recursiveSeed.simplify key slice) (ordinarySeed.simplify key slice) :=
  Recursive.simplify_erases (Effects.mapAllocator Recorded.effects) child physicalFind
    (fixture_child_transport Recorded.effects advance (fun effects => effects + 1) (fun _ => rfl))
    recordedSeed seed Compiler.Extraction.Recursive.Tests.reads 64 key slice

def found (fail : Bool) := Caller.find (external (record host)) 160 7
  (callbacks (recordProbe (attempt fail)) (record host) 7 source recursiveSeed)
  Caller.Tests.queries source buffer request (capture world)

/-- The old complete caller specializes the publication composition; neither
its dispatcher nor its actual publication is replaced with a result fixture. -/
theorem caller_erases (fail : Bool) : Publication.Tests.found fail =
    ((found fail).1, (found fail).2.mapEffects (Effects.mapAllocator Recorded.effects)) :=
  find_erases (attempt fail) host 160 7 source buffer simplify_transport (fun _ _ _ _ => rfl)
    Caller.Tests.queries request (capture world)

theorem caller_success : (found false).1 = .ok 7 ∧
    (found false).2.world.memory.effects.keys findKey = some ⟨5, 7⟩ ∧
    (found false).2.world.memory.effects.allocator.effects = 15 ∧
    (found false).2.scope.handedOff = true := ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem caller_oom_cleanup : (found true).1 = .error (.language .outOfMemory) ∧
    (found true).2.world.memory.effects.allocator.effects = 117 ∧
    (found true).2.scope = ⟨none, none, false⟩ := ⟨by rfl', by rfl', by rfl'⟩

theorem caller_success_events : (found false).2.world.memory.effects.allocator.events =
    [.allocate .duplicate 8 (some 76), .publicationProbe findKey true] := by rfl'

theorem caller_oom_events : (found true).2.world.memory.effects.allocator.events =
    [.allocate .duplicate 8 (some 76), .publicationProbe findKey false, .free ⟨5, [1, 3]⟩] := by rfl'

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication.Recording.Tests
