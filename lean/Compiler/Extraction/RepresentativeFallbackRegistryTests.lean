/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeFallbackRegistry
import Compiler.Extraction.RepresentativeFirstRegistryTests

namespace Compiler.Extraction.RepresentativeArray.DescriptorRelation.FallbackRegistryTests
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

def before (runtimeSafety : Bool) : Session Backing.Release.Tests.Effects := {Tests.before runtimeSafety with
  heap := Compiler.Extraction.Memory.write (Tests.before runtimeSafety).heap 2 (some ⟨7, .representatives Tests.nodes⟩) }
def request (response : Option Nat := some 640) : Backing.Registry.Allocate Backing.Release.Tests.Effects :=
  Backing.Fallback.Tests.request response
def external := Backing.Release.Tests.external

theorem initial_valid (runtimeSafety : Bool) : Valid (before runtimeSafety) :=
  Backing.Registry.vector_write_valid (Tests.before runtimeSafety) 7 2 (Tests.backing Tests.allCells) Tests.nodes
    (Tests.initial_valid runtimeSafety) (by cases runtimeSafety <;> rfl) rfl

theorem source_owned (runtimeSafety : Bool) : Backing.Release.Owned 7 ⟨2, 0⟩ 3 (before runtimeSafety) :=
  ⟨rfl, ⟨Tests.nodes, rfl⟩, Tests.backing Tests.allCells, by cases runtimeSafety <;> rfl, rfl, rfl, rfl⟩

theorem registered_move (runtimeSafety : Bool) : ∃ raw after : Session Backing.Release.Tests.Effects,
    Backing.Fallback.run request external 7 ⟨3, 16⟩ ⟨2, 0⟩ 3 5 (before runtimeSafety) = (.ok (some ()), raw) ∧
    after.memory = raw.memory ∧ after.effects = raw.effects ∧
    Compiler.Extraction.Memory.Vector 7 raw.heap 4 [] ∧
    Compiler.Extraction.Memory.moveVector (before runtimeSafety).heap 7 2 4 true = .ok after.heap ∧
    Valid after ∧ Compiler.Extraction.Memory.Vector 7 after.heap 4 Tests.nodes ∧
    Backing.Release.Owned 7 ⟨4, 0⟩ 5 after ∧ after.heap 2 = none ∧ after.memory.heap.lookup 2 = none ∧
    Prefix after.memory 4 Tests.nodes ∧ after.memory.nextId = 5 ∧
    after.effects = [(7, 0, 96, 8), (7, 0, 160, 8), (7, 512, 96, 8)] ∧
    (∀ id, representativeFields after.memory ⟨3, 16⟩ id =
      .ok ((Storage.representativeProgram.run Tests.nodes id).map (values id.toNat))) := by
  obtain ⟨oldCell, raw, after, oldFound, executed, memory, effects, heap, moved, reached, valid, vector, owned,
      oldDead, nativeDead, _, represented, nextId, _, queries, _⟩ :=
    fallback_registered runtimeSafety request external 7 3 2 3 5 640 (before runtimeSafety) _ (Backing.Relocation.Tests.owner runtimeSafety)
      Tests.nodes (initial_valid runtimeSafety) (by cases runtimeSafety <;> rfl) rfl rfl (source_owned runtimeSafety) rfl
      (by decide) (by decide) (by decide) (by decide) rfl (Tests.fits runtimeSafety) (by cases runtimeSafety <;> rfl)
      (Tests.prefix_from_initialization runtimeSafety)
  have same : oldCell = Tests.backing Tests.allCells := Option.some.inj
    (oldFound.symm.trans (by cases runtimeSafety <;> rfl))
  subst oldCell
  refine ⟨raw, after, executed, memory, effects, ?_, moved, valid, vector, owned, oldDead, nativeDead, represented, nextId, reached, queries⟩
  simp only [Compiler.Extraction.Memory.Vector, heap, before, Tests.before, Tests.memory,
    Backing.Fallback.Tests.before, Compiler.Extraction.Memory.write, ↓reduceIte]
  rfl

theorem raw_is_provisional (runtimeSafety : Bool) : ∃ raw,
    Backing.Fallback.run request external 7 ⟨3, 16⟩ ⟨2, 0⟩ 3 5 (before runtimeSafety) = (.ok (some ()), raw) ∧
    Prefix raw.memory 4 Tests.nodes ∧ ¬Compiler.Extraction.Memory.Vector 7 raw.heap 4 Tests.nodes := by
  obtain ⟨raw, after, executed, memory, _, provisional, _, _, _, _, _, _, represented, _⟩ := registered_move runtimeSafety
  refine ⟨raw, executed, memory ▸ represented, ?_⟩
  intro complete
  have wrong := provisional.symm.trans complete
  cases wrong

theorem every_outcome_valid (runtimeSafety : Bool) (allocator oldCapacity : Nat) (oldData : Address) (response : Option Nat) :
    Valid (Backing.Fallback.run (request response) external allocator ⟨3, 16⟩ oldData oldCapacity 5 (before runtimeSafety)).2 :=
  (Backing.Fallback.storage runtimeSafety (request response) external allocator 3 oldCapacity 5 oldData (before runtimeSafety)
    (Backing.Relocation.Tests.owner runtimeSafety) (initial_valid runtimeSafety) (by decide) (by cases runtimeSafety <;> rfl) rfl).1

theorem parent_offset (runtimeSafety : Bool) (allocator oldCapacity : Nat) (oldData : Address) (response : Option Nat) :
    WordArray.Represents (Backing.Fallback.run (request response) external allocator ⟨3, 16⟩ oldData oldCapacity 5
      (before runtimeSafety)).2.memory ⟨1, 1, 2⟩ [99, 1] :=
  (Backing.Fallback.parent_borrow runtimeSafety (request response) external allocator 3 oldCapacity 5 oldData (before runtimeSafety)
    (Backing.Relocation.Tests.owner runtimeSafety) (initial_valid runtimeSafety) (by decide) (by cases runtimeSafety <;> rfl) rfl
    ⟨1, 1, 2⟩ [99, 1] 4 Expression.Tests.argumentsAllocation (by cases runtimeSafety <;> rfl) rfl
    (Tests.offset_borrow_still_live runtimeSafety)).2

theorem oom_keeps_vector (runtimeSafety : Bool) (header oldData : Address) :
    Backing.Fallback.run (request none) external 7 header oldData 3 5 (before runtimeSafety) =
      (.ok none, {before runtimeSafety with effects := [(7, 0, 96, 8), (7, 0, 160, 8)]}) ∧
    Compiler.Extraction.Memory.moveVector (before runtimeSafety).heap 7 2 4 false = .error .outOfMemory ∧
    Valid ({before runtimeSafety with effects := [(7, 0, 96, 8), (7, 0, 160, 8)]} : Session Backing.Release.Tests.Effects) ∧
    Compiler.Extraction.Memory.Vector 7 (before runtimeSafety).heap 2 Tests.nodes ∧ (before runtimeSafety).heap 4 = none :=
  fallback_registry_oom (request none) external 7 2 3 5 header oldData (before runtimeSafety) _ Tests.nodes
    (initial_valid runtimeSafety) rfl (by decide) (by decide) rfl

theorem wrong_vector_rejects (runtimeSafety : Bool) :
    ¬Compiler.Extraction.Memory.Vector 7 (before runtimeSafety).heap 2 [] ∧
    ¬Compiler.Extraction.Memory.Vector 8 (before runtimeSafety).heap 2 Tests.nodes := by
  constructor <;> intro wrong <;> cases wrong

def damaged (runtimeSafety : Bool) : Session Backing.Release.Tests.Effects := {before runtimeSafety with
  memory := (Backing.Fallback.Tests.damaged runtimeSafety).memory }
def copyReached (runtimeSafety : Bool) : Session Backing.Release.Tests.Effects := {Backing.Fallback.Tests.copyPrefix runtimeSafety with
  heap := Compiler.Extraction.Memory.write (damaged runtimeSafety).heap 4 (some ⟨7, .representatives []⟩) }

theorem partial_copy_execution (runtimeSafety : Bool) :
    Backing.Fallback.run request external 7 ⟨3, 16⟩ ⟨2, 0⟩ 3 5 (damaged runtimeSafety) =
      (.error (.memory .uninitialized), copyReached runtimeSafety) := by cases runtimeSafety <;> rfl

theorem partial_copy_is_not_move (runtimeSafety : Bool) :
    Compiler.Extraction.Memory.Vector 7 (copyReached runtimeSafety).heap 2 Tests.nodes ∧
    Compiler.Extraction.Memory.Vector 7 (copyReached runtimeSafety).heap 4 [] ∧
    (copyReached runtimeSafety).effects = [(7, 0, 96, 8), (7, 0, 160, 8)] ∧
    ¬Prefix (copyReached runtimeSafety).memory 4 Tests.nodes ∧
    Compiler.Extraction.Memory.moveVector (damaged runtimeSafety).heap 7 2 4 true ≠ .ok (copyReached runtimeSafety).heap := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · intro represented
    have rejected : ¬Row (copyReached runtimeSafety).memory 4 0 Tests.first := by
      simp only [Row]; cases runtimeSafety <;> decide
    exact rejected (represented 0 Tests.first rfl)
  · intro moved
    have expected := Compiler.Extraction.Memory.move_vector_eq 7 (damaged runtimeSafety).heap 2 4 Tests.nodes rfl rfl
    have same := congrArg (fun heap => heap 2) (Except.ok.inj (moved.symm.trans expected))
    cases same

def readonly (runtimeSafety : Bool) : Session Backing.Release.Tests.Effects := {before runtimeSafety with
  memory := {(before runtimeSafety).memory with
    heap := (before runtimeSafety).memory.heap.replace 3 {(Backing.Relocation.Tests.owner runtimeSafety) with writable := false}} }
def readonlyReserved (runtimeSafety : Bool) : Session Backing.Release.Tests.Effects := {readonly runtimeSafety with
  heap := Compiler.Extraction.Memory.write (readonly runtimeSafety).heap 4 (some ⟨7, .representatives []⟩)
  memory := RegionAllocation.extend (readonly runtimeSafety).memory (Backing.type 5) 160 640
  effects := [(7, 0, 96, 8), (7, 0, 160, 8)] }
def readonlyCopied (runtimeSafety : Bool) : Session Backing.Release.Tests.Effects := {readonlyReserved runtimeSafety with
  memory := {(readonlyReserved runtimeSafety).memory with
    heap := (readonlyReserved runtimeSafety).memory.heap.replace 4 {RepresentativeArray.Copy.Tests.targetCell with cells := Tests.allCells}} }
def readonlyFirst (runtimeSafety : Bool) : State := {(readonlyReserved runtimeSafety).memory with
  heap := (readonlyReserved runtimeSafety).memory.heap.replace 4 {RepresentativeArray.Copy.Tests.targetCell with cells := Tests.firstCells} }
def readonlyReleased (runtimeSafety : Bool) : Session Backing.Release.Tests.Effects :=
  ⟨Compiler.Extraction.Memory.write (readonlyCopied runtimeSafety).heap 2 none,
    erase (readonlyCopied runtimeSafety).memory 2, [(7, 0, 96, 8), (7, 0, 160, 8), (7, 512, 96, 8)]⟩

theorem readonly_reservation (runtimeSafety : Bool) : Backing.Registry.run request 7 5 (readonly runtimeSafety) =
    (.ok (some ⟨4, 0⟩), readonlyReserved runtimeSafety) := by cases runtimeSafety <;> rfl

theorem readonly_first_copy (runtimeSafety : Bool) : RepresentativeArray.Copy.fields expressionSlots ⟨2, 0⟩ ⟨4, 0⟩
    (readonlyReserved runtimeSafety).memory = (.ok (), readonlyFirst runtimeSafety) := by cases runtimeSafety <;> rfl
theorem readonly_second_copy (runtimeSafety : Bool) : RepresentativeArray.Copy.fields expressionSlots ⟨2, 32⟩ ⟨4, 32⟩
    (readonlyFirst runtimeSafety) = (.ok (), (readonlyCopied runtimeSafety).memory) := by cases runtimeSafety <;> rfl
theorem readonly_copy (runtimeSafety : Bool) : Backing.RegisteredCopy.run 2 4 2 (readonlyReserved runtimeSafety) =
    (.ok (), readonlyCopied runtimeSafety) := by
  simp only [Backing.RegisteredCopy.run, RepresentativeArray.Copy.run, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 4 by decide,
    ↓reduceIte, RepresentativeArray.Copy.copyFrom, Nat.zero_mul, Nat.reduceAdd, Nat.reduceMul, readonly_first_copy, readonly_second_copy]
  rfl

theorem readonly_release (runtimeSafety : Bool) : Backing.Release.run external 7 ⟨2, 0⟩ 3 (readonlyCopied runtimeSafety) =
    (.ok (), readonlyReleased runtimeSafety) := by cases runtimeSafety <;> rfl

theorem readonly_publication (runtimeSafety : Bool) : Publication.Registered.run ⟨3, 16⟩ ⟨4, 0⟩ 5 (readonlyReleased runtimeSafety) =
    (.error .readOnly, readonlyReleased runtimeSafety) := by cases runtimeSafety <;> rfl

theorem publication_fault_execution (runtimeSafety : Bool) :
    Backing.Fallback.run request external 7 ⟨3, 16⟩ ⟨2, 0⟩ 3 5 (readonly runtimeSafety) =
      (.error (.memory .readOnly), readonlyReleased runtimeSafety) := by
  have loaded : readItems (readonlyReserved runtimeSafety).memory ⟨3, 16⟩ = .ok (.slice itemsType ⟨2, 0⟩ 2) := by
    cases runtimeSafety <;> rfl
  simp only [Backing.Fallback.run, readonly_reservation, Backing.Relocation.run, loaded, ne_self_iff_false, ↓reduceIte, and_false, or_self,
    readonly_copy, Backing.Relocation.finish, readonly_release, readonly_publication, Except.mapError, Except.map]

theorem publication_fault_keeps_release (runtimeSafety : Bool) :
    let outcome := Backing.Fallback.run request external 7 ⟨3, 16⟩ ⟨2, 0⟩ 3 5 (readonly runtimeSafety)
    outcome.1 = .error (.memory .readOnly) ∧ outcome.2.heap 2 = none ∧ outcome.2.memory.heap.lookup 2 = none ∧
      Compiler.Extraction.Memory.Vector 7 outcome.2.heap 4 [] ∧
      outcome.2.effects = [(7, 0, 96, 8), (7, 0, 160, 8), (7, 512, 96, 8)] ∧
      readHeader outcome.2.memory ⟨3, 16⟩ = .ok (.slice itemsType ⟨2, 0⟩ 2, .scalar (.int false 64 3)) := by
  rw [publication_fault_execution]
  cases runtimeSafety <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem publication_fault_is_not_move (runtimeSafety : Bool) :
    let outcome := Backing.Fallback.run request external 7 ⟨3, 16⟩ ⟨2, 0⟩ 3 5 (readonly runtimeSafety)
    Compiler.Extraction.Memory.moveVector (readonly runtimeSafety).heap 7 2 4 true ≠ .ok outcome.2.heap := by
  dsimp only
  intro moved
  have expected := Compiler.Extraction.Memory.move_vector_eq 7 (readonly runtimeSafety).heap 2 4 Tests.nodes rfl rfl
  have same := congrArg (fun heap => heap 4) (Except.ok.inj (moved.symm.trans expected))
  have provisional := (publication_fault_keeps_release runtimeSafety).2.2.2.1
  dsimp only [Compiler.Extraction.Memory.Vector] at provisional
  dsimp only at same
  rw [provisional] at same
  cases same

end Compiler.Extraction.RepresentativeArray.DescriptorRelation.FallbackRegistryTests
