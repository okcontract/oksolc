/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.CallerTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open Tests (model push)

def cells := [push 0, push 10, push 20, push 32, push 42]
def heap := Interner.observedHeap cells (fun _ => none)
def source := Semantic.Tests.source
def request := Semantic.Tests.request
def original : World (Publication.Effects Nat) := ⟨heap, ⟨Normalization.Tests.original.heap, Normalization.Tests.original.memory,
  ⟨fun _ => none, 0⟩⟩⟩
def world : World (Publication.Effects Nat) := { original with memory := { original.memory with memory := Normalization.Tests.before.memory } }
def buffer : View := ⟨3, 0, 2⟩
def select (key : Key) (_ : World (Publication.Effects Nat)) : AssemblyClone.Value Nat :=
  ⟨⟨key.kind, if key.kind = 1 then some key.instruction else none, key.data⟩, 0, none⟩
def seed : Primitives (Publication.Effects Nat) where
  simplify := fun _ _ before => (.ok none, before)
  publish := fun _ _ _ before => (.error (.language .unsupported), before)
  insert := fun _ _ _ before => (.error (.language .unsupported), before)
def ops (failure : Option Storage.Allocation := none) := Tests.ops failure
def actual (failure : Option Storage.Allocation := none) := graphCallbacks (ops failure) 7 source model select seed
def found (failure : Option Storage.Allocation := none) :=
  Caller.find (Publication.external (ops failure).arguments) 160 7 (actual failure) Caller.Tests.queries source buffer request world
def forced (failure : Option Storage.Allocation := none) :=
  Caller.force (Publication.external (ops failure).arguments) 160 7 (actual failure) Caller.Tests.queries source buffer 4 request.item request.arguments world

theorem original_good : Good source request.arguments original :=
  ⟨⟨Normalization.Tests.original_valid.memory, Normalization.Tests.original_valid.related,
    Normalization.Tests.original_valid.injected⟩, Semantic.Tests.source_represented⟩
theorem prepared : Good source request.arguments world ∧
    (∀ commutative : Bool, commutative = true → 2 ≤ source.length → source.length ≤ buffer.length → Scratch source buffer world.memory) := by
  obtain ⟨valid, represented, scratch, _⟩ := caller_buffer original.memory Normalization.Tests.before.memory _ source request.arguments
    original_good.1 original_good.2 Normalization.Tests.actual_caller_allocation
  exact ⟨⟨valid, represented⟩, scratch⟩
theorem graph_valid : Interner.Invariant model heap := by
  refine ⟨?_, rfl, ?_⟩
  · intro _ _ impossible; cases impossible
  · simp [Storage.Coherent, cells, push, Cache.Item.eval, Cache.readArguments, Tests.model,
      Folding.wordMeaning, Storage.Cell.value, Storage.Cell.isPush, Storage.Cell.dataValue, Tests.base]

theorem contracts (failure : Option Storage.Allocation) :
    OwnedCall.Contracts 7 source request.arguments (actual failure) ∧
    Semantic.Contracts 7 source request.arguments model (actual failure) := by
  have graph := graph_contracts (ops failure) 7 source request.arguments model select seed (Tests.admitted failure)
  refine ⟨⟨graph.1, ?_⟩, ⟨graph.2, ?_⟩⟩
  · intro _ _ _ _ held _; exact held
  · intro _ _ before _ _ _ _ valid _
    exact Semantic.Ensures.pure model before.graph none _ valid (fun _ impossible => by cases impossible)

/-- Complete normalization, sort, transfer, insertion/publication and cleanup
clients of the new graph contracts. Simplification deliberately returns no
rewrite here; the general production theorem separately uses the dispatcher. -/
theorem caller_verified (failure : Option Storage.Allocation) :
    Semantic.Verified (Publication.external (ops failure).arguments) 7 source request.arguments model
      (Caller.findBody (Publication.external (ops failure).arguments) 160 7 (actual failure) Caller.Tests.queries source buffer request)
      world (fun id after => after.read id = some 42) ∧
    Semantic.Verified (Publication.external (ops failure).arguments) 7 source request.arguments model
      (Caller.forceBody (Publication.external (ops failure).arguments) 160 7 (actual failure) Caller.Tests.queries source buffer 4 request.item request.arguments)
      world (fun _ _ => True) := by
  exact ⟨Semantic.find_verified _ 160 7 (actual failure) _ source buffer request world Tests.base 42 prepared.1 prepared.2
    (Publication.external_admitted _ (Tests.admitted failure)) (contracts failure).1 (contracts failure).2 graph_valid (by rfl'),
    Semantic.force_verified _ 160 7 (actual failure) _ source buffer 4 request.item request.arguments world Tests.base 42 prepared.1 prepared.2
      (Publication.external_admitted _ (Tests.admitted failure)) (contracts failure).1 (contracts failure).2.toGraphContracts graph_valid (by rfl') (by rfl')⟩

theorem find_success : found.1 = .ok 5 ∧ found.2.world.graph.read 5 = some 42 ∧
    found.2.world.memory.effects.allocator = 11578 ∧ found.2.world.memory.heap 5 = some ⟨7, .arguments [1, 3]⟩ ∧
    found.2.world.memory.heap 6 = some ⟨7, .arguments [1, 3]⟩ := ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩
theorem find_rollback : (found (some .publish)).1 = .error (.language .outOfMemory) ∧
    (found (some .publish)).2.world.graph.representatives = some cells ∧
    (found (some .publish)).2.world.memory.effects.allocator = 11578344 ∧
    (found (some .publish)).2.world.memory.heap 5 = none ∧
    (found (some .publish)).2.world.memory.heap 6 = none ∧
    (found (some .publish)).2.world.memory.memory.heap.lookup 7 = none :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩
theorem force_success : forced.1 = .ok () ∧ forced.2.world.memory.effects.allocator = 18 ∧
    forced.2.world.memory.effects.keys ⟨1, 1, 0, [1, 3], 0⟩ = some ⟨5, 4⟩ := ⟨by rfl', by rfl', by rfl'⟩
theorem force_oom : (forced (some .publish)).1 = .error (.language .outOfMemory) ∧
    (forced (some .publish)).2.world.memory.effects.allocator = 184 ∧
    (forced (some .publish)).2.world.memory.heap 5 = none := ⟨by rfl', by rfl', by rfl'⟩

theorem find_closed : Good source request.arguments found.2.world ∧ Closed found.2.scope ∧
    Interner.Invariant model found.2.world.graph ∧ Interner.Stable world.graph found.2.world.graph ∧
    found.2.world.graph.read 5 = some 42 := by
  have completed : ordinary found.1 = true := by rw [find_success.1]; rfl
  have checked := Semantic.Verified.closed _ 7 source request.arguments model _ world _ (caller_verified none).1 completed
  have same : Caller.invoke (Publication.external (ops).arguments) 7
      (Caller.findBody (Publication.external (ops).arguments) 160 7 (actual) Caller.Tests.queries source buffer request) world = found := rfl
  rw [same] at checked
  simpa only [find_success.1] using checked

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.CallerTests
