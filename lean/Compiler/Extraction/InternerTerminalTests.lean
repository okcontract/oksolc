/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerTerminalProduction
import Compiler.Extraction.InternerQueryCallerTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Terminal.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open Insertion.CallerTests (source request original world buffer select)
open Insertion.Tests (base model ops)

/-- A reached call would invalidate both the graph and the effect observation.
No soundness or simulation contract can be supplied for this callback. -/
def poison : Primitives (Publication.Effects Nat) :=
  { Insertion.CallerTests.seed with simplify := fun _ _ before =>
    let graph := { before.graph with read := fun _ => none }
    let memory := { before.memory with effects := { before.memory.effects with allocator := 999 } }
    (.error (.language .safetyFault), { before with graph, memory }) }

def actual (source : View) (failure : Option Storage.Allocation) :=
  Insertion.graphCallbacks (ops failure) 7 source model select poison

def forceBody (failure : Option Storage.Allocation) :=
  Query.forceBody (Publication.external (ops failure).arguments) 160 7 (actual source failure)
    source buffer 4 request.item request.arguments
def forced (failure : Option Storage.Allocation := none) :=
  Caller.invoke (Publication.external (ops failure).arguments) 7 (forceBody failure) world

theorem force_contract (failure : Option Storage.Allocation) :
    Semantic.Verified (Publication.external (ops failure).arguments) 7 source request.arguments model
      (forceBody failure) world (fun _ _ => True) :=
  force_verified (ops failure) select 160 7 poison source request.item request.arguments 4 original Normalization.Tests.before.memory _
    base 42 Insertion.CallerTests.original_good (by rfl) Normalization.Tests.actual_caller_allocation
    (Insertion.Tests.admitted failure) Insertion.CallerTests.graph_valid (by rfl') (by rfl')

theorem force_publishes_without_recursion : forced.1 = .ok () ∧
    forced.2.world.graph.table ⟨1, 1, 0, [1, 3], 0⟩ = some 4 ∧
    forced.2.world.memory.effects.allocator = 18 ∧ Closed forced.2.scope := by
  exact ⟨by rfl', by rfl', by rfl', by exact ⟨by rfl', Or.inl (by rfl')⟩⟩

theorem force_failure_cleanup : (forced (some .publish)).1 = .error (.language .outOfMemory) ∧
    (forced (some .publish)).2.world.memory.effects.allocator = 184 ∧
    (forced (some .publish)).2.world.memory.heap 5 = none ∧ Closed (forced (some .publish)).2.scope := by
  exact ⟨by rfl', by rfl', by rfl', by exact ⟨by rfl', Or.inr (by rfl')⟩⟩

def emptySource : View := ⟨900, 90, 0⟩
def constantBody (failure : Option Storage.Allocation) (budget := 160) :=
  Query.findBody (Publication.external (ops failure).arguments) budget 7 (actual emptySource failure)
    emptySource buffer (Interner.constructorCode.constantRequest 42)
def constant (failure : Option Storage.Allocation := none) (budget := 160) :=
  Caller.invoke (Publication.external (ops failure).arguments) 7 (constantBody failure budget) world

theorem constant_contract (failure : Option Storage.Allocation) :
    Semantic.Verified (Publication.external (ops failure).arguments) 7 emptySource [] model
      (constantBody failure) world (fun id after => after.read id = some 42) :=
  constant_verified (ops failure) select 160 7 poison emptySource original Normalization.Tests.before.memory _
    base 42 (fun _ => rfl) ⟨Insertion.CallerTests.original_good.1, by simp [Represents, emptySource]⟩
    (by rfl) Normalization.Tests.actual_caller_allocation (Insertion.Tests.admitted failure) Insertion.CallerTests.graph_valid

theorem constant_inserts_without_recursion : constant.1 = .ok 5 ∧ constant.2.world.graph.read 5 = some 42 ∧
    constant.2.world.graph.table ⟨2, 0, 42, [], 0⟩ = some 5 ∧ Closed constant.2.scope := by
  exact ⟨by rfl', by rfl', by rfl', by exact ⟨by rfl', Or.inl (by rfl')⟩⟩

theorem constant_failure_cleanup (failure : Storage.Allocation)
    (supported : failure = .item ∨ failure = .append ∨ failure = .publish) :
    (constant (some failure)).1 = .error (.language .outOfMemory) ∧
    (constant (some failure)).2.world.graph.representatives = original.graph.representatives ∧
    Closed (constant (some failure)).2.scope := by
  rcases supported with rfl | rfl | rfl
  all_goals exact ⟨by rfl', by rfl', by exact ⟨by rfl', Or.inl (by rfl')⟩⟩

theorem empty_arguments_skip_allocation : (constant (some .arguments)).1 = .ok 5 := by rfl'

theorem constant_needs_no_sort_fuel : (constant none 0).1 = .ok 5 := by rfl'

theorem force_sort_cutoff_rejected :
    ordinary (Caller.invoke (Publication.external (ops none).arguments) 7
      (Query.forceBody (Publication.external (ops none).arguments) 0 7 (actual source none)
        source buffer 4 request.item request.arguments) world).1 = false := by rfl'

theorem operation_reaches_poison :
    (Caller.invoke (Publication.external (ops none).arguments) 7
      (Query.findBody (Publication.external (ops none).arguments) 160 7 (actual source none) source buffer request) world).1 =
      .error (.language .safetyFault) := by rfl'

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Terminal.Tests
