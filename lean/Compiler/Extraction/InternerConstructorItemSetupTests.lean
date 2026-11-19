/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorItem
import Compiler.Extraction.InternerCallerNativeRoutingTests
import Compiler.Extraction.AssemblyItemInitializationTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.Tests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion.Native
open CallerGrowingChainTests (parent cells startId lifetime ops allocate growth)
open CallerInputTests (values)

abbrev debug := AssemblyItem.Initializers.Tests.debug
def request (empty : Bool) := Interner.constructorCode.operationRequest 254 (values empty)
def native (empty : Bool) := input (request empty).item debug
def key (empty : Bool) : Key := ⟨1, 254, 0, values empty, 0⟩
def before (safety empty : Bool) := CallerGrowingChainTests.before safety empty 4
def itemSource (empty : Bool) : Compiler.ZigAir.Memory.Address := ⟨startId empty 4, 0⟩
def constructed (safety empty : Bool) := (prepare (request empty).item debug (before safety empty)).2
def stack (safety empty : Bool) :=
  ((Compiler.ZigAir.Memory.allocate (constructed safety empty).memory.memory (.array 2 word)).toOption.getD
    (.pointer (.pointer true false (.array 2 word)) ⟨0, 0⟩, (constructed safety empty).memory.memory)).2
def prepared (safety empty : Bool) := Caller.initLookup (Publication.external ops.arguments) 160 7 (parent empty)
  ⟨startId empty 4 + 1, 0, 2⟩ (request empty)
  ⟨{ constructed safety empty with memory := { (constructed safety empty).memory with memory := stack safety empty } }, { lookup := none }⟩
def taken (safety empty : Bool) := take (Publication.external ops.arguments) 7 (prepared safety empty).2
def normalized (empty : Bool) : ArgumentSlice := ⟨startId empty 4 + 2, values empty⟩
def lookup (empty : Bool) : Handle := ⟨parent empty, values empty, none⟩

def observations (safety empty : Bool) :=
  ((prepare (request empty).item debug (before safety empty)).1,
    (constructed safety empty).memory.memory.nextId,
    Compiler.ZigAir.Memory.allocate (constructed safety empty).memory.memory (.array 2 word),
    (prepared safety empty).1, (taken safety empty).1, (taken safety empty).2.scope,
    (before safety empty).graph.table (key empty))

def expected (safety empty : Bool) :=
  ((Except.ok (itemSource empty) : Except Fault Compiler.ZigAir.Memory.Address),
    startId empty 4 + 1,
    (Except.ok (.pointer (.pointer true false (.array 2 word)) ⟨startId empty 4 + 1, 0⟩, stack safety empty) :
      Except Compiler.ZigAir.Memory.Fault (Compiler.ZigAir.Memory.Value × Compiler.ZigAir.Memory.State)),
    (Except.ok (values empty) : Except Fault (List NodeId)), (Except.ok () : Except Fault Unit),
    Local.mk (some (lookup empty)) (some (normalized empty)) false,
    (none : Option NodeId))

/-- Only actual prefix observations are evaluated. Reached ownership and native
correspondence below are supplied by the universal implementation proofs. -/
theorem observed (safety empty : Bool) : observations safety empty = expected safety empty := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

theorem prefix_results (safety empty : Bool) :
    prepare (request empty).item debug (before safety empty) = (.ok (itemSource empty), constructed safety empty) ∧
    (constructed safety empty).memory.memory.nextId = startId empty 4 + 1 ∧
    Compiler.ZigAir.Memory.allocate (constructed safety empty).memory.memory (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨startId empty 4 + 1, 0⟩, stack safety empty) ∧
    (prepared safety empty).1 = .ok (values empty) ∧
    (taken safety empty).1 = .ok () ∧
    (taken safety empty).2.scope = ⟨some (lookup empty), some (normalized empty), false⟩ ∧
    (before safety empty).graph.table (key empty) = none := by
  have calls := observed safety empty
  simp only [observations, expected, Prod.mk.injEq] at calls
  exact ⟨Prod.ext calls.1 rfl, calls.2⟩

theorem made_key (empty : Bool) : Interner.makeKey (request empty) (values empty) = .ok (key empty) := by
  cases empty <;> rfl

theorem construction (safety empty : Bool) : Prepared (request empty).item debug (before safety empty) (constructed safety empty) :=
  (prepare_success _ _ _ _ _ (CallerGrowingChainTests.initialized_prefix safety empty 4 (by decide)).facts.valid
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide)
    AssemblyItem.Initializers.Tests.debug_valid (prefix_results safety empty).1).2

theorem entry (safety empty : Bool) :
    CallerInput 7 (parent empty) (itemSource empty) (request empty) (values empty) (native empty) (key empty)
      (constructed safety empty) (taken safety empty).2 (normalized empty) (lookup empty) := by
  have prior := CallerGrowingChainTests.initialized_prefix safety empty 4 (by decide)
  have calls := prefix_results safety empty
  have initialized : Caller.initLookup (Publication.external ops.arguments) 160 7 (parent empty)
      ⟨(constructed safety empty).memory.memory.nextId, 0, 2⟩ (request empty)
      ⟨{ constructed safety empty with memory := { (constructed safety empty).memory with memory := stack safety empty } }, { lookup := none }⟩ =
        (.ok (values empty), (prepared safety empty).2) := by
    rw [calls.2.1]
    exact Prod.ext calls.2.2.2.1 rfl
  obtain ⟨slice, remaining, incoming⟩ := caller_input ops.arguments 160 7 (parent empty) (request empty) debug
    (before safety empty) (constructed safety empty) (itemSource empty) (stack safety empty) _ (values empty)
    (prepared safety empty).2 (taken safety empty).2 (key empty) prior.parent_good
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) AssemblyItem.Initializers.Tests.debug_valid
    (Normalization.Tests.external_admitted _) calls.1 calls.2.2.1 initialized (Prod.ext calls.2.2.2.2.1 rfl)
    (made_key empty) prior.facts.live prior.facts.unique (by
      intro old found _ _
      have absent := calls.2.2.2.2.2.2
      simp only [before] at absent found
      rw [prior.facts.linked, OwnedKeys.view, found] at absent
      cases absent)
  have same := Local.mk.inj (incoming.origin.scope.symm.trans calls.2.2.2.2.2.1)
  cases Option.some.inj same.1
  cases Option.some.inj same.2.1
  exact incoming

theorem constructed_graph (safety empty : Bool) :
    CallerGrowingChainTests.GraphFacts safety (lifetime empty) 5 (constructed safety empty) (cells safety empty 4) := by
  have prior := CallerGrowingChainTests.initialized_prefix safety empty 4 (by decide)
  have post := construction safety empty
  exact prior.facts.frame (by rw [prior.count]; decide) post.valid
    ((congrArg Interner.Heap.representatives post.graph).trans prior.facts.projected)
    (congrArg Interner.Heap.table post.graph) (congrArg Publication.Effects.keys post.effects) post.memory
    (by intro id block found; rw [post.heap]; exact found)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.Tests
