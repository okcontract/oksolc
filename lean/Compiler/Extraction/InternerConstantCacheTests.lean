/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeConstantTests
import Compiler.Extraction.InternerConstantPublicationTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ConstantCacheTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops growth GraphFacts)
open RecursiveTests (Call debug)

def before (safety : Bool) (value : Word) := ConstantPublicationTests.ready safety value RecursiveNonemptyTests.failing (some growth)
def call (safety : Bool) (value : Word) : Call := ⟨Interner.constructorCode.constantRequest value, ⟨0, 0, 0⟩, before safety value⟩

/-- A capacity witness only: allocation transports its address bound, while
all actual input cells and lifetime identifiers come from the reached world. -/
def reference (safety : Bool) : Compiler.ZigAir.Memory.State := ⟨[], 0, ConstantPublicationTests.publishedAddress safety⟩
def allocatedReference (safety : Bool) :=
  ((Compiler.ZigAir.Memory.allocate (reference safety) AssemblyItem.viewType).toOption.map Prod.snd).getD (reference safety)
def scratchReference (safety : Bool) :=
  ((Compiler.ZigAir.Memory.allocate (allocatedReference safety) (.array 2 word)).toOption.map Prod.snd).getD (allocatedReference safety)

theorem allocations (safety : Bool) :
    (reference safety).valid = true ∧
    Compiler.ZigAir.Memory.allocate (reference safety) AssemblyItem.viewType =
      .ok (.pointer (.pointer true false AssemblyItem.viewType) ⟨0, 0⟩, allocatedReference safety) ∧
    Compiler.ZigAir.Memory.allocate (allocatedReference safety) (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨1, 0⟩, scratchReference safety) := by
  cases safety <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

attribute [local irreducible] before ConstantPublicationTests.ready

theorem prepared (safety : Bool) (value : Word) :
    prepare (call safety value).request.item debug (before safety value) =
      (.ok (call safety value).address, (call safety value).constructed) ∧
    Prepared (call safety value).request.item debug (before safety value) (call safety value).constructed ∧
    (call safety value).constructed.memory.memory.nextAddress = (allocatedReference safety).nextAddress := by
  have prior := ConstantPublicationTests.contract safety value RecursiveNonemptyTests.failing (some growth)
  have address : (before safety value).memory.memory.nextAddress = (reference safety).nextAddress := by
    simpa only [before, reference] using prior.2.2.2.2.2.2.1
  have valid : Valid (before safety value).memory := by
    simpa only [before] using prior.2.1.valid
  obtain ⟨pointer, allocated, ran, allocatedCounter⟩ := Compiler.ZigAir.Memory.allocate_at_same_address _ _ _
    valid.memory (allocations safety).1 address _ _ (allocations safety).2.1
  obtain ⟨after, made, post⟩ := prepare_verified (call safety value).request.item debug (before safety value)
    pointer allocated valid (by change (2 : Int) ∈ AssemblyItem.itemTagValues; decide)
    AssemblyItem.Initializers.Tests.debug_valid ran
  have same : after = (call safety value).constructed := (congrArg Prod.snd made).symm
  rw [same] at made post
  obtain ⟨p, memory, allocation, counter⟩ := post.allocation
  have sameMemory : memory = allocated := congrArg Prod.snd (Except.ok.inj (allocation.symm.trans ran))
  exact ⟨made, post, counter.trans ((congrArg Compiler.ZigAir.Memory.State.nextAddress sameMemory).trans allocatedCounter)⟩

theorem stack (safety : Bool) (value : Word) :
    Compiler.ZigAir.Memory.allocate (call safety value).constructed.memory.memory (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨(before safety value).memory.memory.nextId + 1, 0⟩,
        (call safety value).stack) ∧
    (call safety value).stack.nextAddress = (scratchReference safety).nextAddress := by
  have current := prepared safety value
  have valid := Compiler.ZigAir.Memory.allocate_preserves_valid _ _ _ _ (allocations safety).2.1
  obtain ⟨pointer, scratch, ran, counter⟩ := Compiler.ZigAir.Memory.allocate_at_same_address _ _ _ current.2.1.valid.memory
    valid current.2.2 _ _ (allocations safety).2.2
  have shape := Compiler.ZigAir.Memory.allocate_pointer _ _ _ _ ran
  have sameStack : (call safety value).stack = scratch := by
    unfold Call.stack; rw [ran]; rfl
  rw [shape.1, current.2.1.nextId, ← sameStack] at ran
  exact ⟨ran, (congrArg Compiler.ZigAir.Memory.State.nextAddress sameStack).trans counter⟩

attribute [local irreducible] Call.constructed Call.stack

theorem initialized (safety : Bool) (value : Word) :
    (call safety value).prepared =
      (.ok [], ⟨{ (call safety value).constructed with memory :=
        { (call safety value).constructed.memory with memory := (call safety value).stack } },
        { lookup := some ⟨(call safety value).source, [], none⟩ }⟩) := by
  have commutative : Interner.Scoped.commutative (call safety value).request.item = .ok false := rfl
  simp only [Call.prepared, Caller.initLookup, commutative, init, Bool.not_false, Bool.true_or, ↓reduceIte]
  rfl

def entered (safety : Bool) (value : Word) :=
  { (call safety value).constructed with memory := { (call safety value).constructed.memory with memory := (call safety value).stack } }

theorem room (safety : Bool) (value : Word) :
    Interner.Queries.queries.atCapacity (call safety value).constructed.graph = false := by
  have facts : GraphFacts safety ReachablePrefixTests.backing 5 (before safety value) (ConstantPublicationTests.rows safety value) := by
    simpa only [before] using (ConstantPublicationTests.contract safety value RecursiveNonemptyTests.failing (some growth)).2.1
  have projected := (congrArg Interner.Heap.representatives (prepared safety value).2.1.graph).trans facts.projected
  rw [Interner.Queries.capacity_exact _ _ projected, ConstantPublicationTests.rows_count]
  decide

theorem selected (safety : Bool) (value : Word) :
    (call safety value).constructed.graph.table (call safety value).key = some 4 := by
  have prior := (ConstantPublicationTests.contract safety value RecursiveNonemptyTests.failing (some growth)).2.2.2.2.2.2.2.1
  rw [(prepared safety value).2.1.graph]
  simpa only [before, Call.key, call, ConstantInputTests.call] using prior

theorem cached (safety : Bool) (value : Word) (p : Primitives (Publication.Effects Nat)) :
    Caller.find (Publication.external ops.arguments) 160 7 p Interner.Queries.queries
      (call safety value).source ⟨(before safety value).memory.memory.nextId + 1, 0, 2⟩ (call safety value).request
      (entered safety value) = (.ok 4, ⟨entered safety value, { lookup := none }⟩) := by
  have initializedValue := congrArg Prod.fst (initialized safety value)
  have hit := Caller.find_cached (Publication.external ops.arguments) 160 7 p Interner.Queries.queries
    (call safety value).source ⟨(before safety value).memory.memory.nextId + 1, 0, 2⟩ (call safety value).request
    (entered safety value) [] (call safety value).prepared.2 (call safety value).key 4
    (room safety value) (Prod.ext initializedValue rfl) rfl rfl (selected safety value)
  rw [initialized] at hit
  exact hit

def returned (safety : Bool) (value : Word) := (call safety value).returnedWorld (entered safety value)

theorem invoked (safety : Bool) (value : Word)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives (Publication.Effects Nat)) :
    (call safety value).invoked p = (.ok 4, ⟨returned safety value, { lookup := none }⟩) := by
  have hit := cached safety value (p (call safety value).address (call safety value).native)
  simp only [Call.native, entered] at hit
  unfold Call.invoked
  change invoke (Publication.external ops.arguments) 160 7 p Interner.Queries.queries
    (call safety value).source (call safety value).request debug (before safety value) = _
  rw [invoke_prepared _ _ _ _ _ _ _ _ _ _ _ (prepared safety value).1]
  simp only [ConstructorFrame.find, room, Bool.false_eq_true, ↓reduceIte, (stack safety value).1,
    (prepared safety value).2.1.nextId, hit]
  rfl

theorem entered_facts (safety : Bool) (value : Word) :
    GraphFacts safety ReachablePrefixTests.backing 5 (entered safety value) (ConstantPublicationTests.rows safety value) ∧
    (∀ id cell, (before safety value).memory.memory.heap.lookup id = some cell →
      (entered safety value).memory.memory.heap.lookup id = some cell) := by
  have facts : GraphFacts safety ReachablePrefixTests.backing 5 (before safety value) (ConstantPublicationTests.rows safety value) := by
    simpa only [before] using (ConstantPublicationTests.contract safety value RecursiveNonemptyTests.failing (some growth)).2.1
  have current := (prepared safety value).2.1
  have buffer := caller_buffer (call safety value).constructed.memory (call safety value).stack _ ⟨0, 0, 0⟩ []
    current.valid (RecursiveTests.empty_good _ current.valid).2 (stack safety value).1
  have frame : ∀ id cell, (before safety value).memory.memory.heap.lookup id = some cell →
      (entered safety value).memory.memory.heap.lookup id = some cell :=
    fun id cell found => buffer.2.2.2 id cell (current.memory id cell found)
  refine ⟨facts.frame (by rw [ConstantPublicationTests.rows_count]; decide) buffer.1 ?_ ?_ (congrArg Publication.Effects.keys current.effects) frame ?_, frame⟩
  · exact (congrArg Interner.Heap.representatives current.graph).trans facts.projected
  · exact congrArg Interner.Heap.table current.graph
  · intro id block found
    change (call safety value).constructed.memory.heap id = some block
    rw [current.heap]; exact found

theorem returned_facts (safety : Bool) (value : Word) :
    GraphFacts safety ReachablePrefixTests.backing 5 (returned safety value) (ConstantPublicationTests.rows safety value) ∧
    (∀ id cell, (before safety value).memory.memory.heap.lookup id = some cell →
      (returned safety value).memory.memory.heap.lookup id = some cell) ∧
    (returned safety value).graph = (before safety value).graph ∧
    (returned safety value).memory.effects = (before safety value).memory.effects ∧
    (returned safety value).memory.heap = (before safety value).memory.heap := by
  have facts : GraphFacts safety ReachablePrefixTests.backing 5 (before safety value) (ConstantPublicationTests.rows safety value) := by
    simpa only [before] using (ConstantPublicationTests.contract safety value RecursiveNonemptyTests.failing (some growth)).2.1
  obtain ⟨owner, found, _⟩ := facts.owner
  have older := (Compiler.ZigAir.Memory.valid_lookup _ _ _ facts.valid.memory found).1
  have current := entered_facts safety value
  have bounded : (ConstantPublicationTests.rows safety value).length ≤ 5 := by rw [ConstantPublicationTests.rows_count]; decide
  have cleaned := (current.1.cleanup ((before safety value).memory.memory.nextId + 1) (by omega)
    (by change 5 < _; omega) bounded).cleanup (before safety value).memory.memory.nextId older (by change 5 < _; omega) bounded
  exact ⟨cleaned, fun id cell found => (call safety value).returned_cell _ facts.valid id cell found (current.2 id cell found),
    (prepared safety value).2.1.graph, (prepared safety value).2.1.effects, (prepared safety value).2.1.heap⟩

theorem locals_retired (safety : Bool) (value : Word) :
    (returned safety value).memory.memory.heap.lookup (before safety value).memory.memory.nextId = none ∧
    (returned safety value).memory.memory.heap.lookup ((before safety value).memory.memory.nextId + 1) = none := by
  have current := (prepared safety value).2.1
  have valid := (entered_facts safety value).1.valid.memory
  have cleaned : (returned safety value).memory.memory.heap =
      (Compiler.ZigAir.Memory.cleanup (before safety value).memory.memory.nextId (entered safety value).memory.memory).heap := by
    change ((entered safety value).memory.memory.heap.filter
      (fun entry => !entry.2.stack || entry.1 < (before safety value).memory.memory.nextId + 1)).filter
      (fun entry => !entry.2.stack || entry.1 < (before safety value).memory.memory.nextId) = _
    rw [List.filter_filter]
    apply List.filter_congr
    intro entry present
    by_cases older : entry.1 < (before safety value).memory.memory.nextId
    · have inner : entry.1 < (before safety value).memory.memory.nextId + 1 := by omega
      simp [older, inner]
    · cases flag : entry.2.stack <;> simp [older, flag]
  rw [cleaned]
  obtain ⟨item, found, isStack⟩ := current.stack
  obtain ⟨retained, kept, shape⟩ := (Compiler.ZigAir.Memory.allocate_retains_shape _ _ _ _ current.valid.memory
    (stack safety value).1) _ item found
  have itemDead := Compiler.ZigAir.Memory.cleanup_lookup_stack (entered safety value).memory.memory
    (before safety value).memory.memory.nextId (before safety value).memory.memory.nextId retained valid kept
    (shape.2.2.2.trans isStack) (Nat.le_refl _)
  obtain ⟨layout, base, _, _, allocated⟩ := Compiler.ZigAir.Memory.allocate_shape _ _ _ _ (stack safety value).1
  have scratch : (entered safety value).memory.memory.heap.lookup ((before safety value).memory.memory.nextId + 1) =
      some ⟨base, .array 2 word, [], true, true⟩ := by
    change (call safety value).stack.heap.lookup _ = _
    rw [allocated, current.nextId]
    simp only [Compiler.ZigAir.Memory.Heap.lookup_cons, ite_true]
  exact ⟨itemDead, Compiler.ZigAir.Memory.cleanup_lookup_stack _ _ _ _ valid scratch rfl (Nat.le_succ _)⟩
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ConstantCacheTests
