/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursiveNonemptyReturnTests
import Compiler.Extraction.InternerViewInput
import Compiler.Extraction.InternerReachablePrefixTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.BinaryPreludeTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops cells lifetime GraphFacts)
open RecursiveTests (Call debug)

def opcode (xor : Bool) : Opcode := if xor then 24 else 22

abbrev initial (safety : Bool) := ReachablePrefixTests.before safety 3
def arguments (safety : Bool) := Arguments.prepare [0, 1] (initial safety)
def source : View := ⟨21, 0, 2⟩
def call (safety xor : Bool) : Call := ⟨Interner.constructorCode.operationRequest (opcode xor) [0, 1], source, (arguments safety).2⟩
def operands : ArgumentSlice := ⟨25, [0, 1]⟩
def seed (source : View) : Primitives (Publication.Effects Nat) := RecursiveNonemptyTests.childSeed source
def primitives (safety _xor : Bool) (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue) :=
  callerPrimitives ops CallerGrowingChainTests.allocate safety 7 6 source address Insertion.Tests.model native (seed source)
def inner (safety xor : Bool) := operation (Publication.external ops.arguments) 160 7 (primitives safety xor)
  Interner.Queries.queries source (opcode xor) [0, 1] debug (call safety xor).before
def full (safety xor : Bool) := Arguments.operation (Publication.external ops.arguments) 160 7
  (fun _ => primitives safety xor) Interner.Queries.queries (opcode xor) [0, 1] debug (initial safety)
def row (safety xor : Bool) := (call safety xor).publicationRow 26 operands (call safety xor).taken.2.world
def rows (safety xor : Bool) := ReachablePrefixTests.cells safety 3 ++ [row safety xor]
def ready (safety xor : Bool) := (full safety xor).2

attribute [local irreducible] invoke arguments full ready

set_option maxHeartbeats 800000 in
theorem prefix_observed (safety xor : Bool) :
    (arguments safety).1 = .ok source ∧
    (call safety xor).observations = (call safety xor).expected ∧
    (call safety xor).duplicate.1 = .ok (operands, ⟨view (call safety xor).normalized, [0, 1], none⟩) ∧
    (call safety xor).create.1 = .ok 26 ∧ (call safety xor).clone.1 = .ok (call safety xor).native := by
  cases safety <;> cases xor <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> insertion_kernel_rfl

theorem literal_facts (safety : Bool) (capacity : Nat) (rows : List Storage.Cell)
    (values : List NodeId) (before after : World (Publication.Effects Nat)) (source : View)
    (facts : GraphFacts safety ReachablePrefixTests.backing capacity before rows) (bounded : rows.length ≤ capacity)
    (ran : Arguments.prepare values before = (.ok source, after)) :
    Arguments.Prepared values before source after ∧ GraphFacts safety ReachablePrefixTests.backing capacity after rows := by
  have prepared := Arguments.prepare_success values before after source facts.valid ran
  refine ⟨prepared, facts.frame bounded prepared.good.1 ?_ ?_ ?_ prepared.frame ?_⟩
  · exact (congrArg Interner.Heap.representatives prepared.graph).trans facts.projected
  · exact congrArg Interner.Heap.table prepared.graph
  · exact congrArg Publication.Effects.keys prepared.effects
  · intro id block found; rw [prepared.heap]; exact found

theorem literal (safety xor : Bool) :
    Arguments.Prepared [0, 1] (initial safety) source (call safety xor).before ∧
    GraphFacts safety ReachablePrefixTests.backing 5 (call safety xor).before (ReachablePrefixTests.cells safety 3) := by
  have prior := ReachablePrefixTests.initialized_prefix safety 3 (by decide)
  exact literal_facts safety 5 _ _ _ _ _ prior.facts (by rw [prior.count]; decide)
    (by simpa only [call, arguments] using
      (Prod.ext (prefix_observed safety xor).1 rfl : arguments safety = (.ok source, (arguments safety).2)))

theorem established (safety xor : Bool) : (call safety xor).Established safety ReachablePrefixTests.backing 5 (ReachablePrefixTests.cells safety 3) :=
  (call safety xor).establish safety ReachablePrefixTests.backing 5 _ (literal safety xor).2
    (by rw [(ReachablePrefixTests.initialized_prefix safety 3 (by decide)).count]; decide)
    (literal safety xor).1.good (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) (prefix_observed safety xor).2.1

theorem simplified (safety xor : Bool) : (seed source).simplify (call safety xor).key
    (call safety xor).normalized (call safety xor).taken.2.world = (.ok none, (call safety xor).taken.2.world) := by
  have dispatch : Dispatch.simplify (Nested.storageReads (ReachablePrefixTests.cells safety 3)) RecursiveNonemptyTests.noChildren
      64 (opcode xor) [0, 1] debug = (fun world => (.ok none, world)) := by
    cases safety <;> cases xor <;> insertion_kernel_rfl
  change Dispatch.simplify (Interner.representativeReads (call safety xor).taken.2.world.graph)
    RecursiveNonemptyTests.noChildren 64 (opcode xor) [0, 1] debug (call safety xor).taken.2.world = _
  simp only [Interner.representativeReads, (established safety xor).taken.projected, dispatch]

/-- Publish AND or XOR through its full constructor before exposing its operand view.
The spare-capacity native proof supplies the installed fields and graph owners. -/
theorem inner_contract (safety xor : Bool) :
    (inner safety xor).1 = .ok 4 ∧ GraphFacts safety ReachablePrefixTests.backing 5 (inner safety xor).2.world (rows safety xor) ∧
    AssemblyClone.NativeFields.Represents (inner safety xor).2.world.memory.memory ⟨26, 0⟩ (call safety xor).native ∧
    (inner safety xor).2.world.graph.read = Storage.readValue (rows safety xor) := by
  have prior := ReachablePrefixTests.initialized_prefix safety 3 (by decide)
  have established := established safety xor
  have calls := prefix_observed safety xor
  have room : Interner.Queries.queries.atCapacity (call safety xor).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ established.constructed.projected, prior.count]; decide
  have routed := (call safety xor).route (primitives safety xor) calls.2.1 established.item.graph room
    (by cases xor <;> rfl)
  have continued : (call safety xor).continuation (primitives safety xor (call safety xor).address (call safety xor).native) =
      (do handoff; graph (fun slice => Native.insert ops CallerGrowingChainTests.allocate safety 7 6 source
        (call safety xor).address Insertion.Tests.model (call safety xor).native (call safety xor).key slice true none) :
          Action (Publication.Effects Nat) NodeId) (call safety xor).taken.2 := by
    simp only [Call.continuation, Interner.FindCode.controlMiss, Caller.execution, OwnedCall.execution,
      show (call safety xor).request.item.kind = 1 from rfl, beq_self_eq_true, Bool.and_self, ↓reduceIte,
      primitives, callerPrimitives, graph, established.entry.origin.scope, simplified, bind, Effect.bind]
    rw [← established.entry.origin.scope]; rfl
  rw [continued] at routed
  change (call safety xor).invoked (primitives safety xor) =
    (let done := finishInsertion ops CallerGrowingChainTests.allocate safety 7 6 (call safety xor).source (call safety xor).address
      Insertion.Tests.model (call safety xor).native (call safety xor).key true (call safety xor).taken.2 none
     if ordinary done.1 then (done.1, (call safety xor).returned done.2) else done) at routed
  have complete := (call safety xor).spare_publication CallerGrowingChainTests.allocate none safety ReachablePrefixTests.backing 5 26 (ReachablePrefixTests.cells safety 3) operands
    (call safety xor).duplicate.2 (call safety xor).create.2 (call safety xor).clone.2 (primitives safety xor)
    (literal safety xor).2 (literal safety xor).1.good (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide)
    calls.2.1 (by rw [prior.count]; decide) (by rw [prior.count]; decide)
    (Prod.ext calls.2.2.1 rfl) (Prod.ext calls.2.2.2.1 rfl) (Prod.ext calls.2.2.2.2 rfl) routed
  have called : (call safety xor).invoked (primitives safety xor) = inner safety xor := by
    unfold Call.invoked inner operation; rfl
  rw [called, Storage.idFor, prior.count] at complete
  exact ⟨complete.1, complete.2.1, complete.2.2.1, complete.2.2.2.1⟩

theorem route (safety xor : Bool) : full safety xor =
    TemporaryArguments.unwind (initial safety).memory.memory.nextId (inner safety xor) := by
  have literal : Arguments.prepare [0, 1] (initial safety) = (.ok source, (call safety xor).before) :=
    by simpa only [call, arguments] using
      (Prod.ext (prefix_observed safety xor).1 rfl : arguments safety = (.ok source, (arguments safety).2))
  rw [full, Arguments.operation_prepared _ _ _ _ _ _ _ _ _ _ _ literal]
  exact Arguments.returned_nonempty [0, 1] _ _ rfl

theorem rows_count (safety xor : Bool) : (rows safety xor).length = 5 := by
  simp only [rows, List.length_append, List.length_singleton,
    (ReachablePrefixTests.initialized_prefix safety 3 (by decide)).count]

/-- Outer literal cleanup follows the actual successful constructor result;
persistent graph operands and the installed binary item survive it. -/
theorem contract (safety xor : Bool) :
    (full safety xor).1 = .ok 4 ∧ GraphFacts safety ReachablePrefixTests.backing 5 (ready safety xor) (rows safety xor) ∧
    (ready safety xor).graph.read = Storage.readValue (rows safety xor) := by
  have result := inner_contract safety xor
  have reached : ready safety xor = { (inner safety xor).2.world with memory := { (inner safety xor).2.world.memory with
      memory := Compiler.ZigAir.Memory.cleanup (initial safety).memory.memory.nextId (inner safety xor).2.world.memory.memory } } := by
    rw [ready, route]; simp only [TemporaryArguments.unwind, result.1]; rfl
  have count : (initial safety).memory.memory.nextId = 21 := by cases safety <;> cases xor <;> insertion_kernel_rfl
  have cleaned := result.2.1.cleanup (initial safety).memory.memory.nextId
    (by rw [count]; decide) (by rw [count]; decide) (by rw [rows_count]; decide)
  refine ⟨?_, ?_, ?_⟩
  · rw [route]; simp only [TemporaryArguments.unwind, result.1]
  · rw [reached]; exact cleaned
  · rw [reached]; exact result.2.2.2

/-- Retire the actual temporary literal after an ordinary constructor return. -/
theorem literal_return_facts (safety : Bool) (backing capacity : Nat) (rows : List Storage.Cell)
    (values : List NodeId) (before prepared : World (Publication.Effects Nat)) (source : View)
    (ran : Except Fault NodeId × OwnedCall.State (Publication.Effects Nat))
    (prior : GraphFacts safety backing capacity before rows)
    (literal : Arguments.Prepared values before source prepared) (nonempty : values ≠ [])
    (facts : GraphFacts safety backing capacity ran.2.world rows) (bounded : rows.length ≤ capacity)
    (native : ∀ id cell, prepared.memory.memory.heap.lookup id = some cell → ran.2.world.memory.memory.heap.lookup id = some cell)
    (ordinary : ordinary ran.1 = true) :
    let returned := TemporaryArguments.unwind before.memory.memory.nextId ran
    GraphFacts safety backing capacity returned.2 rows ∧
    returned.2.memory.memory.heap.lookup source.allocation = none ∧
    (∀ id cell, before.memory.memory.heap.lookup id = some cell → returned.2.memory.memory.heap.lookup id = some cell) := by
  simp only [TemporaryArguments.unwind, ordinary, ↓reduceIte]
  obtain ⟨owner, ownerFound, _⟩ := prior.owner
  obtain ⟨input, inputFound, _⟩ := prior.nativeInput
  have retained := facts.cleanup before.memory.memory.nextId
    (Compiler.ZigAir.Memory.valid_lookup _ _ _ prior.valid.memory ownerFound).1
    (Compiler.ZigAir.Memory.valid_lookup _ _ _ prior.valid.memory inputFound).1 bounded
  obtain ⟨cell, found, _, _, _⟩ := literal.storage nonempty
  refine ⟨retained, literal.retire values before prepared source nonempty _ facts.valid.memory
    ((native _ _ found).trans found.symm), ?_⟩
  intro id cell found
  exact (Compiler.ZigAir.Memory.cleanup_lookup_older _ _ id
    (Compiler.ZigAir.Memory.valid_lookup _ _ _ prior.valid.memory found).1).trans
    (native id cell (literal.frame id cell found))

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.BinaryPreludeTests
