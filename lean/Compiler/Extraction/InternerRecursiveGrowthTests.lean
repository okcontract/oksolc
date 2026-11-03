/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursiveGrowthFailureTests
import Compiler.Extraction.InternerNativeInput

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveGrowthTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops lifetime growth GraphFacts)
open RecursiveTests (Call debug)
open RecursiveNonemptyTests
open NativeRecursion (constant_succ)

attribute [local irreducible] ready rootArguments childArguments Arguments.operation

/-- The growth context initializes the same prefix even when the later
simplified-parent publication is selected to fail. Empty-operand dispatch
reaches native insertion, whose publication probe belongs to the same context. -/
theorem prefix_equivalent (safety : Bool) (n : Nat) (bounded : n < 4) (depth : Nat) (publishOK : Bool) :
    (children safety (depth + 1) publishOK).operation (ReachablePrefixTests.opcode n) [] debug
      (ReachablePrefixTests.prior safety n) = ReachablePrefixTests.invoke safety n (ReachablePrefixTests.prior safety n) := by
  let call := ReachablePrefixTests.call safety n
  obtain ⟨item, entry, room⟩ := ReachablePrefixTests.entered safety n bounded
  have scope : call.taken.2.scope.slice = some call.normalized := by rw [entry.origin.scope]
  have current := NativeRecursion.Tests.miss_continuation call
    (primitives safety depth call.source publishOK call.address call.native) scope rfl
    (ReachablePrefixTests.simplified safety n (children safety depth publishOK) (base safety publishOK))
  have canonical := NativeRecursion.Tests.miss_continuation call
    (ReachablePrefixTests.primitives safety call.address call.native) scope rfl
    (ReachablePrefixTests.simplified safety n NativeRecursion.exhausted)
  have continuation : call.continuation (primitives safety depth call.source publishOK call.address call.native) =
      call.continuation (ReachablePrefixTests.primitives safety call.address call.native) := by
    rw [current, canonical]
    simp only [handoff, graph, scope, bind, Effect.bind]
    exact congrArg (fun ran => (ran.1, { call.taken.2 with
      world := ran.2
      scope := { call.taken.2.scope with slice := some call.normalized, handedOff := true } }))
      (NativeRecursion.Tests.prefix_insertion safety true n bounded)
  have same := NativeRecursion.Tests.same_call call _ _ (ReachablePrefixTests.observed safety n bounded).1
    item.graph room (ReachablePrefixTests.classified n) continuation
  have literal : Arguments.prepare [] (ReachablePrefixTests.prior safety n) =
      (.ok ⟨0, 0, 0⟩, ReachablePrefixTests.prior safety n) := rfl
  rw [children, NativeRecursion.operation_succ, Arguments.operation_prepared _ _ _ _ _ _ _ _ _ _ _ literal,
    ReachablePrefixTests.invoked]
  exact congrArg (fun ran => (ran.1, ran.2.world)) same

theorem prefix_result (safety : Bool) (depth n : Nat) (bounded : n < 4) (publishOK : Bool) :
    ReachablePrefixTests.sequence (children safety (depth + 1) publishOK) n (CallerInputTests.world safety) =
      (.ok (BitVec.ofNat 32 n), ReachablePrefixTests.before safety n) := by
  induction n with
  | zero => exact (prefix_equivalent safety 0 bounded depth publishOK).trans (ReachablePrefixTests.step_result safety 0 bounded)
  | succ n ih =>
    exact (Effect.bind_success _ _ _ _ _ (ih (by omega))).trans
      ((prefix_equivalent safety (n + 1) bounded depth publishOK).trans (ReachablePrefixTests.step_result safety (n + 1) bounded))

/-- The constant and recursive calls share one context; spare insertion does
not invoke the configured nonempty-growth callback. -/
theorem zero_insertion (safety : Bool) :
    Native.insert ops ReachablePrefixTests.allocate safety 7 6 ⟨0, 0, 0⟩ (zero safety).address Insertion.Tests.model
      (zero safety).native (zero safety).key (zero safety).normalized true (some growth) (zero safety).taken.2.world =
    Native.insert ops ReachablePrefixTests.allocate safety 7 6 ⟨0, 0, 0⟩ (zero safety).address Insertion.Tests.model
      (zero safety).native (zero safety).key (zero safety).normalized true none (zero safety).taken.2.world := by
  cases safety <;> insertion_kernel_rfl

theorem zero_equivalent (safety : Bool) (depth : Nat) (publishOK : Bool := true) :
    (children safety (depth + 1) publishOK).constant 0 debug (initial safety) = (.ok 4, ready safety) := by
  have established := zero_established safety
  have prior := ReachablePrefixTests.initialized_prefix safety 3 (by decide)
  have room : Interner.Queries.queries.atCapacity (zero safety).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ established.constructed.projected, prior.count]; decide
  have sameContinuation : (zero safety).continuation (primitives safety depth ⟨0, 0, 0⟩ publishOK (zero safety).address (zero safety).native) =
      (zero safety).continuation (zeroPrimitives safety (zero safety).address (zero safety).native) := by
    simp only [Call.continuation, Interner.FindCode.controlMiss, Caller.execution, OwnedCall.execution,
      show (zero safety).request.item.kind = 2 from rfl, BitVec.reduceBEq, Bool.false_eq_true,
      Bool.true_and, ↓reduceIte, handoff, graph, established.entry.origin.scope,
      bind, Effect.bind, pure, Effect.pure]
    exact congrArg (fun ran =>
      (ran.1, { (zero safety).taken.2 with
        world := ran.2
        scope := ⟨some (zero safety).lookup, some (zero safety).normalized, true⟩ }))
      (zero_insertion safety)
  have same : (zero safety).invoked (primitives safety depth ⟨0, 0, 0⟩ publishOK) = (zero safety).invoked (zeroPrimitives safety) := by
    rw [(zero safety).route _ (zero_observed safety).1 established.item.graph room rfl,
      (zero safety).route _ (zero_observed safety).1 established.item.graph room rfl, sameContinuation]
  have called : (zero safety).invoked (zeroPrimitives safety) = zeroFull safety := by
    unfold Call.invoked zeroFull constant
    rfl
  rw [called] at same
  have result : ((zeroFull safety).1, (zeroFull safety).2.world) = (.ok 4, ready safety) :=
    Prod.ext (zero_contract safety).1 (by unfold ready; rfl)
  rw [children, constant_succ]
  exact (congrArg (fun ran => (ran.1, ran.2.world)) same).trans
    result

def program (safety : Bool) (depth : Nat) (publishOK : Bool := true) : Except Fault NodeId × World (Publication.Effects Nat) :=
  (do let _ ← ReachablePrefixTests.sequence (children safety depth publishOK) 3
      let id ← (children safety depth publishOK).constant 0 debug
      (children safety depth publishOK).operation 20 [0, id] debug) (CallerInputTests.world safety)

theorem program_equivalent (safety : Bool) (depth : Nat) : program safety (depth + 2) = root safety (depth + 2) :=
  (Effect.bind_success _ _ _ _ _ (prefix_result safety (depth + 1) 3 (by decide) true)).trans
    ((Effect.bind_success _ _ _ _ _ (zero_equivalent safety (depth + 1))).trans rfl)

/-- Word observations of this initialized fixture and the newly inserted row.
General environment-word semantics remain outside the fixture's scope. -/
theorem selected_words (safety : Bool) :
    (row safety).value = 1 ∧ (parent safety).key.eval Insertion.Tests.model (ready safety).graph.read = some 1 := by
  constructor <;> cases safety <;> insertion_kernel_rfl

theorem reached_words (safety : Bool) (depth : Nat) :
    (root safety (depth + 2)).2.graph.read 5 = some 1 ∧
    (∀ id value, (ready safety).graph.read id = some value → (root safety (depth + 2)).2.graph.read id = some value) := by
  obtain ⟨after, result, _⟩ := root_native safety depth
  have read : (root safety (depth + 2)).2.graph.read = Storage.readValue (appendedRows safety) := by rw [result]; rfl
  rw [read]
  constructor
  · simp [Storage.readValue, appendedRows, rows_count, (selected_words safety).1]
  · intro id value known
    rw [(zero_contract safety).2.2.2.1] at known
    have inside : id.toNat < (rows safety).length := by
      by_cases inside : id.toNat < (rows safety).length
      · exact inside
      · simp only [Storage.readValue, List.getElem?_eq_none (Nat.le_of_not_gt inside), Option.map_none] at known
        contradiction
    simpa only [Storage.readValue, appendedRows, List.getElem?_append, inside, ↓reduceIte] using known

/-- One actual recursive program publishes Push zero, calls EQ, recursively
inserts ISZERO through nonempty relocation, then publishes the parent key and
returns. Native graph/query facts, live parent ownership, exact result and word
preservation follow from that execution at every sufficient depth. This scoped
composition does not establish the general constructor induction. -/
theorem program_contract (safety : Bool) (depth : Nat) :
    (program safety (depth + 2)).1 = .ok 5 ∧
    NativeGraph.Facts safety 7 6 ⟨backing safety, 0⟩ 13 (program safety (depth + 2)).2 (appendedRows safety) ∧
    (program safety (depth + 2)).2.memory.memory.heap.lookup rootSource.allocation = none ∧
    (program safety (depth + 2)).2.memory.heap ReachablePrefixTests.backing = none ∧
    (program safety (depth + 2)).2.memory.memory.heap.lookup ReachablePrefixTests.backing = none ∧
    (program safety (depth + 2)).2.memory.effects.keys (parent safety).key = some ⟨(parent safety).normalized.address, 5⟩ ∧
    (program safety (depth + 2)).2.graph.read 5 = some 1 ∧
    (parent safety).key.eval Insertion.Tests.model (ready safety).graph.read = some 1 ∧
    (∀ id value, (ready safety).graph.read id = some value → (program safety (depth + 2)).2.graph.read id = some value) ∧
    (∀ id, Constant.value (program safety (depth + 2)).2.memory.memory (Owner.headerAddress ⟨6, 0⟩) id =
      .ok (Storage.constantProgram.run (appendedRows safety) id)) ∧
    (∀ id opcode, Operation.run (program safety (depth + 2)).2.memory.memory (Owner.headerAddress ⟨6, 0⟩) id opcode =
      .ok ((Storage.operationProgram.run (appendedRows safety) id opcode).map (Option.map Operation.returned))) ∧
    ∃ after, (children safety (depth + 1)).operation 21 [0] debug (parent safety).taken.2.world = (.ok 5, returnedChild safety after) ∧
      Held 7 rootSource [0, 4] (parent safety).normalized (returnedChild safety after) := by
  rw [program_equivalent]
  obtain ⟨after, result, facts, called, held, keys, oldDead, nativeDead, sourceDead⟩ := root_native safety depth
  have words := reached_words safety depth
  refine ⟨congrArg Prod.fst result, facts, sourceDead, oldDead, nativeDead, ?_, words.1, (selected_words safety).2,
    words.2, facts.constants, facts.operations, after, called, held⟩
  rw [keys, OwnedKeys.store, if_pos rfl]

/-- Every previously queried operand remains readable through the shared
dispatcher's native input boundary after the actual child relocation, parent
publication and cleanup. The annotation cannot substitute for the native read. -/
theorem program_inputs (safety : Bool) (depth : Nat) (id : NodeId) (opcode : Opcode)
    (source : ArgumentSlice)
    (query : Storage.operationProgram.run (rows safety) id opcode = .ok (some source))
    (index : Nat) (inside : index < source.items.length) (annotation : NodeId) :
    NativeRecursion.operand source index annotation (program safety (depth + 2)).2 =
      (.ok source.items[index], (program safety (depth + 2)).2) :=
  ((program_contract safety depth).2.1).operand_after_append (rows safety) [row safety]
    id opcode source query index inside annotation

/-- Depth exhaustion preserves the newly published Push and the reached parent
owners. It is an explicit nonordinary rejection, not a native allocation error. -/
theorem root_one (safety : Bool) : root safety 1 =
    (.error (.language .unsupported), (parent safety).taken.2.world) := by
  have established := parent_established safety
  have scope := established.entry.origin.scope
  have room : Interner.Queries.queries.atCapacity (parent safety).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ established.constructed.projected, rows_count]; decide
  have simplified : (primitives safety 0 rootSource true (parent safety).address (parent safety).native).simplify
      (parent safety).key (parent safety).normalized (parent safety).taken.2.world =
        (.error (.language .unsupported), (parent safety).taken.2.world) := by
    have facts := (parent_established safety).taken.native (by rw [rows_count]; decide)
    simp only [primitives, NativeRecursion.dispatcher_snapshot]
    rw [facts.reads]
    exact iszero_failure (input := NativeRecursion.operand) (address := (parent safety).normalized.address)
      (Interner.representativeReads (parent safety).taken.2.world.graph)
      (children safety 0) (parent safety).taken.2.world (parent safety).taken.2.world
      (first_constant safety _ established.taken).1 (parent_zero safety).1 rfl
  have continuation : (parent safety).continuation (primitives safety 0 rootSource true (parent safety).address (parent safety).native) =
      (.error (.language .unsupported), (parent safety).taken.2) := by
    simp only [Call.continuation, Interner.FindCode.controlMiss, Caller.execution, OwnedCall.execution,
      show (parent safety).request.item.kind = 1 from rfl, beq_self_eq_true, Bool.and_self, ↓reduceIte,
      graph, scope, simplified, bind, Effect.bind]
    rw [← scope]
  have routed := (parent safety).route (primitives safety 0 rootSource true) (calls_observed safety false)
    established.item.graph room rfl
  rw [continuation] at routed
  have result : (parent safety).invoked (primitives safety 0 rootSource true) =
      (.error (.language .unsupported), (parent safety).taken.2) := routed
  have literal : Arguments.prepare [0, 4] (ready safety) = (.ok rootSource, (parent safety).before) := by
    simpa only [parent, rootArguments] using
      (Prod.ext (literals_observed safety).1 rfl : rootArguments safety = (.ok rootSource, (rootArguments safety).2))
  rw [root, children, show 1 = 0 + 1 from rfl, NativeRecursion.operation_succ,
    Arguments.operation_prepared _ _ _ _ _ _ _ _ _ _ _ literal]
  change Arguments.returned [0, 4] _ ((parent safety).invoked (primitives safety 0 rootSource true)) = _
  rw [result]; rfl

theorem program_one (safety : Bool) : program safety 1 =
    (.error (.language .unsupported), (parent safety).taken.2.world) :=
  (Effect.bind_success _ _ _ _ _ (prefix_result safety 0 3 (by decide) true)).trans
    ((Effect.bind_success _ _ _ _ _ (zero_equivalent safety 0)).trans (root_one safety))

theorem exhaustion_retained (safety : Bool) :
    ordinary (program safety 1).1 = false ∧
    Held 7 rootSource [0, 4] (parent safety).normalized (program safety 1).2 ∧
    NativeGraph.Facts safety 7 6 ⟨ReachablePrefixTests.backing, 0⟩ 5 (program safety 1).2 (rows safety) ∧
    Constant.value (program safety 1).2.memory.memory (Owner.headerAddress ⟨6, 0⟩) 4 = .ok (.ok (some 0)) := by
  rw [program_one]
  have established := parent_established safety
  exact ⟨rfl, established.entry.origin.held,
    established.taken.native (by rw [rows_count]; decide), (parent_zero safety).2⟩

/-- Initial Push publication and the failing parent use the same recursive
family and reached state; the child's new word remains observable after OOM. -/
theorem program_failed_equivalent (safety : Bool) (depth : Nat) :
    program safety (depth + 2) false = failedRoot safety (depth + 2) :=
  (Effect.bind_success _ _ _ _ _ (prefix_result safety (depth + 1) 3 (by decide) false)).trans
    ((Effect.bind_success _ _ _ _ _ (zero_equivalent safety (depth + 1) false)).trans rfl)

theorem program_failed_words (safety : Bool) (depth : Nat) :
    (program safety (depth + 2) false).1 = .error (.language .outOfMemory) ∧
    (program safety (depth + 2) false).2.graph.read 5 = some 1 ∧
    (∀ id value, (ready safety).graph.read id = some value →
      (program safety (depth + 2) false).2.graph.read id = some value) := by
  rw [program_failed_equivalent]
  have outcome := failed_root_native safety depth
  refine ⟨outcome.1, ?_, ?_⟩
  · rw [outcome.2.2.2.2.2.2.2]
    simp [Storage.readValue, appendedRows, rows_count, (selected_words safety).1]
  · intro id value known
    rw [outcome.2.2.2.2.2.2.2]
    rw [(zero_contract safety).2.2.2.1] at known
    have inside : id.toNat < (rows safety).length := by
      by_cases inside : id.toNat < (rows safety).length
      · exact inside
      · simp only [Storage.readValue, List.getElem?_eq_none (Nat.le_of_not_gt inside), Option.map_none] at known
        contradiction
    simpa only [Storage.readValue, appendedRows, List.getElem?_append, inside, ↓reduceIte] using known

theorem program_zero (safety publishOK : Bool) : program safety 0 publishOK =
    (.error (.language .unsupported), CallerInputTests.world safety) := by rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveGrowthTests
