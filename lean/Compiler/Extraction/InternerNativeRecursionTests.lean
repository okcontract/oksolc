/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeDispatch
import Compiler.Extraction.InternerRecursiveBorrowedTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.Tests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops lifetime growth GraphFacts)
open RecursiveTests (Call debug)
open RecursiveBorrowedTests

def children (safety : Bool) (depth : Nat) := NativeRecursion.unfold (childContext safety) 6 64 depth
def recursivePrimitives (safety : Bool) (depth : Nat) (source : View) :=
  (context (childContext safety) 6 64 (children safety depth) debug).primitives source
def recursiveChild (safety : Bool) (depth : Nat) :=
  (children safety (depth + 1)).borrowedOperation xorOperands.address 20 xorOperands.items debug (child safety).before
def recursiveRoot (safety : Bool) (depth : Nat) :=
  (children safety depth).operation 21 [4] debug (ready safety)

attribute [local irreducible] ready rootArguments Arguments.operation

theorem same_call (call : Call)
    (p q : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives (Publication.Effects Nat))
    (observed : call.observations = call.expected) (unchanged : call.constructed.graph = call.before.graph)
    (room : Interner.Queries.queries.atCapacity call.constructed.graph = false)
    (classified : Interner.Queries.queries.deterministic call.request.item = .ok true)
    (same : call.continuation (p call.address call.native) = call.continuation (q call.address call.native)) :
    call.invoked p = call.invoked q := by
  rw [call.route p observed unchanged room classified, call.route q observed unchanged room classified, same]

theorem miss_continuation (call : Call) (p : Primitives (Publication.Effects Nat))
    (scope : call.taken.2.scope.slice = some call.normalized) (kind : call.request.item.kind = 1)
    (missed : p.simplify call.key call.normalized call.taken.2.world = (.ok none, call.taken.2.world)) :
    call.continuation p =
      (do handoff; graph (fun slice => p.insert call.key slice true) : Action (Publication.Effects Nat) NodeId) call.taken.2 := by
  simp only [Call.continuation, Interner.FindCode.controlMiss, Caller.execution, OwnedCall.execution,
    kind, beq_self_eq_true, Bool.and_self, ↓reduceIte, graph, scope, missed, bind, Effect.bind]
  rfl

/-- Both recursive allocation policies agree with the canonical prefix before
any nonempty growth is requested. -/
def PrefixInsertion (safety grow : Bool) (n : Nat) : Prop :=
    Native.insert ops (ReachablePrefixTests.allocator grow) safety 7 6 (ReachablePrefixTests.call safety n).source
      (ReachablePrefixTests.call safety n).address Insertion.Tests.model
      (ReachablePrefixTests.call safety n).native (ReachablePrefixTests.call safety n).key
      (ReachablePrefixTests.call safety n).normalized true (some growth) (ReachablePrefixTests.call safety n).taken.2.world =
    Native.insert ops ReachablePrefixTests.allocate safety 7 6 (ReachablePrefixTests.call safety n).source
      (ReachablePrefixTests.call safety n).address Insertion.Tests.model
      (ReachablePrefixTests.call safety n).native (ReachablePrefixTests.call safety n).key
      (ReachablePrefixTests.call safety n).normalized true none (ReachablePrefixTests.call safety n).taken.2.world

private theorem prefix_insertion_0 (safety grow : Bool) : PrefixInsertion safety grow 0 := by
  let call := ReachablePrefixTests.call safety 0
  let current := Native.insert ops (ReachablePrefixTests.allocator grow) safety 7 6 call.source call.address Insertion.Tests.model
    call.native call.key call.normalized true (some growth) call.taken.2.world
  let canonical := Native.insert ops ReachablePrefixTests.allocate safety 7 6 call.source call.address Insertion.Tests.model
    call.native call.key call.normalized true none call.taken.2.world
  have currentHeap : current.2.memory.heap = Memory.write
      (Memory.write call.clone.2.heap 11 (some ⟨7, .representatives []⟩)) 11
      (some ⟨7, .representatives [ReachablePrefixTests.row safety 0]⟩) := by
    dsimp only [current, canonical, call]
    cases safety <;> cases grow <;> insertion_kernel_rfl
  have canonicalHeap : canonical.2.memory.heap = Memory.write call.clone.2.heap 11
      (some ⟨7, .representatives [ReachablePrefixTests.row safety 0]⟩) := by
    dsimp only [current, canonical, call]
    cases safety <;> cases grow <;> insertion_kernel_rfl
  have heap : current.2.memory.heap = canonical.2.memory.heap := by
    rw [currentHeap, canonicalHeap]
    funext query
    by_cases selected : query = 11 <;> simp only [Memory.write, selected, ↓reduceIte]
  have same : current = (canonical.1, { canonical.2 with memory := { canonical.2.memory with heap := current.2.memory.heap } }) := by
    dsimp only [current, canonical, call]
    cases safety <;> cases grow <;> insertion_kernel_rfl
  change current = canonical
  simpa only [heap] using same

private theorem prefix_insertion_1 (safety grow : Bool) : PrefixInsertion safety grow 1 := by
  unfold PrefixInsertion
  cases safety <;> cases grow <;> insertion_kernel_rfl

private theorem prefix_insertion_2 (safety grow : Bool) : PrefixInsertion safety grow 2 := by
  unfold PrefixInsertion
  cases safety <;> cases grow <;> insertion_kernel_rfl

private theorem prefix_insertion_3 (safety grow : Bool) : PrefixInsertion safety grow 3 := by
  unfold PrefixInsertion
  cases safety <;> cases grow <;> insertion_kernel_rfl

theorem prefix_insertion (safety grow : Bool) (n : Nat) (bounded : n < 4) : PrefixInsertion safety grow n := by
  have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact prefix_insertion_0 safety grow
  · exact prefix_insertion_1 safety grow
  · exact prefix_insertion_2 safety grow
  · exact prefix_insertion_3 safety grow

/-- Empty-operand dispatch proves no proper child is visited at any positive
observation depth. The full call retains this context's actual allocator. -/
theorem prefix_equivalent (safety : Bool) (n : Nat) (bounded : n < 4) (depth : Nat) :
    (children safety (depth + 1)).operation (ReachablePrefixTests.opcode n) [] debug
      (ReachablePrefixTests.prior safety n) = ReachablePrefixTests.invoke safety n (ReachablePrefixTests.prior safety n) := by
  let call := ReachablePrefixTests.call safety n
  obtain ⟨item, entry, room⟩ := ReachablePrefixTests.entered safety n bounded
  have scope : call.taken.2.scope.slice = some call.normalized := by rw [entry.origin.scope]
  have current := miss_continuation call (recursivePrimitives safety depth call.source call.address call.native)
    scope rfl (ReachablePrefixTests.simplified safety n (children safety depth))
  have old := miss_continuation call (ReachablePrefixTests.primitives safety call.address call.native)
    scope rfl (ReachablePrefixTests.simplified safety n NativeRecursion.exhausted)
  have sameContinuation : call.continuation (recursivePrimitives safety depth call.source call.address call.native) =
      call.continuation (ReachablePrefixTests.primitives safety call.address call.native) := by
    rw [current, old]
    simp only [handoff, graph, scope, bind, Effect.bind]
    exact congrArg (fun ran => (ran.1, { call.taken.2 with
      world := ran.2
      scope := { call.taken.2.scope with slice := some call.normalized, handedOff := true } }))
      (prefix_insertion safety false n bounded)
  have same := same_call call _ _ (ReachablePrefixTests.observed safety n bounded).1 item.graph room
    (ReachablePrefixTests.classified n) sameContinuation
  have literal : Arguments.prepare [] (ReachablePrefixTests.prior safety n) =
      (.ok ⟨0, 0, 0⟩, ReachablePrefixTests.prior safety n) := rfl
  rw [children, operation_succ, Arguments.operation_prepared _ _ _ _ _ _ _ _ _ _ _ literal,
    ReachablePrefixTests.invoked]
  exact congrArg (fun ran => (ran.1, ran.2.world)) same

/-- Initialization and all four full constructors execute under the very same
recursive context later used by the parent and child, for every positive depth. -/
theorem prefix_result (safety : Bool) (depth n : Nat) (bounded : n < 4) :
    ReachablePrefixTests.sequence (children safety (depth + 1)) n (CallerInputTests.world safety) =
      (.ok (BitVec.ofNat 32 n), ReachablePrefixTests.before safety n) := by
  induction n with
  | zero => exact (prefix_equivalent safety 0 bounded depth).trans (ReachablePrefixTests.step_result safety 0 bounded)
  | succ n ih =>
    exact (Effect.bind_success _ _ _ _ _ (ih (by omega))).trans
      ((prefix_equivalent safety (n + 1) bounded depth).trans (ReachablePrefixTests.step_result safety (n + 1) bounded))

theorem child_simplifier (safety : Bool) (depth : Nat) :
    (recursivePrimitives safety depth childSource (child safety).address (child safety).native).simplify
      (child safety).key (child safety).normalized (child safety).taken.2.world = (.ok none, (child safety).taken.2.world) := by
  have facts := (child_established safety).taken.native (by rw [rows_count]; decide)
  simp only [recursivePrimitives, dispatcher_snapshot]
  rw [facts.reads]
  apply eq_miss (input := NativeRecursion.operand) (address := (child safety).normalized.address) _ _ _
  · exact (constants safety _ (child_established safety).taken 0 (Or.inl rfl)).1
  · exact (constants safety _ (child_established safety).taken 1 (Or.inr (Or.inl rfl))).1
  · simp only [Interner.representativeReads, (child_established safety).taken.projected, Nested.storageReads]

/-- At every positive child depth the complete native EQ constructor reaches
the same insertion and cleanup. Its recursive callbacks are the real lower
unfolding; the actual EQ guards prove those callbacks are not visited. -/
theorem child_equivalent (safety : Bool) (depth : Nat) : recursiveChild safety depth = childFull safety := by
  have established := child_established safety
  have room : Interner.Queries.queries.atCapacity (child safety).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ established.constructed.projected, rows_count]; decide
  have scope : (child safety).taken.2.scope.slice = some (child safety).normalized := by rw [established.entry.origin.scope]
  have old := miss_continuation (child safety) (childPrimitives safety childSource (child safety).address (child safety).native)
    scope rfl (child_simplified safety)
  have current := miss_continuation (child safety) (recursivePrimitives safety depth childSource (child safety).address (child safety).native)
    scope rfl (child_simplifier safety depth)
  have same : (child safety).invoked (recursivePrimitives safety depth childSource) =
      (child safety).invoked (childPrimitives safety childSource) :=
    same_call _ _ _ (calls_observed safety true) established.item.graph room rfl (current.trans old.symm)
  have actual := congrArg (fun ran => (ran.1, ran.2.world)) same
  rw [recursiveChild, children, borrowed_succ]
  exact actual

theorem parent_continuation (safety : Bool) (depth : Nat) (after : Native.Frame Nat)
    (called : childFull safety = (.error (.language .outOfMemory), childReturned safety after)) :
    (parent safety).continuation (recursivePrimitives safety (depth + 1) rootSource (parent safety).address (parent safety).native) =
      (.error (.language .outOfMemory), ⟨childReturned safety after, (parent safety).taken.2.scope⟩) := by
  have scope := (parent_established safety).entry.origin.scope
  have childCall : (children safety (depth + 1)).borrowedOperation xorOperands.address 20 xorOperands.items debug
      (parent safety).taken.2.world = (.error (.language .outOfMemory), childReturned safety after) :=
    (child_equivalent safety depth).trans called
  have simplified : (recursivePrimitives safety (depth + 1) rootSource (parent safety).address (parent safety).native).simplify
      (parent safety).key (parent safety).normalized (parent safety).taken.2.world =
        (.error (.language .outOfMemory), childReturned safety after) := by
    have facts := (parent_established safety).taken.native (by rw [rows_count]; decide)
    simp only [recursivePrimitives, dispatcher_snapshot]
    rw [facts.reads]
    exact borrowed_failure (input := NativeRecursion.operand) (address := (parent safety).normalized.address) _ _ _ _ (constants safety _ (parent_established safety).taken 4 (Or.inr (Or.inr rfl))).1
      (parent_iszero safety).1 (xor_query safety).1 childCall
  simp only [Call.continuation, Interner.FindCode.controlMiss, Caller.execution, OwnedCall.execution,
    show (parent safety).request.item.kind = 1 from rfl, beq_self_eq_true, Bool.and_self, ↓reduceIte,
    graph, scope, simplified, bind, Effect.bind]

/-- The manually selected child is replaced by the actual recursive family.
Every sufficient depth runs the identical native parent and outer cleanup. -/
theorem root_equivalent (safety : Bool) (depth : Nat) : recursiveRoot safety (depth + 2) = complete safety := by
  obtain ⟨after, called, _⟩ := child_contract safety
  have established := parent_established safety
  have room : Interner.Queries.queries.atCapacity (parent safety).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ established.constructed.projected, rows_count]; decide
  have same : (parent safety).invoked (recursivePrimitives safety (depth + 1) rootSource) =
      (parent safety).invoked (parentPrimitives safety) :=
    same_call _ _ _ (calls_observed safety false) established.item.graph room rfl
      ((parent_continuation safety depth after called).trans (RecursiveBorrowedTests.parent_continuation safety after called).symm)
  have literal : Arguments.prepare [4] (ready safety) = (.ok rootSource, (parent safety).before) := by
    simpa only [parent, rootArguments] using
      (Prod.ext (literals_observed safety).1 rfl : rootArguments safety = (.ok rootSource, (rootArguments safety).2))
  rw [recursiveRoot, children, show depth + 2 = (depth + 1) + 1 from rfl, operation_succ]
  rw [Arguments.operation_prepared _ _ _ _ _ _ _ _ _ _ _ literal]
  rw [complete, Arguments.operation_prepared _ _ _ _ _ _ _ _ _ _ _ literal]
  exact congrArg (Arguments.returned [4] (ready safety).memory.memory.nextId) same

theorem binary_simplifier (safety xor : Bool) (depth : Nat) :
    (recursivePrimitives safety depth BinaryPreludeTests.source (BinaryPreludeTests.call safety xor).address (BinaryPreludeTests.call safety xor).native).simplify
      (BinaryPreludeTests.call safety xor).key (BinaryPreludeTests.call safety xor).normalized (BinaryPreludeTests.call safety xor).taken.2.world = (.ok none, (BinaryPreludeTests.call safety xor).taken.2.world) := by
  have dispatch : (fun (input : Nested.OperandRead (GraphAction (Publication.Effects Nat))) (address : Nat) (constructors : Constructors (Publication.Effects Nat)) =>
      Dispatch.simplifyWithInputs (Nested.storageReads (ReachablePrefixTests.cells safety 3)) constructors 64 (BinaryPreludeTests.opcode xor) [0, 1] debug input address) =
      (fun _ _ _ world => (.ok none, world)) := by
    cases safety <;> cases xor <;> insertion_kernel_rfl
  have prior := ReachablePrefixTests.initialized_prefix safety 3 (by decide)
  have facts := (BinaryPreludeTests.established safety xor).taken.native (by rw [prior.count]; decide)
  simp only [recursivePrimitives, dispatcher_snapshot]
  rw [facts.reads]
  change (Dispatch.simplifyWithInputs (Interner.representativeReads (BinaryPreludeTests.call safety xor).taken.2.world.graph)
    (children safety depth) 64 (BinaryPreludeTests.opcode xor) [0, 1] debug operand (BinaryPreludeTests.call safety xor).normalized.address) (BinaryPreludeTests.call safety xor).taken.2.world = _
  have reads : Interner.representativeReads (BinaryPreludeTests.call safety xor).taken.2.world.graph =
      Nested.storageReads (ReachablePrefixTests.cells safety 3) := by
    simp only [Interner.representativeReads, (BinaryPreludeTests.established safety xor).taken.projected]
  rw [reads]
  exact congrFun (congrFun (congrFun (congrFun dispatch operand) (BinaryPreludeTests.call safety xor).normalized.address) (children safety depth)) _

/-- A spare-capacity insertion never invokes either growth allocator. The
uniform recursive context therefore performs the same full binary publication. -/
theorem binary_insertion (safety xor : Bool) :
    Native.insert ops failing safety 7 6 BinaryPreludeTests.source (BinaryPreludeTests.call safety xor).address Insertion.Tests.model
      (BinaryPreludeTests.call safety xor).native (BinaryPreludeTests.call safety xor).key (BinaryPreludeTests.call safety xor).normalized true (some growth) (BinaryPreludeTests.call safety xor).taken.2.world =
    Native.insert ops CallerGrowingChainTests.allocate safety 7 6 BinaryPreludeTests.source (BinaryPreludeTests.call safety xor).address Insertion.Tests.model
      (BinaryPreludeTests.call safety xor).native (BinaryPreludeTests.call safety xor).key (BinaryPreludeTests.call safety xor).normalized true none (BinaryPreludeTests.call safety xor).taken.2.world := by
  cases safety <;> cases xor <;> insertion_kernel_rfl

theorem binary_equivalent (safety xor : Bool) (depth : Nat) :
    (children safety (depth + 1)).operation (BinaryPreludeTests.opcode xor) [0, 1] debug (BinaryPreludeTests.initial safety) = BinaryPreludeTests.full safety xor := by
  have established := BinaryPreludeTests.established safety xor
  have prior := ReachablePrefixTests.initialized_prefix safety 3 (by decide)
  have room : Interner.Queries.queries.atCapacity (BinaryPreludeTests.call safety xor).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ established.constructed.projected, prior.count]; decide
  have scope : (BinaryPreludeTests.call safety xor).taken.2.scope.slice = some (BinaryPreludeTests.call safety xor).normalized := by rw [established.entry.origin.scope]
  have current := miss_continuation (BinaryPreludeTests.call safety xor) (recursivePrimitives safety depth BinaryPreludeTests.source (BinaryPreludeTests.call safety xor).address (BinaryPreludeTests.call safety xor).native)
    scope rfl (binary_simplifier safety xor depth)
  have old := miss_continuation (BinaryPreludeTests.call safety xor) (BinaryPreludeTests.primitives safety xor (BinaryPreludeTests.call safety xor).address (BinaryPreludeTests.call safety xor).native)
    scope rfl (BinaryPreludeTests.simplified safety xor)
  have sameContinuation : (BinaryPreludeTests.call safety xor).continuation (recursivePrimitives safety depth BinaryPreludeTests.source (BinaryPreludeTests.call safety xor).address (BinaryPreludeTests.call safety xor).native) =
      (BinaryPreludeTests.call safety xor).continuation (BinaryPreludeTests.primitives safety xor (BinaryPreludeTests.call safety xor).address (BinaryPreludeTests.call safety xor).native) := by
    rw [current, old]
    simp only [handoff, graph, scope, bind, Effect.bind]
    exact congrArg (fun ran =>
      (ran.1, { (BinaryPreludeTests.call safety xor).taken.2 with
        world := ran.2
        scope := { (BinaryPreludeTests.call safety xor).taken.2.scope with slice := some (BinaryPreludeTests.call safety xor).normalized, handedOff := true } }))
      (binary_insertion safety xor)
  have same := same_call _ _ _ (BinaryPreludeTests.prefix_observed safety xor).2.1 established.item.graph room
    (by cases xor <;> rfl) sameContinuation
  have literal : Arguments.prepare [0, 1] (BinaryPreludeTests.initial safety) = (.ok BinaryPreludeTests.source, (BinaryPreludeTests.call safety xor).before) := by
    simpa only [BinaryPreludeTests.call, BinaryPreludeTests.arguments] using
      (Prod.ext (BinaryPreludeTests.prefix_observed safety xor).1 rfl : BinaryPreludeTests.arguments safety = (.ok BinaryPreludeTests.source, (BinaryPreludeTests.arguments safety).2))
  rw [children, operation_succ, Arguments.operation_prepared _ _ _ _ _ _ _ _ _ _ _ literal]
  rw [BinaryPreludeTests.full, Arguments.operation_prepared _ _ _ _ _ _ _ _ _ _ _ literal]
  exact congrArg (Arguments.returned [0, 1] (BinaryPreludeTests.initial safety).memory.memory.nextId) same

theorem xor_simplifier (safety : Bool) (depth : Nat) :
    (recursivePrimitives safety depth xorSource (xorCall safety).address (xorCall safety).native).simplify
      (xorCall safety).key (xorCall safety).normalized (xorCall safety).taken.2.world = (.ok none, (xorCall safety).taken.2.world) :=
  binary_simplifier safety true depth

theorem xor_insertion (safety : Bool) :
    Native.insert ops failing safety 7 6 xorSource (xorCall safety).address Insertion.Tests.model
      (xorCall safety).native (xorCall safety).key (xorCall safety).normalized true (some growth) (xorCall safety).taken.2.world =
    Native.insert ops CallerGrowingChainTests.allocate safety 7 6 xorSource (xorCall safety).address Insertion.Tests.model
      (xorCall safety).native (xorCall safety).key (xorCall safety).normalized true none (xorCall safety).taken.2.world :=
  binary_insertion safety true

theorem xor_equivalent (safety : Bool) (depth : Nat) :
    (children safety (depth + 1)).operation 24 [0, 1] debug (initial safety) = xorFull safety :=
  binary_equivalent safety true depth

/-- Both calls use one recursive context. The second input contains the ID
returned by the actual first call, in that call's reached native world. -/
def program (safety : Bool) (depth : Nat) : Except Fault NodeId × World (Publication.Effects Nat) :=
  (do let _ ← ReachablePrefixTests.sequence (children safety depth) 3
      let id ← (children safety depth).operation 24 [0, 1] debug
      (children safety depth).operation 21 [id] debug) (CallerInputTests.world safety)

theorem program_equivalent (safety : Bool) (depth : Nat) : program safety (depth + 2) = complete safety := by
  have first : (children safety (depth + 2)).operation 24 [0, 1] debug (initial safety) = (.ok 4, ready safety) :=
    (xor_equivalent safety (depth + 1)).trans (Prod.ext (xor_contract safety).1 (by unfold ready; rfl))
  exact (Effect.bind_success _ _ _ _ _ (prefix_result safety (depth + 1) 3 (by decide))).trans
    ((Effect.bind_success _ _ _ _ _ first).trans (root_equivalent safety depth))

/-- The complete recursive program, at every sufficient observation depth,
derives its result, reached native graph, surviving borrow, parent cleanup and
old word observations. Native reads are those reached by this execution. The
initial four rows come from full constructors after native initialization. -/
theorem program_contract (safety : Bool) (depth : Nat) :
    (program safety (depth + 2)).1 = .error (.language .outOfMemory) ∧
    GraphFacts safety ReachablePrefixTests.backing 5 (program safety (depth + 2)).2 (rows safety) ∧
    Good childSource [0, 1] (program safety (depth + 2)).2 ∧
    (program safety (depth + 2)).2.memory.memory.heap.lookup rootSource.allocation = none ∧
    (∀ id cell, (ready safety).memory.memory.heap.lookup id = some cell →
      (program safety (depth + 2)).2.memory.memory.heap.lookup id = some cell) ∧
    (∀ id, (program safety (depth + 2)).2.graph.read id = (ready safety).graph.read id) ∧
    (∀ id, id = 0 ∨ id = 1 →
      Constant.value (xorCall safety).taken.2.world.memory.memory (Owner.headerAddress ⟨6, 0⟩) id = .ok (.ok none) ∧
      Operation.run (xorCall safety).taken.2.world.memory.memory (Owner.headerAddress ⟨6, 0⟩) id 24 = .ok (.ok none) ∧
      Constant.value (child safety).taken.2.world.memory.memory (Owner.headerAddress ⟨6, 0⟩) id = .ok (.ok none)) ∧
    Constant.value (parent safety).taken.2.world.memory.memory (Owner.headerAddress ⟨6, 0⟩) 4 = .ok (.ok none) ∧
    Operation.run (parent safety).taken.2.world.memory.memory (Owner.headerAddress ⟨6, 0⟩) 4 21 = .ok (.ok none) ∧
    Operation.run (parent safety).taken.2.world.memory.memory (Owner.headerAddress ⟨6, 0⟩) 4 24 =
      .ok (.ok (some (Operation.returned xorOperands))) := by
  rw [program_equivalent]
  obtain ⟨result, facts, borrow, native, words, reads⟩ := composition safety
  exact ⟨result, facts, borrow, (complete_contract safety).2.2.2.2.1, native, words, reads⟩

theorem root_one (safety : Bool) : recursiveRoot safety 1 =
    (.error (.language .unsupported), (parent safety).taken.2.world) := by
  have established := parent_established safety
  have scope := established.entry.origin.scope
  have room : Interner.Queries.queries.atCapacity (parent safety).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ established.constructed.projected, rows_count]; decide
  have simplified : (recursivePrimitives safety 0 rootSource (parent safety).address (parent safety).native).simplify
      (parent safety).key (parent safety).normalized (parent safety).taken.2.world =
        (.error (.language .unsupported), (parent safety).taken.2.world) := by
    have facts := established.taken.native (by rw [rows_count]; decide)
    simp only [recursivePrimitives, dispatcher_snapshot]
    rw [facts.reads]
    exact borrowed_failure (input := NativeRecursion.operand) (address := (parent safety).normalized.address) _ _ _ _ (constants safety _ established.taken 4 (Or.inr (Or.inr rfl))).1
      (parent_iszero safety).1 (xor_query safety).1 rfl
  have continuation : (parent safety).continuation (recursivePrimitives safety 0 rootSource (parent safety).address (parent safety).native) =
      (.error (.language .unsupported), (parent safety).taken.2) := by
    simp only [Call.continuation, Interner.FindCode.controlMiss, Caller.execution, OwnedCall.execution,
      show (parent safety).request.item.kind = 1 from rfl, beq_self_eq_true, Bool.and_self, ↓reduceIte,
      graph, scope, simplified, bind, Effect.bind]
    rw [← scope]
  have routed := (parent safety).route (recursivePrimitives safety 0 rootSource) (calls_observed safety false)
    established.item.graph room rfl
  rw [continuation] at routed
  have result : (parent safety).invoked (recursivePrimitives safety 0 rootSource) =
      (.error (.language .unsupported), (parent safety).taken.2) := routed
  have literal : Arguments.prepare [4] (ready safety) = (.ok rootSource, (parent safety).before) := by
    simpa only [parent, rootArguments] using
      (Prod.ext (literals_observed safety).1 rfl : rootArguments safety = (.ok rootSource, (rootArguments safety).2))
  rw [recursiveRoot, children, show 1 = 0 + 1 from rfl, operation_succ,
    Arguments.operation_prepared _ _ _ _ _ _ _ _ _ _ _ literal]
  change Arguments.returned [4] _ ((parent safety).invoked (recursivePrimitives safety 0 rootSource)) = _
  rw [result]; rfl

theorem program_one (safety : Bool) : program safety 1 =
    (.error (.language .unsupported), (parent safety).taken.2.world) := by
  have first : (children safety 1).operation 24 [0, 1] debug (initial safety) = (.ok 4, ready safety) :=
    (xor_equivalent safety 0).trans (Prod.ext (xor_contract safety).1 (by unfold ready; rfl))
  exact (Effect.bind_success _ _ _ _ _ (prefix_result safety 0 3 (by decide))).trans
    ((Effect.bind_success _ _ _ _ _ first).trans (root_one safety))

/-- Exhaustion after publication retains the reached graph and live parent
owners. It neither rolls back the XOR nor invents ordinary native cleanup. -/
theorem incomplete_retains_parent (safety : Bool) :
    ordinary (program safety 1).1 = false ∧
    Held 7 rootSource [4] (parent safety).normalized (program safety 1).2 ∧
    GraphFacts safety ReachablePrefixTests.backing 5 (program safety 1).2 (rows safety) ∧
    ∃ cell, (program safety 1).2.memory.memory.heap.lookup rootSource.allocation = some cell ∧ cell.stack = true := by
  rw [program_one]
  obtain ⟨cell, found, stack⟩ := literal_stack safety
  have established := parent_established safety
  exact ⟨rfl, established.entry.origin.held, established.taken, cell,
    established.entry.origin.memory _ _ (established.item.memory _ _ found), stack⟩

/-- Exhaustion before the first constructor retains the initialized empty graph. -/
theorem program_zero (safety : Bool) : program safety 0 =
    (.error (.language .unsupported), CallerInputTests.world safety) := by rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.Tests
