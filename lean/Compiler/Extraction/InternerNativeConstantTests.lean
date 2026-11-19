/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeRecursionTests
import Compiler.Extraction.InternerRecursiveNonemptyTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ConstantTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops lifetime growth GraphFacts)
open RecursiveTests (Call debug)
open RecursiveNonemptyTests

def children (safety : Bool) (depth : Nat) := NativeRecursion.unfold (childContext safety) 6 64 depth
def primitives (safety : Bool) (depth : Nat) (source : View) :=
  (context (childContext safety) 6 64 (children safety depth) debug).primitives source
def root (safety : Bool) (depth : Nat) :=
  (children safety depth).operation 20 [0, 4] debug (ready safety)

attribute [local irreducible] ready rootArguments childArguments Arguments.operation

/-- Constant failure and borrowed failure use the same admitted allocator and
constructor context. Their actual prefixes therefore share the checked route. -/
theorem context_same (safety : Bool) : childContext safety = RecursiveBorrowedTests.childContext safety := rfl

theorem prefix_result (safety : Bool) (depth n : Nat) (bounded : n < 4) :
    ReachablePrefixTests.sequence (children safety (depth + 1)) n (CallerInputTests.world safety) =
      (.ok (BitVec.ofNat 32 n), ReachablePrefixTests.before safety n) := by
  unfold children
  rw [context_same]
  exact NativeRecursion.Tests.prefix_result safety depth n bounded

/-- Push bypasses simplification. Its spare-capacity publication uses neither
growth allocator, so the same context supplies the constant and recursive calls. -/
theorem zero_insertion (safety : Bool) :
    Native.insert ops failing safety 7 6 ⟨0, 0, 0⟩ (zero safety).address Insertion.Tests.model
      (zero safety).native (zero safety).key (zero safety).normalized true (some growth) (zero safety).taken.2.world =
    Native.insert ops ReachablePrefixTests.allocate safety 7 6 ⟨0, 0, 0⟩ (zero safety).address Insertion.Tests.model
      (zero safety).native (zero safety).key (zero safety).normalized true none (zero safety).taken.2.world := by
  cases safety <;> insertion_kernel_rfl

theorem zero_equivalent (safety : Bool) (depth : Nat) :
    (children safety (depth + 1)).constant 0 debug (initial safety) = (.ok 4, ready safety) := by
  have established := zero_established safety
  have prior := ReachablePrefixTests.initialized_prefix safety 3 (by decide)
  have room : Interner.Queries.queries.atCapacity (zero safety).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ established.constructed.projected, prior.count]; decide
  have sameContinuation : (zero safety).continuation (primitives safety depth ⟨0, 0, 0⟩ (zero safety).address (zero safety).native) =
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
  have same : (zero safety).invoked (primitives safety depth ⟨0, 0, 0⟩) = (zero safety).invoked (zeroPrimitives safety) := by
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

theorem child_simplifier (safety : Bool) (depth : Nat) :
    (primitives safety depth childSource (child safety).address (child safety).native).simplify
      (child safety).key (child safety).normalized (child safety).taken.2.world = (.ok none, (child safety).taken.2.world) := by
  have facts := (child_established safety).taken.native (by rw [rows_count]; decide)
  simp only [primitives, NativeRecursion.dispatcher_snapshot]
  rw [facts.reads]
  exact iszero_miss (input := NativeRecursion.operand) (address := (child safety).normalized.address) _ _ _ (first_constant safety _ (child_established safety).taken).1
    (first_operation safety _ 21 (child_established safety).taken (by decide)).1
    (first_operation safety _ 24 (child_established safety).taken (by decide)).1
    (first_operation safety _ 3 (child_established safety).taken (by decide)).1

/-- The actual child uses the lower recursive family. Its guards derive that
no grandchild is reached, before the native nonempty growth attempt fails. -/
theorem child_equivalent (safety : Bool) (depth : Nat) :
    (children safety (depth + 1)).operation 21 [0] debug (parent safety).taken.2.world = childFull safety := by
  have established := child_established safety
  have room : Interner.Queries.queries.atCapacity (child safety).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ established.constructed.projected, rows_count]; decide
  have sameContinuation : (child safety).continuation (primitives safety depth childSource (child safety).address (child safety).native) =
      (child safety).continuation (childPrimitives safety childSource (child safety).address (child safety).native) := by
    simp only [Call.continuation, Interner.FindCode.controlMiss, Caller.execution, OwnedCall.execution,
      show (child safety).request.item.kind = 1 from rfl, beq_self_eq_true, Bool.and_self, ↓reduceIte,
      graph, established.entry.origin.scope, child_simplifier, childPrimitives, callerPrimitives,
      child_simplified, bind, Effect.bind]
    rfl
  have same : (child safety).invoked (primitives safety depth childSource) = (child safety).invoked (childPrimitives safety childSource) := by
    rw [(child safety).route _ (calls_observed safety true) established.item.graph room rfl,
      (child safety).route _ (calls_observed safety true) established.item.graph room rfl, sameContinuation]
  have literal : Arguments.prepare [0] (parent safety).taken.2.world = (.ok childSource, (child safety).before) := by
    simpa only [child, childArguments] using
      (Prod.ext (literals_observed safety).2.2.1 rfl : childArguments safety = (.ok childSource, (childArguments safety).2))
  rw [children, operation_succ, Arguments.operation_prepared _ _ _ _ _ _ _ _ _ _ _ literal]
  rw [childFull, Arguments.operation_prepared _ _ _ _ _ _ _ _ _ _ _ literal]
  exact congrArg (Arguments.returned [0] (parent safety).taken.2.world.memory.memory.nextId) same

theorem parent_continuation (safety : Bool) (depth : Nat) (after : Native.Frame Nat)
    (called : childFull safety = (.error (.language .outOfMemory), childReturned safety after)) :
    (parent safety).continuation (primitives safety (depth + 1) rootSource (parent safety).address (parent safety).native) =
      (.error (.language .outOfMemory), ⟨childReturned safety after, (parent safety).taken.2.scope⟩) := by
  have simplified : (primitives safety (depth + 1) rootSource (parent safety).address (parent safety).native).simplify
      (parent safety).key (parent safety).normalized (parent safety).taken.2.world =
        (.error (.language .outOfMemory), childReturned safety after) := by
    have facts := (parent_established safety).taken.native (by rw [rows_count]; decide)
    simp only [primitives, NativeRecursion.dispatcher_snapshot]
    rw [facts.reads]
    exact iszero_failure (input := NativeRecursion.operand) (address := (parent safety).normalized.address)
      (Interner.representativeReads (parent safety).taken.2.world.graph)
      (children safety (depth + 1)) (parent safety).taken.2.world (childReturned safety after)
      (first_constant safety _ (parent_established safety).taken).1 (parent_zero safety).1
      ((child_equivalent safety depth).trans called)
  simp only [Call.continuation, Interner.FindCode.controlMiss, Caller.execution, OwnedCall.execution,
    show (parent safety).request.item.kind = 1 from rfl, beq_self_eq_true, Bool.and_self, ↓reduceIte,
    graph, (parent_established safety).entry.origin.scope, simplified, bind, Effect.bind]

theorem root_equivalent (safety : Bool) (depth : Nat) : root safety (depth + 2) = complete safety := by
  obtain ⟨after, called, _⟩ := child_contract safety
  have established := parent_established safety
  have room : Interner.Queries.queries.atCapacity (parent safety).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ established.constructed.projected, rows_count]; decide
  have same : (parent safety).invoked (primitives safety (depth + 1) rootSource) =
      (parent safety).invoked (parentPrimitives safety) := by
    rw [(parent safety).route _ (calls_observed safety false) established.item.graph room rfl,
      (parent safety).route _ (calls_observed safety false) established.item.graph room rfl,
      parent_continuation safety depth after called, RecursiveNonemptyTests.parent_continuation safety after called]
  have literal : Arguments.prepare [0, 4] (ready safety) = (.ok rootSource, (parent safety).before) := by
    simpa only [parent, rootArguments] using
      (Prod.ext (literals_observed safety).1 rfl : rootArguments safety = (.ok rootSource, (rootArguments safety).2))
  rw [root, children, show depth + 2 = (depth + 1) + 1 from rfl, operation_succ,
    Arguments.operation_prepared _ _ _ _ _ _ _ _ _ _ _ literal]
  rw [complete, Arguments.operation_prepared _ _ _ _ _ _ _ _ _ _ _ literal]
  exact congrArg (Arguments.returned [0, 4] (ready safety).memory.memory.nextId) same

/-- The parent consumes the ID and world returned by the full constant call. -/
def program (safety : Bool) (depth : Nat) : Except Fault NodeId × World (Publication.Effects Nat) :=
  (do let _ ← ReachablePrefixTests.sequence (children safety depth) 3
      let id ← (children safety depth).constant 0 debug
      (children safety depth).operation 20 [0, id] debug) (CallerInputTests.world safety)

theorem program_equivalent (safety : Bool) (depth : Nat) : program safety (depth + 2) = complete safety :=
  (Effect.bind_success _ _ _ _ _ (prefix_result safety (depth + 1) 3 (by decide))).trans
    ((Effect.bind_success _ _ _ _ _ (zero_equivalent safety (depth + 1))).trans (root_equivalent safety depth))

/-- Publication supplies the native Push data used by the parent guard. The
actual recursive growth failure returns through child, parent and outer cleanup;
all final constant and operation reads follow from the reached graph invariant.
The initial four rows come from full constructors under the same context. -/
theorem program_contract (safety : Bool) (depth : Nat) :
    (program safety (depth + 2)).1 = .error (.language .outOfMemory) ∧
    NativeGraph.Facts safety 7 6 ⟨ReachablePrefixTests.backing, 0⟩ 5 (program safety (depth + 2)).2 (rows safety) ∧
    (program safety (depth + 2)).2.memory.memory.heap.lookup rootSource.allocation = none ∧
    (∀ id cell, (ready safety).memory.memory.heap.lookup id = some cell →
      (program safety (depth + 2)).2.memory.memory.heap.lookup id = some cell) ∧
    (∀ id, (program safety (depth + 2)).2.graph.read id = (ready safety).graph.read id) ∧
    (∀ id, Constant.value (program safety (depth + 2)).2.memory.memory (Owner.headerAddress ⟨6, 0⟩) id =
      .ok (Storage.constantProgram.run (rows safety) id)) ∧
    (∀ id opcode, Operation.run (program safety (depth + 2)).2.memory.memory (Owner.headerAddress ⟨6, 0⟩) id opcode =
      .ok ((Storage.operationProgram.run (rows safety) id opcode).map (Option.map Operation.returned))) ∧
    Constant.value (parent safety).taken.2.world.memory.memory (Owner.headerAddress ⟨6, 0⟩) 4 = .ok (.ok (some 0)) ∧
    ∃ after, (children safety (depth + 1)).operation 21 [0] debug (parent safety).taken.2.world =
        (.error (.language .outOfMemory), childReturned safety after) ∧
      Held 7 rootSource [0, 4] (parent safety).normalized (childReturned safety after) ∧
      (∀ id cell, (parent safety).taken.2.world.memory.memory.heap.lookup id = some cell →
        (childReturned safety after).memory.memory.heap.lookup id = some cell) := by
  rw [program_equivalent]
  obtain ⟨result, facts, _, dead, _, _, native, words⟩ := complete_contract safety
  have reached := facts.native (by rw [rows_count]; decide)
  obtain ⟨after, called, childFacts, _, _, childFrame, registered, _⟩ := child_contract safety
  exact ⟨result, reached, dead, native, words, reached.constants, reached.operations,
    (parent_zero safety).2, after, (child_equivalent safety depth).trans called,
    held_after_child safety _ childFacts.valid childFrame registered, childFrame⟩

/-- Depth exhaustion preserves the newly published Push and the reached parent
owners. It is an explicit nonordinary rejection, not a native allocation error. -/
theorem root_one (safety : Bool) : root safety 1 =
    (.error (.language .unsupported), (parent safety).taken.2.world) := by
  have established := parent_established safety
  have scope := established.entry.origin.scope
  have room : Interner.Queries.queries.atCapacity (parent safety).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ established.constructed.projected, rows_count]; decide
  have simplified : (primitives safety 0 rootSource (parent safety).address (parent safety).native).simplify
      (parent safety).key (parent safety).normalized (parent safety).taken.2.world =
        (.error (.language .unsupported), (parent safety).taken.2.world) := by
    have facts := (parent_established safety).taken.native (by rw [rows_count]; decide)
    simp only [primitives, NativeRecursion.dispatcher_snapshot]
    rw [facts.reads]
    exact iszero_failure (input := NativeRecursion.operand) (address := (parent safety).normalized.address) _ _ _ _ (first_constant safety _ established.taken).1 (parent_zero safety).1 rfl
  have continuation : (parent safety).continuation (primitives safety 0 rootSource (parent safety).address (parent safety).native) =
      (.error (.language .unsupported), (parent safety).taken.2) := by
    simp only [Call.continuation, Interner.FindCode.controlMiss, Caller.execution, OwnedCall.execution,
      show (parent safety).request.item.kind = 1 from rfl, beq_self_eq_true, Bool.and_self, ↓reduceIte,
      graph, scope, simplified, bind, Effect.bind]
    rw [← scope]
  have routed := (parent safety).route (primitives safety 0 rootSource) (calls_observed safety false)
    established.item.graph room rfl
  rw [continuation] at routed
  have result : (parent safety).invoked (primitives safety 0 rootSource) =
      (.error (.language .unsupported), (parent safety).taken.2) := routed
  have literal : Arguments.prepare [0, 4] (ready safety) = (.ok rootSource, (parent safety).before) := by
    simpa only [parent, rootArguments] using
      (Prod.ext (literals_observed safety).1 rfl : rootArguments safety = (.ok rootSource, (rootArguments safety).2))
  rw [root, children, show 1 = 0 + 1 from rfl, operation_succ,
    Arguments.operation_prepared _ _ _ _ _ _ _ _ _ _ _ literal]
  change Arguments.returned [0, 4] _ ((parent safety).invoked (primitives safety 0 rootSource)) = _
  rw [result]; rfl

theorem program_one (safety : Bool) : program safety 1 =
    (.error (.language .unsupported), (parent safety).taken.2.world) :=
  (Effect.bind_success _ _ _ _ _ (prefix_result safety 0 3 (by decide))).trans
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

theorem program_zero (safety : Bool) : program safety 0 =
    (.error (.language .unsupported), CallerInputTests.world safety) := by rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ConstantTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.EqualTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native RecursiveTests
open CallerGrowingChainTests (ops GraphFacts)
open ConstantTests (children primitives prefix_result zero_equivalent)

attribute [local irreducible] RecursiveNonemptyTests.ready rootArguments Arguments.operation

def root (safety : Bool) (depth : Nat) := (children safety depth).operation 20 [0, 0] debug (old safety)

/-- The equal-operands child is the same complete constant constructor under
the parent's actual recursive context. Push bypasses the unused simplifier. -/
theorem child_equivalent (safety : Bool) (depth : Nat) :
    (children safety (depth + 1)).constant 1 debug (child safety).before =
      ((childFull safety).1, (childFull safety).2.world) := by
  have established := child_established safety
  have room : Interner.Queries.queries.atCapacity (child safety).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ established.constructed.projected, RecursiveNonemptyTests.rows_count]; decide
  have continuation :
      (child safety).continuation (primitives safety depth ⟨0, 0, 0⟩ (child safety).address (child safety).native) =
      (child safety).continuation (childPrimitives safety (child safety).address (child safety).native) := by
    simp only [Call.continuation, Interner.FindCode.controlMiss, Caller.execution, OwnedCall.execution,
      show (child safety).request.item.kind = 2 from rfl, BitVec.reduceBEq, Bool.false_eq_true,
      Bool.true_and, ↓reduceIte, handoff, graph, established.entry.origin.scope,
      bind, Effect.bind, pure, Effect.pure]
    rfl
  have same := NativeRecursion.Tests.same_call (child safety) (primitives safety depth ⟨0, 0, 0⟩)
    (childPrimitives safety) (observed safety true) established.item.graph room rfl continuation
  rw [children, constant_succ]
  exact congrArg (fun ran => (ran.1, ran.2.world)) same

theorem parent_continuation (safety : Bool) (depth : Nat) (after : Native.Frame Nat)
    (called : childFull safety = (.error (.language .outOfMemory),
      ⟨childReturned safety after, ⟨none, some (child safety).normalized, true⟩⟩)) :
    (parent safety).continuation (primitives safety (depth + 1) rootSource (parent safety).address (parent safety).native) =
      (.error (.language .outOfMemory), ⟨childReturned safety after, (parent safety).taken.2.scope⟩) := by
  have established := parent_established safety
  have simplified : (primitives safety (depth + 1) rootSource (parent safety).address (parent safety).native).simplify
      (parent safety).key (parent safety).normalized (parent safety).taken.2.world =
        (.error (.language .outOfMemory), childReturned safety after) := by
    have facts := established.taken.native (by rw [RecursiveNonemptyTests.rows_count]; decide)
    simp only [ConstantTests.primitives, NativeRecursion.dispatcher_snapshot]
    rw [facts.reads]
    apply equal_failure (input := NativeRecursion.operand) (address := (parent safety).normalized.address)
      _ _ _ _ _ (parent_constant safety).1
    · simp only [Interner.representativeReads, established.taken.projected, Nested.storageReads]
    · exact (child_equivalent safety depth).trans (congrArg (fun ran => (ran.1, ran.2.world)) called)
  exact (parent safety).simplify_error _ _ _ rfl established.entry.origin.scope simplified

theorem root_equivalent (safety : Bool) (depth : Nat) : root safety (depth + 2) = complete safety := by
  obtain ⟨after, called, _⟩ := child_contract safety
  have established := parent_established safety
  have room : Interner.Queries.queries.atCapacity (parent safety).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ established.constructed.projected, RecursiveNonemptyTests.rows_count]; decide
  have same := NativeRecursion.Tests.same_call (parent safety) (primitives safety (depth + 1) rootSource)
    (parentPrimitives safety) (observed safety false) established.item.graph room rfl
    ((parent_continuation safety depth after called).trans (RecursiveTests.parent_continuation safety after called).symm)
  have literal : Arguments.prepare [0, 0] (old safety) = (.ok rootSource, (parent safety).before) := by
    change TemporaryArguments.prepare 0 0 (old safety) = (.ok rootSource, (rootArguments safety).2)
    simpa only [rootArguments] using
      (Prod.ext (root_observed safety).1 rfl : rootArguments safety = (.ok rootSource, (rootArguments safety).2))
  rw [root, children, operation_succ, Arguments.operation_prepared _ _ _ _ _ _ _ _ _ _ _ literal, complete_route]
  change Arguments.returned [0, 0] _ ((parent safety).invoked (primitives safety (depth + 1) rootSource)) = _
  rw [same]
  rfl

/-- Four native prefix operations and Push-zero fill the reached backing.
EQ(x,x) then calls Push-one in that same context and observes its growth OOM. -/
def program (safety : Bool) (depth : Nat) : Except Fault NodeId × World (Publication.Effects Nat) :=
  (do let _ ← ReachablePrefixTests.sequence (children safety depth) 3
      let _ ← (children safety depth).constant 0 debug
      (children safety depth).operation 20 [0, 0] debug) (CallerInputTests.world safety)

theorem program_equivalent (safety : Bool) (depth : Nat) : program safety (depth + 2) = complete safety :=
  (Effect.bind_success _ _ _ _ _ (prefix_result safety (depth + 1) 3 (by decide))).trans
    ((Effect.bind_success _ _ _ _ _ (zero_equivalent safety (depth + 1))).trans (root_equivalent safety depth))

theorem program_contract (safety : Bool) (depth : Nat) :
    (program safety (depth + 2)).1 = .error (.language .outOfMemory) ∧
    NativeGraph.Facts safety 7 6 ⟨ReachablePrefixTests.backing, 0⟩ 5
      (program safety (depth + 2)).2 (RecursiveNonemptyTests.rows safety) ∧
    (program safety (depth + 2)).2.memory.memory.heap.lookup rootSource.allocation = none ∧
    (∀ id cell, (old safety).memory.memory.heap.lookup id = some cell →
      (program safety (depth + 2)).2.memory.memory.heap.lookup id = some cell) ∧
    Good (CallerInputTests.argumentView false) [0] (program safety (depth + 2)).2 ∧
    (∀ id, (program safety (depth + 2)).2.graph.read id = (old safety).graph.read id) ∧
    ∃ after, (children safety (depth + 1)).constant 1 debug (child safety).before =
        (.error (.language .outOfMemory), childReturned safety after) ∧
      Held 7 rootSource [0, 0] (parent safety).normalized (childReturned safety after) ∧
      (∀ id cell, (parent safety).taken.2.world.memory.memory.heap.lookup id = some cell →
        (childReturned safety after).memory.memory.heap.lookup id = some cell) := by
  rw [program_equivalent]
  obtain ⟨failed, facts, graph, dead, _, _, frame, caller⟩ := complete_contract safety
  obtain ⟨after, called, childFacts, _, native, registry⟩ := child_contract safety
  exact ⟨failed, facts.native (by rw [RecursiveNonemptyTests.rows_count]; decide), dead, frame, caller,
    fun id => congrArg (fun heap => heap.read id) graph,
    after, (child_equivalent safety depth).trans (congrArg (fun ran => (ran.1, ran.2.world)) called),
    held_after_child safety _ childFacts.valid native registry, native⟩

/-- Exhaustion occurs at the reached constant child. It keeps the live parent
and literal owners, and cannot be identified with the child's ordinary OOM. -/
theorem root_one (safety : Bool) : root safety 1 =
    (.error (.language .unsupported), (parent safety).taken.2.world) := by
  have established := parent_established safety
  have room : Interner.Queries.queries.atCapacity (parent safety).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ established.constructed.projected, RecursiveNonemptyTests.rows_count]; decide
  have simplified : (primitives safety 0 rootSource (parent safety).address (parent safety).native).simplify
      (parent safety).key (parent safety).normalized (parent safety).taken.2.world =
        (.error (.language .unsupported), (parent safety).taken.2.world) := by
    have facts := established.taken.native (by rw [RecursiveNonemptyTests.rows_count]; decide)
    simp only [ConstantTests.primitives, NativeRecursion.dispatcher_snapshot]
    rw [facts.reads]
    apply equal_failure (input := NativeRecursion.operand) (address := (parent safety).normalized.address)
      _ _ _ _ _ (parent_constant safety).1
    · simp only [Interner.representativeReads, established.taken.projected, Nested.storageReads]
    · rfl
  have continuation := (parent safety).simplify_error _ _ _ rfl established.entry.origin.scope simplified
  have routed := (parent safety).route (primitives safety 0 rootSource) (observed safety false)
    established.item.graph room rfl
  rw [continuation] at routed
  have result : (parent safety).invoked (primitives safety 0 rootSource) =
      (.error (.language .unsupported), (parent safety).taken.2) := routed
  have literal : Arguments.prepare [0, 0] (old safety) = (.ok rootSource, (parent safety).before) := by
    change TemporaryArguments.prepare 0 0 (old safety) = (.ok rootSource, (rootArguments safety).2)
    simpa only [rootArguments] using
      (Prod.ext (root_observed safety).1 rfl : rootArguments safety = (.ok rootSource, (rootArguments safety).2))
  rw [root, children, show 1 = 0 + 1 from rfl, operation_succ,
    Arguments.operation_prepared _ _ _ _ _ _ _ _ _ _ _ literal]
  change Arguments.returned [0, 0] _ ((parent safety).invoked (primitives safety 0 rootSource)) = _
  rw [result]; rfl

theorem program_one (safety : Bool) : program safety 1 =
    (.error (.language .unsupported), (parent safety).taken.2.world) :=
  (Effect.bind_success _ _ _ _ _ (prefix_result safety 0 3 (by decide))).trans
    ((Effect.bind_success _ _ _ _ _ (zero_equivalent safety 0)).trans (root_one safety))

theorem exhaustion_retained (safety : Bool) :
    ordinary (program safety 1).1 = false ∧
    Held 7 rootSource [0, 0] (parent safety).normalized (program safety 1).2 ∧
    NativeGraph.Facts safety 7 6 ⟨ReachablePrefixTests.backing, 0⟩ 5
      (program safety 1).2 (RecursiveNonemptyTests.rows safety) := by
  rw [program_one]
  have established := parent_established safety
  exact ⟨rfl, established.entry.origin.held,
    established.taken.native (by rw [RecursiveNonemptyTests.rows_count]; decide)⟩

theorem program_zero (safety : Bool) : program safety 0 =
    (.error (.language .unsupported), CallerInputTests.world safety) := by rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.EqualTests
