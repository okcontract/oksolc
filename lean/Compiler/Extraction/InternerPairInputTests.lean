/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RulePairInputProgram
import Compiler.Extraction.InternerAlgebraicInputTests
import Compiler.Extraction.InternerShiftInputTests
import Compiler.Extraction.InternerNativeConstantTests
import Compiler.Extraction.InternerNativeGraphPublication

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.PairInput.Tests
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops cells lifetime GraphFacts)
open RecursiveTests (debug)

attribute [local irreducible] Arguments.operation ConstructorItem.constant

/-- The two source orders keep the returned child ID in its actual slot. This
check reaches the outer call independently of the failing-child endpoints. -/
theorem after_child (context : Context σ) (before after : World σ) (id operand : NodeId)
    (debug : AssemblyItem.Fields.Values)
    (called : (constructors context).constant 1 debug before = (.ok id, after)) :
    oppositeOuter context Dispatch.opSHL 1 0 operand debug before =
      Arguments.operation context.external context.budget context.allocator context.primitives context.queries
        Dispatch.opSHL [id, operand] debug after ∧
    addMaterializedDifference context operand 99 1 debug before =
      Arguments.operation context.external context.budget context.allocator context.primitives context.queries
        Dispatch.opADD [operand, id] debug after := by
  constructor
  · exact Effect.bind_success _ _ _ _ _ called
  · exact Effect.bind_success _ _ _ _ _ called

/-- These source literals run the complete constant child through nonempty
backing growth OOM. Materialization and the first-element shift both retain the
actual reached graph and live parent, without allocating the outer literal. -/
theorem actual_failure (safety materialized : Bool) : ∃ after,
    (if materialized then addMaterializedDifference (ShiftInput.Tests.context safety) 0 99 1 debug
      else oppositeOuter (ShiftInput.Tests.context safety) Dispatch.opSHL 1 0 0 debug)
        (RecursiveTests.child safety).before =
      (.error (.language .outOfMemory), RecursiveTests.childReturned safety after) ∧
    Held 7 RecursiveTests.rootSource [0, 0] (RecursiveTests.parent safety).normalized
      (RecursiveTests.childReturned safety after) ∧
    GraphFacts safety ReachablePrefixTests.backing 5 (RecursiveTests.childReturned safety after) (RecursiveNonemptyTests.rows safety) ∧
    (∀ id native, (RecursiveTests.child safety).before.memory.memory.heap.lookup id = some native →
      (RecursiveTests.childReturned safety after).memory.memory.heap.lookup id = some native) := by
  obtain ⟨after, called, facts, _, native, registry⟩ := RecursiveTests.child_contract safety
  have forwarded : (constructors (ShiftInput.Tests.context safety)).constant 1 debug
      (RecursiveTests.child safety).before = (.error (.language .outOfMemory), RecursiveTests.childReturned safety after) := by
    rw [constant_forwarded, ShiftInput.Tests.child_forwarded, called]
  refine ⟨after, ?_, RecursiveTests.held_after_child safety _ facts.valid native registry, facts, native⟩
  cases materialized
  · exact first_error _ _ _ _ _ _ _ _ forwarded
  · exact second_error _ _ _ _ _ _ _ _ forwarded

open RecursiveNonemptyTests
open AlgebraicInput.Tests (publishing)

def afterPublication (safety : Bool) := Arguments.prepare [0, 4] (ready safety)

theorem publication_literal (safety : Bool) :
    afterPublication safety = (.ok rootSource, (afterPublication safety).2) := by
  apply Prod.ext
  · cases safety <;> insertion_kernel_rfl
  · rfl

/-- A successful actual publication, not a callback assumption, supplies ID 4
and the fifth graph row to two second-element source initializers. The exposed
outer call includes its native item, normalization, insertion and cleanup.
Its complete result is still a recursive obligation. -/
theorem actual_publication_input (safety materialized : Bool) :
    Arguments.Prepared [0, 4] (ready safety) rootSource (afterPublication safety).2 ∧
    (if materialized then addMaterializedDifference (publishing safety) 0 99 0 debug
      else subtractConstant (publishing safety) 0 0 debug) (initial safety) =
      Arguments.returned [0, 4] (ready safety).memory.memory.nextId
        (ConstructorItem.operation (Publication.external ops.arguments) 160 7 ((publishing safety).primitives rootSource)
          Interner.Queries.queries rootSource Dispatch.opADD [0, 4] debug (afterPublication safety).2) ∧
    GraphFacts safety ReachablePrefixTests.backing 5 (ready safety) (rows safety) ∧
    (afterPublication safety).2.graph = (ready safety).graph := by
  have child := AlgebraicInput.Tests.published_child safety
  have forwarded : (constructors (publishing safety)).constant 0 debug (initial safety) = (.ok 4, ready safety) := child.1
  have reached := second_input (publishing safety) Dispatch.opADD 0 4
    ((constructors (publishing safety)).constant 0 debug) debug
    (initial safety) (ready safety) (afterPublication safety).2 rootSource
    forwarded child.2.valid (publication_literal safety)
  refine ⟨reached.1, ?_, child.2, reached.1.graph⟩
  cases materialized <;> exact reached.2

/-- Checked initializer arithmetic rejects before any native child, retaining
the exact entry world. Such rejection is not a successful compilation. -/
theorem arithmetic_rejections (context : Context σ) (before : World σ) (debug : AssemblyItem.Fields.Values) :
    modPower context 0 0 debug before = (.error (.language .safetyFault), before) ∧
    oppositeOuter context Dispatch.opSHL 0 1 0 debug before = (.error (.language .safetyFault), before) ∧
    reassociateConstants context Dispatch.opSUB 0 0 0 debug before = (.error (.language .safetyFault), before) := by
  exact ⟨rfl, rfl, rfl⟩

/-- Reuse the actual literal returned by constant publication for the source
ADD continuation. The request changes; its native allocation does not. -/
def addParent (safety : Bool) : RecursiveTests.Call :=
  ⟨Interner.constructorCode.operationRequest 1 [0, 4], rootSource, (afterPublication safety).2⟩

def addContext (safety : Bool) (depth : Nat) :=
  NativeRecursion.context (childContext safety) 6 64 (NativeRecursion.ConstantTests.children safety depth) debug

attribute [local irreducible] ready afterPublication rootArguments

theorem add_observed (safety : Bool) : (addParent safety).observations = (addParent safety).expected := by
  cases safety <;> insertion_kernel_rfl

theorem add_established (safety : Bool) :
    (addParent safety).Established safety ReachablePrefixTests.backing 5 (rows safety) :=
  (addParent safety).establish safety ReachablePrefixTests.backing 5 (rows safety)
    (by simpa only [addParent, afterPublication, parent, rootArguments] using (parent_literal safety).2)
    (by rw [rows_count]; decide)
    (by simpa only [addParent, afterPublication, parent, rootArguments] using (parent_literal safety).1.good)
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) (add_observed safety)

/-- The ordered source dispatcher reads the published zero before selecting
ADD's identity rule. No later query or recursive constructor is reached. -/
theorem add_identity (reads : Nested.Reads) (constructors : NativeRecursion.Constructors (Publication.Effects Nat))
    (before : World (Publication.Effects Nat))
    (left : reads.constant 0 = .ok none) (right : reads.constant 4 = .ok (some 0))
    (input : Nested.OperandRead (GraphAction (Publication.Effects Nat))) (address : Nat) :
    (Dispatch.simplifyWithInputs reads constructors 64 1 [0, 4] debug input address) before =
      (.ok (some 0), before) := by
  have collected : Dispatch.collectConstants reads [0, 4] = .ok none := by
    unfold Dispatch.collectConstants; rw [left]; rfl
  have first : (Dispatch.constantStage reads constructors 1 [0, 4] debug) before = (.ok none, before) := by
    simp only [Dispatch.constantStage, collected]; rfl
  have selected : zigSelect 1 .constants ⟨none, some 0, false⟩ = some .left := by insertion_kernel_rfl
  have binary : (Dispatch.binaryStageWithInputs reads constructors 64 1 0 4 debug Dispatch.defaultOptions input) before =
      (.ok (some 0), before) := by
    unfold Dispatch.binaryStageWithInputs
    simp only [left, right, Nested.readAction, bind, Effect.bind, selected, zigApply, pure, Effect.pure]
  unfold Dispatch.simplifyWithInputs Dispatch.simplifyOptionsWithInputs
  simp only [Dispatch.orNext, bind, Effect.bind, first, binary]
  rfl

theorem add_simplified (safety : Bool) (depth : Nat) :
    ((addContext safety depth).primitives rootSource (addParent safety).address (addParent safety).native).simplify
      (addParent safety).key (addParent safety).normalized (addParent safety).taken.2.world =
        (.ok (some 0), (addParent safety).taken.2.world) := by
  have facts := (add_established safety).taken
  simp only [addContext, NativeRecursion.dispatcher_snapshot]
  rw [(facts.native (by rw [rows_count]; decide)).reads]
  exact add_identity _ _ _ (first_constant safety _ facts).1 (zero_constant safety _ facts).1 _ _

def addPublished (safety : Bool) := Publication.freshWorld (addParent safety).key (addParent safety).normalized 0
  ((addParent safety).taken.2.world.memory.effects.allocator * 10 + 8) (addParent safety).taken.2.world

def addReturned (safety : Bool) :=
  let reached := (addParent safety).returnedWorld (addPublished safety)
  { reached with memory := { reached.memory with
    memory := Compiler.ZigAir.Memory.cleanup (ready safety).memory.memory.nextId reached.memory.memory } }

def addRoot (safety : Bool) (depth : Nat) :=
  (NativeRecursion.ConstantTests.children safety (depth + 1)).operation 1 [0, 4] debug (ready safety)

theorem add_literal (safety : Bool) :
    Arguments.Prepared [0, 4] (ready safety) rootSource (addParent safety).before := by
  simpa only [addParent, afterPublication, rootArguments] using (parent_literal safety).1

/-- The identity result publishes the actual normalized key. Its absence and
separation follow from entry lookup and normalization, before any return. -/
theorem add_publication (safety : Bool) :
    Publication.publish ops.probe ops.arguments 7 rootSource (addParent safety).key (addParent safety).normalized 0
      (addParent safety).taken.2.world = (.ok (), addPublished safety) ∧
    NativeGraph.Facts safety 7 6 ⟨ReachablePrefixTests.backing, 0⟩ 5 (addPublished safety) (rows safety) := by
  have established := add_established safety
  have facts := established.taken.native (by rw [rows_count]; decide)
  have custody := established.entry.graph_custody _ established.constructed.resident
  have absent : (addParent safety).taken.2.world.memory.effects.keys (addParent safety).key = none := by
    have missed := (addParent safety).prefix_results (add_observed safety) |>.2.2.2.2.2.2.1
    have table : (addParent safety).taken.2.world.graph.table (addParent safety).key = none := by
      rw [established.entry.origin.graph, established.item.graph]; exact missed
    rw [facts.linked] at table
    cases found : (addParent safety).taken.2.world.memory.effects.keys (addParent safety).key with
    | none => rfl
    | some old => simp only [OwnedKeys.view, found, Option.map_some] at table; cases table
  have fresh : OwnedKeys.Fresh (addParent safety).taken.2.world.memory.effects.keys (addParent safety).key
      ⟨(addParent safety).normalized.address, 0⟩ := by
    intro query old found incoming nonempty alias
    exact custody.apart query old found nonempty ⟨incoming, alias.symm⟩
  exact facts.publish_absent ops.probe ops.arguments rootSource (addParent safety).key (addParent safety).normalized 0
    ((addParent safety).taken.2.world.memory.effects.allocator * 10 + 8) rfl absent custody.live fresh
    (custody.operands (by change [0, 4] ≠ []; decide)) rfl

/-- Complete the same native ADD through publication, handoff, detached lookup
destruction and the caller/item/literal returns. -/
theorem add_result (safety : Bool) (depth : Nat) : addRoot safety depth = (.ok 0, addReturned safety) := by
  have established := add_established safety
  have scope := established.entry.origin.scope
  have publication := (add_publication safety).1
  have continuation :
      (addParent safety).continuation ((addContext safety depth).primitives rootSource
        (addParent safety).address (addParent safety).native) =
      (.ok 0, ⟨addPublished safety, ⟨some (addParent safety).lookup, some (addParent safety).normalized, true⟩⟩) := by
    let resumed : Action (Publication.Effects Nat) NodeId := do
      let _ ← graph (fun slice => Publication.publish ops.probe ops.arguments 7 rootSource (addParent safety).key slice 0)
      handoff
      pure 0
    have asResumed :
        (addParent safety).continuation ((addContext safety depth).primitives rootSource
          (addParent safety).address (addParent safety).native) = resumed (addParent safety).taken.2 := by
      simp only [RecursiveTests.Call.continuation, Interner.FindCode.controlMiss, Caller.execution, OwnedCall.execution,
        show (addParent safety).request.item.kind = 1 from rfl, beq_self_eq_true, Bool.and_self, ↓reduceIte,
        graph, scope, add_simplified, bind, Effect.bind, resumed]
      rfl
    rw [asResumed]
    simp only [resumed, graph, scope, bind, Effect.bind, publication, handoff, pure, Effect.pure]
  have room : Interner.Queries.queries.atCapacity (addParent safety).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ established.constructed.projected, rows_count]; decide
  have routed := (addParent safety).route ((addContext safety depth).primitives rootSource)
    (add_observed safety) established.item.graph room rfl
  rw [continuation] at routed
  have closed := deinit_detached (Publication.external ops.arguments) 7
    (⟨addPublished safety, ⟨some (addParent safety).lookup, some (addParent safety).normalized, true⟩⟩ : State _)
    (addParent safety).lookup rfl established.entry.origin.detached
  simp only [OwnedCall.finish, ordinary, ↓reduceIte, OwnedCall.cleanup, closed] at routed
  have literal : Arguments.prepare [0, 4] (ready safety) = (.ok rootSource, (addParent safety).before) := by
    simpa only [afterPublication, addParent] using publication_literal safety
  rw [addRoot, NativeRecursion.ConstantTests.children, NativeRecursion.operation_succ,
    Arguments.operation_prepared _ _ _ _ _ _ _ _ _ _ _ literal]
  change Arguments.returned [0, 4] _ ((addParent safety).invoked ((addContext safety depth).primitives rootSource)) = _
  rw [routed]; rfl

/-- Publication keeps the reached native cells; captured returns remove only
stack locals. Derive the surviving caller array and final query fields from
those frames, without a final-heap observation. -/
theorem add_contract (safety : Bool) (depth : Nat) :
    (addRoot safety depth).1 = .ok 0 ∧
    NativeGraph.Facts safety 7 6 ⟨ReachablePrefixTests.backing, 0⟩ 5 (addRoot safety depth).2 (rows safety) ∧
    (addRoot safety depth).2.memory.memory.heap.lookup rootSource.allocation = none ∧
    (∀ id cell, (ready safety).memory.memory.heap.lookup id = some cell →
      (addRoot safety depth).2.memory.memory.heap.lookup id = some cell) ∧
    Good (CallerInputTests.argumentView false) [0] (addRoot safety depth).2 ∧
    (addRoot safety depth).2.graph.read = (ready safety).graph.read ∧
    (addRoot safety depth).2.memory.effects.keys = OwnedKeys.store (addParent safety).taken.2.world.memory.effects.keys
      (addParent safety).key ⟨(addParent safety).normalized.address, 0⟩ := by
  have literal := add_literal safety
  have prior := (zero_contract safety).2.1.native (by rw [rows_count]; decide)
  have established := add_established safety
  obtain ⟨ownerCell, ownerFound, _, _⟩ := prior.ownerLive
  have ownerOlder := (Compiler.ZigAir.Memory.valid_lookup _ _ _ prior.valid.memory ownerFound).1
  have parentOlder : 6 < (addParent safety).before.memory.memory.nextId := by
    rw [literal.counter]; exact Nat.lt_trans ownerOlder (Nat.lt_succ_self _)
  have publishedFacts := (add_publication safety).2
  have scratchFacts := publishedFacts.cleanup ((addParent safety).before.memory.memory.nextId + 1)
    (Nat.lt_trans parentOlder (Nat.lt_succ_self _))
  have itemFacts := scratchFacts.cleanup (addParent safety).before.memory.memory.nextId parentOlder
  have finalFacts := itemFacts.cleanup (ready safety).memory.memory.nextId ownerOlder
  have publishedFrame : ∀ id cell, (addParent safety).before.memory.memory.heap.lookup id = some cell →
      (addPublished safety).memory.memory.heap.lookup id = some cell := by
    intro id cell found
    exact established.entry.origin.memory id cell (established.item.memory id cell found)
  have returnedFrame := (addParent safety).returned_frame (addPublished safety) literal.good.1 publishedFrame
  have frame : ∀ id cell, (ready safety).memory.memory.heap.lookup id = some cell →
      (addReturned safety).memory.memory.heap.lookup id = some cell := by
    intro id cell found
    exact (Compiler.ZigAir.Memory.cleanup_lookup_older _ _ id
      (Compiler.ZigAir.Memory.valid_lookup _ _ _ prior.valid.memory found).1).trans
      (returnedFrame _ _ (literal.frame id cell found))
  obtain ⟨cell, found, _⟩ := literal.storage (by decide)
  rw [add_result]
  refine ⟨rfl, finalFacts, ?_, frame,
    good_frame _ _ _ _ (caller_source safety) finalFacts.valid frame, ?_, rfl⟩
  · exact literal.retire [0, 4] _ _ rootSource (by decide) _ itemFacts.valid.memory
      ((returnedFrame _ _ found).trans found.symm)
  · change (addParent safety).taken.2.world.graph.read = _
    rw [established.entry.origin.graph, established.item.graph, literal.graph]

/-- The existing constant and materializer source initializers run after the
same full prefix, with their returned ID in the actual outer pair. -/
def publicationProgram (safety materialized : Bool) (depth : Nat) : Except Fault NodeId × World (Publication.Effects Nat) :=
  (do let _ ← ReachablePrefixTests.sequence (NativeRecursion.ConstantTests.children safety depth) 3
      let id ← if materialized then (NativeRecursion.ConstantTests.children safety depth).materialize 99 0 debug
        else (NativeRecursion.ConstantTests.children safety depth).constant 0 debug
      (NativeRecursion.ConstantTests.children safety depth).operation 1 [0, id] debug) (CallerInputTests.world safety)

/-- Reconcile the complete execution with the already admitted source literal
segments, including materialization and the subtraction constant expression. -/
theorem publication_source (safety materialized : Bool) (depth : Nat) :
    publicationProgram safety materialized (depth + 1) =
      (do let _ ← ReachablePrefixTests.sequence (NativeRecursion.ConstantTests.children safety (depth + 1)) 3
          if materialized then addMaterializedDifference (addContext safety depth) 0 99 0 debug
          else subtractConstant (addContext safety depth) 0 0 debug) (CallerInputTests.world safety) := by
  cases materialized <;> rfl

theorem publication_equivalent (safety materialized : Bool) (depth : Nat) :
    publicationProgram safety materialized (depth + 1) = addRoot safety depth := by
  rw [publication_source]
  have initialized :
      (if materialized then addMaterializedDifference (addContext safety depth) 0 99 0 debug
       else subtractConstant (addContext safety depth) 0 0 debug) (initial safety) = addRoot safety depth := by
    cases materialized <;> exact Effect.bind_success _ _ _ _ _ (NativeRecursion.ConstantTests.zero_equivalent safety depth)
  exact (Effect.bind_success _ _ _ _ _ (NativeRecursion.ConstantTests.prefix_result safety depth 3 (by decide))).trans initialized

/-- The published constant supplies both the real outer literal and the native
identity query. The same initialized recursive execution returns ID zero, keeps
all older cells/words and transfers the normalized key before retiring locals. -/
theorem publication_contract (safety materialized : Bool) (depth : Nat) :
    (publicationProgram safety materialized (depth + 1)).1 = .ok 0 ∧
    NativeGraph.Facts safety 7 6 ⟨ReachablePrefixTests.backing, 0⟩ 5
      (publicationProgram safety materialized (depth + 1)).2 (rows safety) ∧
    (publicationProgram safety materialized (depth + 1)).2.memory.memory.heap.lookup rootSource.allocation = none ∧
    (∀ id cell, (ready safety).memory.memory.heap.lookup id = some cell →
      (publicationProgram safety materialized (depth + 1)).2.memory.memory.heap.lookup id = some cell) ∧
    Good (CallerInputTests.argumentView false) [0] (publicationProgram safety materialized (depth + 1)).2 ∧
    (publicationProgram safety materialized (depth + 1)).2.graph.read = (ready safety).graph.read ∧
    (publicationProgram safety materialized (depth + 1)).2.memory.effects.keys =
      OwnedKeys.store (addParent safety).taken.2.world.memory.effects.keys (addParent safety).key
        ⟨(addParent safety).normalized.address, 0⟩ := by
  rw [publication_equivalent]
  exact add_contract safety depth

theorem publication_zero (safety materialized : Bool) : publicationProgram safety materialized 0 =
    (.error (.language .unsupported), CallerInputTests.world safety) := by rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.PairInput.Tests
