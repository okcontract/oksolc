/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerViewInput
import Compiler.Extraction.InternerLiteralInputTests
import Compiler.Extraction.InternerLocalArgumentsTests
import Compiler.Extraction.InternerBorrowedConstructorTests
import Compiler.Extraction.InternerRecursiveBorrowedTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ViewInput.Tests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops lifetime GraphFacts)
open RecursiveTests (debug)

attribute [local irreducible] operation ConstructorItem.operation Arguments.operation
  RecursiveNonemptyTests.ready RecursiveNonemptyTests.rootArguments RecursiveNonemptyTests.childArguments

private abbrev addressed := Recursive.BorrowedConstructor.Tests.addressed
private def trace (context : PairInput.Context σ) (address : Nat) (nodes : List Dispatch.Tests.Probe)
    (opcode : Opcode) (values : List NodeId) (debug : AssemblyItem.Fields.Values) :=
  Dispatch.simplify (addressed address nodes) (constructors context) 64 opcode values debug
private def output (context : PairInput.Context σ) (address : Nat) (opcode : Opcode) (values : List NodeId)
    (debug : AssemblyItem.Fields.Values) (before : World σ) :=
  let ran := operation context ⟨address, 0, values.length⟩ opcode values debug before
  (ran.1.map some, ran.2)

theorem byte_site (context : PairInput.Context σ) (address : Nat) (debug : AssemblyItem.Fields.Values) (before : World σ) :
    trace context address [⟨none, some 26, [2, 3]⟩, ⟨some 255, none, []⟩, {}, {}] 22 [0, 1] debug before =
      output context address 26 [2, 3] debug before := by
  change (Dispatch.orNext (pure none) (Dispatch.orNext
    (do let id ← operation context ⟨address, 0, 2⟩ 26 [2, 3] debug; pure (some id)) (pure none))) before = _
  cases called : operation context ⟨address, 0, 2⟩ 26 [2, 3] debug before with
  | mk result after => cases result <;> simp only [output, List.length_cons, List.length_nil, Nat.reduceAdd, Dispatch.orNext, bind, Effect.bind, pure, Effect.pure, called, Except.map]

theorem comparison_sites (context : PairInput.Context σ) (address : Nat) (debug : AssemblyItem.Fields.Values)
    (before : World σ) (opcode : Opcode) (allowed : opcode = 20 ∨ opcode = 16 ∨ opcode = 18 ∨ opcode = 17 ∨ opcode = 19) :
    trace context address [⟨none, some 21, [1]⟩, ⟨none, some opcode, [2, 3]⟩, {}, {}] 21 [0] debug before =
      output context address opcode [2, 3] debug before := by
  have shape : trace context address [⟨none, some 21, [1]⟩, ⟨none, some opcode, [2, 3]⟩, {}, {}] 21 [0] debug =
      Dispatch.orNext (pure none) (Dispatch.orNext (pure none) (Dispatch.orNext
        (do let id ← operation context ⟨address, 0, 2⟩ opcode [2, 3] debug; pure (some id)) (pure none))) := by
    rcases allowed with rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [shape]
  cases called : operation context ⟨address, 0, 2⟩ opcode [2, 3] debug before with
  | mk result after => cases result <;> simp only [output, List.length_cons, List.length_nil, Nat.reduceAdd, Dispatch.orNext, bind, Effect.bind, pure, Effect.pure, called, Except.map]

theorem arithmetic_sites (context : PairInput.Context σ) (address : Nat) (debug : AssemblyItem.Fields.Values)
    (before : World σ) (xor : Bool) :
    trace context address [⟨none, some (if xor then 24 else 3), [1, 2]⟩, {}, {}] 21 [0] debug before =
      output context address 20 [1, 2] debug before := by
  cases xor
  all_goals
    change (Dispatch.orNext (pure none) (Dispatch.orNext (pure none) (Dispatch.orNext
      (do let id ← operation context ⟨address, 0, 2⟩ 20 [1, 2] debug; pure (some id)) (pure none)))) before = _
    cases called : operation context ⟨address, 0, 2⟩ 20 [1, 2] debug before with
    | mk result after => cases result <;> simp only [output, List.length_cons, List.length_nil, Nat.reduceAdd, Dispatch.orNext, bind, Effect.bind, pure, Effect.pure, called, Except.map]

theorem shift_mask_site (context : PairInput.Context σ) (address : Nat) (debug : AssemblyItem.Fields.Values) (before : World σ) :
    (ShiftMasks.removeCoveredShiftMask
      (addressed address [⟨some 1, none, []⟩, ⟨none, some 28, [2, 3]⟩, ⟨some 255, none, []⟩, {}])
      (constructors context) 0 1 debug) before =
      output context address 28 [2, 3] debug before := by
  change (do let id ← operation context ⟨address, 0, 2⟩ 28 [2, 3] debug; pure (some id) : GraphAction σ (Option NodeId)) before = _
  cases called : operation context ⟨address, 0, 2⟩ 28 [2, 3] debug before with
  | mk result after => cases result <;> simp only [output, List.length_cons, List.length_nil, Nat.reduceAdd, bind, Effect.bind, pure, Effect.pure, called, Except.map]

private def localBefore := Semantic.Tests.caller
private def localAfter (first overwrite : Bool) :=
  (LocalArguments.zigLocal LocalArguments.Tests.source (if first then 0 else 1) 99 overwrite localBefore).2

theorem local_observed (first overwrite : Bool) :
    LocalArguments.zigLocal LocalArguments.Tests.source (if first then 0 else 1) 99 overwrite localBefore =
      (.ok LocalArguments.Tests.target, localAfter first overwrite) := by
  cases first <;> cases overwrite <;> rfl'

theorem local_constructor (context : PairInput.Context Nat) (first overwrite : Bool) (opcode : Opcode)
    (debug : AssemblyItem.Fields.Values) :
    Arguments.Prepared (if overwrite then [1, 2].set (if first then 0 else 1) 99 else [1, 2])
      localBefore LocalArguments.Tests.target (localAfter first overwrite) ∧
    localOperation context opcode LocalArguments.Tests.source 1 2 99 (if first then 0 else 1) overwrite debug localBefore =
      TemporaryArguments.unwind localBefore.memory.memory.nextId
        (ConstructorItem.operation context.external context.budget context.allocator (context.primitives LocalArguments.Tests.target)
          context.queries LocalArguments.Tests.target opcode
            (if overwrite then [1, 2].set (if first then 0 else 1) 99 else [1, 2]) debug (localAfter first overwrite)) := by
  have good : Good LocalArguments.Tests.source [1, 2] localBefore :=
    ⟨Normalization.Tests.original_valid, LocalArguments.Tests.source_represented⟩
  exact ⟨local_input _ _ _ _ _ _ _ _ _ good (by cases first <;> decide) (local_observed first overwrite),
    local_prepared _ _ _ _ _ _ _ _ _ _ _ _ (local_observed first overwrite)⟩

theorem local_failure (context : PairInput.Context Nat) (debug : AssemblyItem.Fields.Values) :
    localOperation context 20 ⟨0, 2, 2⟩ 2 0 99 0 true debug localBefore =
      (.error (.memory (.preparation (.memory .memoryValidity))), LocalArguments.Tests.secondLoadRejected.2) :=
  local_rejected _ _ _ _ _ _ _ _ _ _ _ _ (Prod.ext LocalArguments.Tests.rejected_second_load_keeps_allocation.1 rfl)

open RecursiveNonemptyTests

/-- The caller-created unary view belongs to the parent. The full child keeps
it alive through nonempty growth OOM; only the enclosing literal return retires
it. Native graph and parent-borrow preservation come from that same execution. -/
theorem actual_view_child (safety : Bool) : ∃ after,
    operation (childContext safety) childSource 21 [0] debug (child safety).before =
      (.error (.language .outOfMemory), (child safety).returnedWorld (failedWorld safety after)) ∧
    Good childSource [0] ((child safety).returnedWorld (failedWorld safety after)) ∧
    Held 7 rootSource [0, 4] (parent safety).normalized ((child safety).returnedWorld (failedWorld safety after)) ∧
    GraphFacts safety ReachablePrefixTests.backing 5 ((child safety).returnedWorld (failedWorld safety after)) (rows safety) ∧
    ((child safety).returnedWorld (failedWorld safety after)).graph = (child safety).before.graph ∧
    TemporaryArguments.unwind (parent safety).taken.2.world.memory.memory.nextId (childInner safety) =
      (.error (.language .outOfMemory), childReturned safety after) := by
  obtain ⟨after, ran, valid, _, _, keys, native, registry, _⟩ := child_allocation safety
  have established := child_established safety
  have literal := (child_literal safety).1
  have prior := (child_literal safety).2
  have frame := (child safety).returned_frame (failedWorld safety after) literal.good.1 (fun id cell found =>
    native id cell (established.item.memory id cell found))
  have reached := (child safety).returned_valid (failedWorld safety after) valid
  have registered : ∀ id block, (child safety).before.memory.heap id = some block →
      ((child safety).returnedWorld (failedWorld safety after)).memory.heap id = some block := by
    intro id block found
    apply registry id block
    rw [established.item.heap]; exact found
  have graph : ((child safety).returnedWorld (failedWorld safety after)).graph = (child safety).before.graph :=
    established.entry.origin.graph.trans established.item.graph
  have keyFrame := keys.trans (congrArg Publication.Effects.keys established.item.effects)
  have facts := prior.frame (by rw [rows_count]; decide) reached
    ((congrArg Interner.Heap.representatives graph).trans prior.projected) (congrArg Interner.Heap.table graph)
    keyFrame frame registered
  have called := (child_result safety after ran).1
  refine ⟨after, ?_, good_frame _ _ _ _ literal.good reached frame,
    held_after_child safety _ reached (fun id cell found => frame id cell (literal.frame id cell found))
      (fun id block found => registered id block (by change (childArguments safety).2.memory.heap id = _; rw [literal.heap]; exact found)), facts, graph, ?_⟩
  · rw [forwards]
    exact congrArg (fun result => (result.1, result.2.world)) called
  · rw [called]; rfl

/-- Reuse the existing complete EQ child whose source is the buffer produced
by full XOR publication. There is no separate selected-prefix graph child. -/
theorem graph_child_route (safety : Bool) :
    operation (RecursiveBorrowedTests.childContext safety) RecursiveBorrowedTests.childSource 20 [0, 1] debug
      (RecursiveBorrowedTests.child safety).before = RecursiveBorrowedTests.childFull safety := rfl

/-- The actual XOR query supplies the graph-owned source. Its full EQ child
preserves that buffer and its live ISZERO parent through nonempty growth OOM. -/
theorem actual_graph_child (safety : Bool) : ∃ after,
    Operation.run (RecursiveBorrowedTests.child safety).before.memory.memory (Owner.headerAddress ⟨6, 0⟩) 4 24 =
      .ok (.ok (some (Operation.returned RecursiveBorrowedTests.xorOperands))) ∧
    Good RecursiveBorrowedTests.childSource [0, 1] (RecursiveBorrowedTests.child safety).before ∧
    operation (RecursiveBorrowedTests.childContext safety) RecursiveBorrowedTests.childSource 20 [0, 1] debug
      (RecursiveBorrowedTests.child safety).before =
        (.error (.language .outOfMemory), RecursiveBorrowedTests.childReturned safety after) ∧
    Good RecursiveBorrowedTests.childSource [0, 1] (RecursiveBorrowedTests.childReturned safety after) ∧
    Held 7 RecursiveBorrowedTests.rootSource [4] (RecursiveBorrowedTests.parent safety).normalized
      (RecursiveBorrowedTests.childReturned safety after) ∧
    GraphFacts safety ReachablePrefixTests.backing 5 (RecursiveBorrowedTests.childReturned safety after) (RecursiveBorrowedTests.rows safety) ∧
    ∀ id, (RecursiveBorrowedTests.childReturned safety after).graph.read id =
      (RecursiveBorrowedTests.child safety).before.graph.read id := by
  obtain ⟨after, called, facts, graph, _, native, registry, _, good⟩ := RecursiveBorrowedTests.child_contract safety
  exact ⟨after, (RecursiveBorrowedTests.xor_query safety).2, (RecursiveBorrowedTests.child_input safety).2.1,
    (graph_child_route safety).trans called, good,
    RecursiveBorrowedTests.held_after_child safety _ facts.valid native registry,
    facts, fun id => congrArg (fun heap => heap.read id) graph⟩

/-- Full XOR publication establishes the native query witness and separation
needed for the next borrowed constructor. Its original operand buffer is live. -/
theorem publication_input (safety : Bool) : ∃ slice,
    Operation.returned RecursiveBorrowedTests.xorOperands = Operation.returned slice ∧
    BorrowedQuery.observe 7 4 24 (RecursiveBorrowedTests.ready safety) = .ok (some slice) ∧
    Good (view slice) slice.items (RecursiveBorrowedTests.ready safety) ∧
    ∀ key old, (RecursiveBorrowedTests.ready safety).memory.effects.keys key = some old → key.arguments ≠ [] →
      (view slice).length ≠ 0 → (view slice).allocation ≠ old.address := by
  have facts := (RecursiveBorrowedTests.xor_contract safety).2.1
  have input := RecursiveBorrowedTests.xor_input_at safety _ facts
  exact ⟨RecursiveBorrowedTests.xorOperands, rfl, input.1, LiteralInput.Tests.published_borrow safety,
    fun key old found nonempty _ => input.2.2 key old found nonempty⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ViewInput.Tests
