/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RuleLiteralInputProgram
import Compiler.Extraction.InternerPairInputTests
import Compiler.Extraction.InternerRecursiveBorrowedInputTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.LiteralInput.Tests
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops cells lifetime GraphFacts)
open RecursiveTests (debug)

attribute [local irreducible] Arguments.operation ConstructorItem.constant
  RecursiveNonemptyTests.ready RecursiveNonemptyTests.rootArguments RecursiveNonemptyTests.childArguments

theorem existing_shift_routes (context : PairInput.Context σ) (power : Nat) (source : View)
    (debug : AssemblyItem.Fields.Values) :
    exponentTwo context source debug = ShiftInput.zigLiteral context .exponentTwo 0 source debug ∧
    multiplyLeft context power source debug = ShiftInput.zigLiteral context .multiplyLeft power source debug ∧
    multiplyRight context power source debug = ShiftInput.zigLiteral context .multiplyRight power source debug ∧
    divide context power source debug = ShiftInput.zigLiteral context .divide power source debug := ⟨rfl, rfl, rfl, rfl⟩

/-- The child returns before the second element is loaded. Its native frame,
not final Good, establishes that load from the same possibly offset view. -/
theorem minimum_after_child (context : PairInput.Context σ) (source : View)
    (outerByte innerByte : Word) (a b id : NodeId) (debug : AssemblyItem.Fields.Values)
    (before after : World σ) (good : Good source [a, b] before)
    (called : (PairInput.constructors context).constant
      (if outerByte.toNat ≤ innerByte.toNat then outerByte else innerByte) debug before = (.ok id, after))
    (valid : Valid after.memory)
    (native : ∀ allocation cell, before.memory.memory.heap.lookup allocation = some cell →
      after.memory.memory.heap.lookup allocation = some cell) :
    minimumSignextend context outerByte innerByte source debug before =
      Arguments.operation context.external context.budget context.allocator context.primitives context.queries
        Dispatch.opSIGNEXTEND [id, b] debug after := by
  exact (Effect.bind_success _ _ _ _ _ called).trans
    (Effect.bind_success _ _ _ _ _ (ShiftInput.operand_after_frame source [a, b] before after good valid native 1 (by simp)))

/-- materializeConstant discards its ID only after the indexed argument has
been read. Both literal positions preserve the original ordering. -/
theorem materialize_after_read (context : PairInput.Context σ) (source : View) (a b scalar id : NodeId)
    (value : Word) (debug : AssemblyItem.Fields.Values) (before after : World σ)
    (good : Good source [a, b] before)
    (called : (PairInput.constructors context).constant value debug before = (.ok id, after)) :
    subtractMaterializedRight context scalar source value debug before =
      Arguments.operation context.external context.budget context.allocator context.primitives context.queries
        Dispatch.opSUB [scalar, id] debug after ∧
    subtractMaterializedLeft context source value scalar debug before =
      Arguments.operation context.external context.budget context.allocator context.primitives context.queries
        Dispatch.opSUB [id, scalar] debug after := by
  constructor
  · exact (Effect.bind_success _ _ _ _ _ (ShiftInput.operand_good source [a, b] before good 1 (by simp))).trans
      (Effect.bind_success _ _ _ _ _ called)
  · exact (Effect.bind_success _ _ _ _ _ (ShiftInput.operand_good source [a, b] before good 0 (by simp))).trans
      (Effect.bind_success _ _ _ _ _ called)

theorem modular_reads (context : PairInput.Context σ) (add : Bool) (source : View) (a b right : NodeId)
    (debug : AssemblyItem.Fields.Values) (before : World σ) (good : Good source [a, b] before) :
    (if add then modularAdd context source right debug else modularMultiply context source right debug) before =
      Arguments.operation context.external context.budget context.allocator context.primitives context.queries
        (if add then Dispatch.opADDMOD else Dispatch.opMULMOD) [a, b, right] debug before := by
  cases add <;> exact
    (Effect.bind_success _ _ _ _ _ (ShiftInput.operand_good source [a, b] before good 0 (by simp))).trans
      (Effect.bind_success _ _ _ _ _ (ShiftInput.operand_good source [a, b] before good 1 (by simp)))

theorem alternating_reads (context : PairInput.Context σ) (source : View) (a b scalar : NodeId)
    (debug : AssemblyItem.Fields.Values) (before : World σ) (good : Good source [a, b] before) (right : Bool) :
    alternatingRight context source (if right then 1 else 0) scalar debug before =
      Arguments.operation context.external context.budget context.allocator context.primitives context.queries
        Dispatch.opAND [if right then a else b, scalar] debug before := by
  cases right
  · exact Effect.bind_success _ _ _ _ _ (ShiftInput.operand_good source [a, b] before good 1 (by simp))
  · exact Effect.bind_success _ _ _ _ _ (ShiftInput.operand_good source [a, b] before good 0 (by simp))

theorem early_rejections (context : PairInput.Context σ) (before : World σ) (debug : AssemblyItem.Fields.Values)
    (allocation offset : Nat) (value : Word) :
    subtractMaterializedLeft context ⟨allocation, offset, 0⟩ value 0 debug before =
      (.error (.memory (.preparation (.memory .sourceBounds))), before) ∧
    subtractMaterializedRight context 0 ⟨allocation, offset, 0⟩ value debug before =
      (.error (.memory (.preparation (.memory .sourceBounds))), before) ∧
    alternatingRight context ⟨allocation, offset, 2⟩ 2 0 debug before =
      (.error (.language .safetyFault), before) := ⟨rfl, rfl, rfl⟩

/-- Real growth OOM skips even an invalid later view. A materialization site
first reads the live parent buffer, then runs the same complete child. -/
theorem actual_constant_failure (safety materialized : Bool) (later : View) : ∃ after,
    (if materialized then subtractMaterializedRight (ShiftInput.Tests.context safety) 0 RecursiveTests.rootSource 1 debug
      else minimumSignextend (ShiftInput.Tests.context safety) 1 1 later debug) (RecursiveTests.child safety).before =
        (.error (.language .outOfMemory), RecursiveTests.childReturned safety after) ∧
    Held 7 RecursiveTests.rootSource [0, 0] (RecursiveTests.parent safety).normalized (RecursiveTests.childReturned safety after) ∧
    GraphFacts safety ReachablePrefixTests.backing 5 (RecursiveTests.childReturned safety after) (RecursiveNonemptyTests.rows safety) := by
  obtain ⟨after, called, facts, _, native, registry⟩ := RecursiveTests.child_contract safety
  have child : (PairInput.constructors (ShiftInput.Tests.context safety)).constant 1 debug
      (RecursiveTests.child safety).before = (.error (.language .outOfMemory), RecursiveTests.childReturned safety after) := by
    rw [PairInput.constant_forwarded, ShiftInput.Tests.child_forwarded, called]
  refine ⟨after, ?_, RecursiveTests.held_after_child safety _ facts.valid native registry, facts⟩
  cases materialized
  · exact Effect.bind_failure _ _ _ _ _ child
  · have good : Good RecursiveTests.rootSource [0, 0] (RecursiveTests.child safety).before :=
      (RecursiveTests.parent_established safety).entry.origin.held.1
    exact (Effect.bind_success _ _ _ _ _ (ShiftInput.operand_good _ _ _ good 1 (by simp))).trans
      (Effect.bind_failure _ _ _ _ _ child)

open RecursiveNonemptyTests

/-- The indexed unary literal prepares the same actual nonempty child as the
composed fixture. Child failure returns through both local frames and retires
the child literal; the parent's later native read is derived from that frame. -/
theorem actual_nonempty_child (safety : Bool) : ∃ after,
    tripleIszero (childContext safety) ⟨rootSource.allocation, 0, 1⟩ debug (parent safety).taken.2.world =
      (.error (.language .outOfMemory), childReturned safety after) ∧
    GraphFacts safety ReachablePrefixTests.backing 5 (childReturned safety after) (rows safety) ∧
    Held 7 rootSource [0, 4] (parent safety).normalized (childReturned safety after) ∧
    ShiftInput.operand rootSource 1 (childReturned safety after) = (.ok 4, childReturned safety after) ∧
    (childReturned safety after).memory.memory.heap.lookup childSource.allocation = none := by
  have good : Good rootSource [0, 4] (parent safety).taken.2.world := (parent_established safety).entry.origin.held.1
  have loaded : ShiftInput.operand ⟨rootSource.allocation, 0, 1⟩ 0 (parent safety).taken.2.world =
      (.ok 0, (parent safety).taken.2.world) :=
    ShiftInput.operand_loaded _ _ _ _ (by decide) (good.2.2 0 (by decide))
  obtain ⟨after, called, facts, _, _, native, registry, _, dead⟩ := child_contract safety
  refine ⟨after, ?_, facts, held_after_child safety _ facts.valid native registry, ?_, dead⟩
  · exact (Effect.bind_success _ _ _ _ _ loaded).trans called
  · exact ShiftInput.operand_after_frame rootSource [0, 4] _ _ good facts.valid native 1 (by decide)

/-- Full XOR publication supplies a nonempty graph operand buffer. The four
initial environment rows have no operands and cannot supply this borrow. -/
theorem published_borrow (safety : Bool) :
    Good RecursiveBorrowedTests.childSource [0, 1] (RecursiveBorrowedTests.ready safety) :=
  (RecursiveBorrowedTests.xor_input_at safety _ (RecursiveBorrowedTests.xor_contract safety).2.1).2.1

/-- Initialization supplies the caller's original array. First allocation,
spare publications and both constructor returns preserve its native cell;
the post-constant indexed read consumes that derived frame. -/
theorem published_source (safety : Bool) :
    Good (CallerInputTests.argumentView false) [0] (ready safety) := by
  exact RecursiveNonemptyTests.caller_source safety

/-- Actual zero publication precedes the native indexed load and next literal.
The complete outer SHL outcome and enclosing branch guards remain open. -/
theorem actual_publication_read (safety : Bool) :
    Arguments.Prepared [4, 0] (ready safety) rootSource (AlgebraicInput.Tests.afterPublication safety false).2 ∧
    multiplyRight (AlgebraicInput.Tests.publishing safety) 0 (CallerInputTests.argumentView false) debug (initial safety) =
      Arguments.returned [4, 0] (ready safety).memory.memory.nextId
        (ConstructorItem.operation (Publication.external ops.arguments) 160 7
          ((AlgebraicInput.Tests.publishing safety).primitives rootSource) Interner.Queries.queries
          rootSource Dispatch.opSHL [4, 0] debug (AlgebraicInput.Tests.afterPublication safety false).2) := by
  have child := AlgebraicInput.Tests.published_child safety
  have loaded := ShiftInput.operand_good _ [0] _ (published_source safety) 0 (by decide)
  have literal := AlgebraicInput.Tests.publication_literal safety false
  have prepared := Arguments.prepare_success [4, 0] (ready safety)
    (AlgebraicInput.Tests.afterPublication safety false).2 rootSource child.2.valid literal
  refine ⟨(by with_reducible exact prepared), ?_⟩
  have next := Arguments.operation_prepared (Publication.external ops.arguments) 160 7
    (AlgebraicInput.Tests.publishing safety).primitives Interner.Queries.queries Dispatch.opSHL [4, 0] debug
    (ready safety) _ rootSource literal
  exact (Effect.bind_success _ _ _ _ _ child.1).trans
    ((Effect.bind_success _ _ _ _ _ loaded).trans next)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.LiteralInput.Tests
