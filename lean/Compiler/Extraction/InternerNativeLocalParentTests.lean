/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeLocalCacheTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeLocal.Tests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops lifetime)
open RecursiveTests (Call debug)
open RecursiveBorrowedTests (childContext)

attribute [local irreducible] BinaryPreludeTests.ready rootArguments copied localReturned

set_option maxRecDepth 8192 in
theorem dispatch_route (reads : Nested.Reads) (constructors : NativeRecursion.Constructors (Publication.Effects Nat))
    (before : World (Publication.Effects Nat))
    (c0 : reads.constant 0 = .ok none) (c4 : reads.constant 4 = .ok none)
    (o0 : reads.operation 0 23 = .ok none) (o4 : reads.operation 4 23 = .ok none)
    (n0 : reads.operation 0 25 = .ok none) (n4 : reads.operation 4 25 = .ok none)
    (a0 : reads.operation 0 22 = .ok none) (a4 : reads.operation 4 22 = .ok (some BinaryPreludeTests.operands))
    (e : reads.overrideEquality = none) (result : Except Fault NodeId) (after : World (Publication.Effects Nat))
    (called : constructors.localOperation 22 BinaryPreludeTests.operands 0 0 true debug before = (result, after))
    (input : Nested.OperandRead (GraphAction (Publication.Effects Nat)) := Nested.logicalOperand)
    (address : Nat := 0) :
    (Dispatch.simplifyWithInputs reads constructors 64 22 [0, 4] debug input address) before =
      (result.map some, after) := by
  have collected : Dispatch.collectConstants reads [0, 4] = .ok none := by
    unfold Dispatch.collectConstants; rw [c0]; rfl
  have first : (Dispatch.constantStage reads constructors 22 [0, 4] debug) before = (.ok none, before) := by
    simp only [Dispatch.constantStage, collected]; rfl
  have noConstants : zigSelect 22 .constants {} = none := by insertion_kernel_rfl
  have pureStep {α β : Type} (value : α) (next : α → GraphAction (Publication.Effects Nat) β) :
      Effect.bind (Effect.pure value) next = next value := rfl
  have binary : (Dispatch.binaryStageWithInputs reads constructors 64 22 0 4 debug Dispatch.defaultOptions input) before =
      (result.map some, after) := by
    unfold Dispatch.binaryStageWithInputs
    simp only [c0, c4, Nested.readAction]
    dsimp only [Bind.bind, Pure.pure, Effect.bind, Effect.pure]
    simp only [Dispatch.opSDIV, Dispatch.opAND, Dispatch.opBYTE,
      Dispatch.opXOR, Dispatch.opOR, Nested.sameExpression, e, Nested.absorbedOccurrence,
      Nested.isNegation, Nested.nestedNotOpcode, Nested.dropRepeatedLocal, Nested.repeatedIndex,
      noConstants, pureStep, BinaryPreludeTests.operands, o0, o4, n0, n4, a0, a4,
      Bind.bind, Pure.pure, Effect.bind, Effect.pure, Except.bind, Except.pure,
      BitVec.reduceBEq, Bool.false_eq_true, ↓reduceIte]
    simp only [BinaryPreludeTests.operands, BitVec.ofNat_eq_ofNat] at called
    cases result <;> simp [Effect.bind, called, Effect.pure, Except.map]
  unfold Dispatch.simplifyWithInputs Dispatch.simplifyOptionsWithInputs
  simp only [Dispatch.orNext, bind, Effect.bind, first, binary]
  cases result <;> rfl

def parentReads (safety : Bool) := Interner.representativeReads (parent safety).taken.2.world.graph

theorem constant_guards (safety : Bool) (id : NodeId) (selected : id = 0 ∨ id = 4) :
    (parentReads safety).constant id = .ok none ∧
    Constant.value (parent safety).taken.2.world.memory.memory (Owner.headerAddress ⟨6, 0⟩) id = .ok (.ok none) := by
  have inside : id.toNat < (BinaryPreludeTests.rows safety false).length := by
    rcases selected with rfl | rfl <;> rw [BinaryPreludeTests.rows_count] <;> decide
  have kinds : (BinaryPreludeTests.rows safety false).map (fun row => row.item.kind) = [1, 1, 1, 1, 1] := by
    cases safety <;> insertion_kernel_rfl
  have kind : (BinaryPreludeTests.rows safety false)[id.toNat].item.kind = 1 := by
    have chosen := congrArg (fun values => values[id.toNat]?) kinds
    simp only [List.getElem?_map, List.getElem?_eq_getElem inside, Option.map_some] at chosen
    rcases selected with rfl | rfl <;> exact Option.some.inj chosen
  exact RecursiveBorrowedTests.constant_nonpush safety 5 _ _ (parent_established safety).taken
    (by rw [BinaryPreludeTests.rows_count]; decide) id inside kind

theorem operation_guards (safety : Bool) :
    (parentReads safety).operation 0 23 = .ok none ∧ (parentReads safety).operation 4 23 = .ok none ∧
    (parentReads safety).operation 0 25 = .ok none ∧ (parentReads safety).operation 4 25 = .ok none ∧
    (parentReads safety).operation 0 22 = .ok none := by
  have observed : ((parentReads safety).operation 0 23, (parentReads safety).operation 4 23,
      (parentReads safety).operation 0 25, (parentReads safety).operation 4 25,
      (parentReads safety).operation 0 22) = (.ok none, .ok none, .ok none, .ok none, .ok none) := by
    simp only [parentReads, Interner.representativeReads, (parent_established safety).taken.projected, Nested.storageReads]
    cases safety <;> insertion_kernel_rfl
  simpa only [Prod.mk.injEq] using observed

theorem operation_agreement (safety : Bool) (id : NodeId) (opcode : Opcode) :
    Operation.run (parent safety).taken.2.world.memory.memory (Owner.headerAddress ⟨6, 0⟩) id opcode =
      .ok (((parentReads safety).operation id opcode).map (Option.map Operation.returned)) := by
  have facts := (parent_established safety).taken
  have native := (facts.native (by rw [BinaryPreludeTests.rows_count]; decide)).operations id opcode
  simpa only [parentReads, Interner.representativeReads, facts.projected, Nested.storageReads] using native

def parentPrimitives (safety : Bool) (children : NativeRecursion.Constructors (Publication.Effects Nat)) :=
  (NativeRecursion.context (childContext safety) 6 64 children debug).primitives rootSource

def resumed (safety : Bool) :=
  (do let _ ← graph (fun slice => Publication.publish ops.probe ops.arguments 7 rootSource (parent safety).key slice 4)
      handoff
      pure 4 : Action (Publication.Effects Nat) NodeId)
    ⟨(localReturned safety).2, (parent safety).taken.2.scope⟩

def reduced (safety : Bool) :=
  let done := OwnedCall.finish (Publication.external ops.arguments) 7 (resumed safety).1 (resumed safety).2
  Arguments.returned [0, 4] (BinaryPreludeTests.ready safety false).memory.memory.nextId
    (if ordinary done.1 then (done.1, (parent safety).returned done.2) else done)

def rootWith (safety : Bool) (children : NativeRecursion.Constructors (Publication.Effects Nat)) :=
  (NativeRecursion.step (childContext safety) 6 64 (NativeRecursion.step (childContext safety) 6 64 children)).operation
    22 [0, 4] debug (BinaryPreludeTests.ready safety false)

theorem parent_simplified (safety : Bool) (children : NativeRecursion.Constructors (Publication.Effects Nat)) :
    (parentPrimitives safety (NativeRecursion.step (childContext safety) 6 64 children)
      (parent safety).address (parent safety).native).simplify (parent safety).key (parent safety).normalized
        (parent safety).taken.2.world = (.ok (some 4), (localReturned safety).2) := by
  have forwarded := congrFun (ViewInput.local_forwarded
    (NativeRecursion.context (childContext safety) 6 64 children debug) BinaryPreludeTests.operands 0 1 rfl 22 0 0 true debug)
      (parent safety).taken.2.world
  have returned : localReturned safety = (.ok 4, (localReturned safety).2) := by unfold localReturned; rfl
  have called := forwarded.trans ((local_result safety children).trans returned)
  have guards := operation_guards safety
  have facts := (parent_established safety).taken.native (by rw [BinaryPreludeTests.rows_count]; decide)
  simp only [parentPrimitives, NativeRecursion.dispatcher_snapshot]
  rw [facts.reads]
  exact dispatch_route (input := NativeRecursion.operand) (address := (parent safety).normalized.address) (parentReads safety) (NativeRecursion.step (childContext safety) 6 64 children)
    (parent safety).taken.2.world (constant_guards safety 0 (Or.inl rfl)).1 (constant_guards safety 4 (Or.inr rfl)).1
    guards.1 guards.2.1 guards.2.2.1 guards.2.2.2.1 guards.2.2.2.2 (source_query safety).1
    (by simp only [parentReads, Interner.representativeReads, (parent_established safety).taken.projected, Nested.storageReads])
    (.ok 4) (localReturned safety).2 called

theorem parent_continuation (safety : Bool) (children : NativeRecursion.Constructors (Publication.Effects Nat)) :
    (parent safety).continuation (parentPrimitives safety (NativeRecursion.step (childContext safety) 6 64 children)
      (parent safety).address (parent safety).native) = resumed safety := by
  have scope := (parent_established safety).entry.origin.scope
  simp only [Call.continuation, Interner.FindCode.controlMiss, Caller.execution, OwnedCall.execution,
    show (parent safety).request.item.kind = 1 from rfl, beq_self_eq_true, Bool.and_self, ↓reduceIte,
    graph, scope, parent_simplified, bind, Effect.bind]
  unfold resumed
  simp only [graph, scope, bind, Effect.bind]
  rfl

theorem root_literal (safety : Bool) : Arguments.prepare [0, 4] (BinaryPreludeTests.ready safety false) =
    (.ok rootSource, (parent safety).before) := by
  simpa only [parent, rootArguments] using
    (Prod.ext (parent_observed safety).1 rfl : rootArguments safety = (.ok rootSource, (rootArguments safety).2))

theorem parent_room (safety : Bool) : Interner.Queries.queries.atCapacity (parent safety).constructed.graph = false := by
  rw [Interner.Queries.capacity_exact _ _ (parent_established safety).constructed.projected, BinaryPreludeTests.rows_count]
  decide

/-- The source-selected child returns into the actual parent publication and
both caller returns. The earlier graph and child result are derived above. -/
theorem root_route (safety : Bool) (children : NativeRecursion.Constructors (Publication.Effects Nat)) :
    rootWith safety children = reduced safety := by
  have routed := (parent safety).route (parentPrimitives safety (NativeRecursion.step (childContext safety) 6 64 children))
    (parent_observed safety).2.1 (parent_established safety).item.graph (parent_room safety) rfl
  rw [parent_continuation] at routed
  change Arguments.operation (childContext safety).external (childContext safety).budget (childContext safety).allocator
    (NativeRecursion.context (childContext safety) 6 64 (NativeRecursion.step (childContext safety) 6 64 children) debug).primitives
    (childContext safety).queries 22 [0, 4] debug (BinaryPreludeTests.ready safety false) = _
  rw [Arguments.operation_prepared _ _ _ _ _ _ _ _ _ _ _ (root_literal safety)]
  exact congrArg (Arguments.returned [0, 4] (BinaryPreludeTests.ready safety false).memory.memory.nextId) routed

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeLocal.Tests
