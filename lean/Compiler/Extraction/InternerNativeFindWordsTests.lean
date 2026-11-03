/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeFindProduction
import Compiler.Extraction.InternerNativeForceProductionTests
import Compiler.Extraction.InternerConstantNegationInputTests
import Compiler.Extraction.InternerAllocationRecursiveReplayTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.FindWordsTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open RecursiveTests (Call debug)
open CallerGrowingChainTests (ops growth)

/-- Select the existing ISZERO and SUB inputs; both use the same caller proof. -/
def call (safety negate : Bool) (value : Word) : Call :=
  if negate then ConstantNegationTests.parent safety value else ConstantFoldTests.parent safety value

def base : PairInput.Context (Publication.Effects Nat) := ForceTests.base none
def env : AddressMask.Environment := ⟨⟨0, 0⟩, 0, 0⟩
def other : Meaning := { Insertion.Tests.base with operation := fun _ _ _ => some 0 }
def meaning := Dispatch.wordDispatchMeaning env (Interner.constructorMeaning other)
def allocate (permitted : Bool) := if permitted then ReachablePrefixTests.allocate else RecursiveNonemptyTests.failing
def nativeBase (safety permitted : Bool) := callerContext ops (allocate permitted) safety 6 meaning base (some growth)
def action (safety negate : Bool) (value : Word) (depth : Nat) (permitted : Bool := false) :=
  let input := call safety negate value
  let actual := (context (nativeBase safety permitted) 6 64 (unfold (nativeBase safety permitted) 6 64 depth) debug).primitives
    input.source input.address input.native
  Caller.findBody (Publication.external ops.arguments) 160 7 actual Interner.Queries.queries
    input.source ⟨input.constructed.memory.memory.nextId, 0, 2⟩ input.request

def initial (safety negate : Bool) (value : Word) :=
  let input := call safety negate value
  {input.constructed with memory := {input.constructed.memory with memory := input.stack}}
def ran (safety negate : Bool) (value : Word) (depth : Nat) (permitted : Bool := false) :=
  Caller.invoke (Publication.external ops.arguments) 7 (action safety negate value depth permitted) (initial safety negate value)

attribute [local irreducible] ConstantPublicationTests.ready ConstantFoldTests.rootArguments
  ConstantNegationTests.rootArguments Call.constructed Call.stack

/-- The original fixture producers discharge native input, source privacy,
layout and scratch admission. Initial semantic validity and the request value
remain explicit, as in the general native theorem. No child result is supplied. -/
theorem prepared_verified (safety negate : Bool) (value : Word) (depth : Nat)
    (valid : Interner.Invariant meaning (call safety negate value).constructed.graph) (expected : Word)
    (evaluated : (call safety negate value).request.item.eval meaning
      (call safety negate value).constructed.graph.read (call safety negate value).request.arguments
      (call safety negate value).request.sequence = some expected) (permitted : Bool := false) :
    Semantic.Verified (Publication.external ops.arguments) 7 (call safety negate value).source
      (call safety negate value).request.arguments meaning (action safety negate value depth permitted)
      (initial safety negate value) (fun id after => after.read id = some expected) := by
  let input := call safety negate value
  have literal : Arguments.Prepared input.request.arguments (WordConstantTests.ready safety value) input.source input.before := by
    cases negate
    · exact (ConstantFoldTests.literal safety value).2.1
    · exact (ConstantNegationTests.literal safety value).2.1
  have established : input.Established safety ReachablePrefixTests.backing 5 (ConstantPublicationTests.rows safety value) := by
    cases negate
    · exact ConstantFoldTests.established safety value
    · exact ConstantNegationTests.established safety value
  have allocated : Compiler.ZigAir.Memory.allocate input.constructed.memory.memory (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨input.before.memory.memory.nextId + 1, 0⟩, input.stack) := by
    cases negate
    · exact (ConstantFoldTests.prepared safety value).2.2.1
    · exact (ConstantNegationTests.prepared safety value).2.2.1
  have prior := (ConstantPublicationTests.contract safety value RecursiveNonemptyTests.failing (some growth)).2.1
  have privateSource : Caller.SourcePrivate input.source input.constructed.memory.effects.keys := by
    rw [congrArg Publication.Effects.keys established.item.effects, congrArg Publication.Effects.keys literal.effects]
    exact fun key => literal.key_apart input.request.arguments _ _ _ prior.valid 7 key prior.live
  exact production_find_verified ops (allocate permitted) safety 6 64 env
    (Interner.constructorMeaning other) base (some growth) debug AllocationRecursiveReplayTests.seed
    (.base .missingArguments) (Normalization.Tests.external_admitted _) AssemblyItem.Initializers.Tests.debug_valid
    (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (Associative.constructor_meaning_pushes _) (Insertion.Native.constructor_push_values _)
    depth (ConstantPublicationTests.rows safety value) (fun _ => True) .root input.source input.request input.constructed
    trivial _ 5 (established.constructed.native (by rw [ConstantPublicationTests.rows_count]; decide))
    (good_frame input.before input.constructed input.source input.request.arguments literal.good
      established.item.valid established.item.memory).2 privateSource
    (literal.arraySource.frame (fun _ cell found => established.item.memory _ cell found))
    input.address input.native established.item.represented rfl
    (by cases negate <;> change (1 : Int) ∈ AssemblyItem.itemTagValues <;> decide)
    input.stack _ allocated valid expected evaluated

/-- The existing word-only attachment specializes the complete caller contract. -/
theorem prepared_words (safety negate : Bool) (value : Word) (depth : Nat)
    (valid : Interner.Invariant meaning (call safety negate value).constructed.graph) (expected : Word)
    (evaluated : (call safety negate value).request.item.eval meaning
      (call safety negate value).constructed.graph.read (call safety negate value).request.arguments
      (call safety negate value).request.sequence = some expected) (permitted : Bool := false) :
    Semantic.Ensures meaning (call safety negate value).constructed.graph (ran safety negate value depth permitted).1
      (ran safety negate value depth permitted).2.world.graph (fun id after => after.read id = some expected) :=
  (prepared_verified safety negate value depth valid expected evaluated permitted).2

private def operationKey (opcode : Opcode) : Key := ⟨1, opcode, 0, [], 0⟩
private def literalKey : Key := ⟨2, 0, 1, [], 0⟩
private def table : Table :=
  Cache.put equalityFields
    (Cache.put equalityFields
      (Cache.put equalityFields
        (Cache.put equalityFields
          (Cache.put equalityFields (fun _ => none) (operationKey 48) 0) (operationKey 50) 1)
        (operationKey 51) 2) (operationKey 52) 3) literalKey 4
private def observation (cell : Storage.Cell) := (cell.item, cell.arguments, cell.sequence, cell.value)

/-- The existing fixture graph assigns zero to ADDRESS/ORIGIN/CALLER/CALLVALUE.
The interpretation above gives these same denotations; they are not compiler
claims that these environment operations always evaluate to zero. -/
private theorem initial_snapshot (safety : Bool) :
    let initial := WordConstantTests.ready safety 1
    (initial.graph.read 0, initial.graph.read 1, initial.graph.read 2, initial.graph.read 3, initial.graph.read 4) =
      (some 0, some 0, some 0, some 0, some 1) ∧
    initial.graph.table = table ∧
    (ConstantPublicationTests.rows safety 1).map observation =
      [(⟨1, some 48, 0⟩, [], 0, 0), (⟨1, some 50, 0⟩, [], 0, 0),
       (⟨1, some 51, 0⟩, [], 0, 0), (⟨1, some 52, 0⟩, [], 0, 0), (⟨2, none, 1⟩, [], 0, 1)] := by
  cases safety <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

private theorem initial_valid (safety : Bool) :
    Interner.Invariant meaning (WordConstantTests.ready safety 1).graph := by
  obtain ⟨reads, tableEq, cells⟩ := initial_snapshot safety
  simp only [Prod.mk.injEq] at reads
  obtain ⟨r0, r1, r2, r3, r4⟩ := reads
  let read := (WordConstantTests.ready safety 1).graph.read
  have empty : Cache.Valid meaning read (fun _ => none) := by intro _ _ impossible; cases impossible
  have first := Cache.put_valid meaning read _ empty (operationKey 48) 0 0 rfl r0
  have second := Cache.put_valid meaning read _ first (operationKey 50) 1 0 rfl r1
  have third := Cache.put_valid meaning read _ second (operationKey 51) 2 0 rfl r2
  have fourth := Cache.put_valid meaning read _ third (operationKey 52) 3 0 rfl r3
  have fifth := Cache.put_valid meaning read _ fourth literalKey 4 1 rfl r4
  have prior := ConstantPublicationTests.contract safety 1 RecursiveNonemptyTests.failing (some growth)
  have projected : (WordConstantTests.ready safety 1).graph.representatives = some (ConstantPublicationTests.rows safety 1) :=
    prior.2.1.projected
  refine ⟨?_, ?_⟩
  · rw [tableEq]; exact fifth
  · simp only [Interner.Represented, projected]
    refine ⟨prior.2.2.2.1, ?_⟩
    intro cell member
    have found : observation cell ∈ (ConstantPublicationTests.rows safety 1).map observation :=
      List.mem_map.mpr ⟨cell, member, rfl⟩
    rw [cells] at found
    simp only [observation, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at found
    rcases found with h | h | h | h | h <;>
      rcases h with ⟨item, arguments, sequence, value⟩ <;>
      rw [item, arguments, sequence, value] <;> rfl

private theorem initial_graph (safety negate : Bool) :
    (call safety negate 1).constructed.graph = (WordConstantTests.ready safety 1).graph := by
  cases negate
  · exact (ConstantFoldTests.prepared safety 1).2.1.graph.trans (ConstantFoldTests.literal safety 1).2.1.graph
  · exact (ConstantNegationTests.prepared safety 1).2.1.graph.trans (ConstantNegationTests.literal safety 1).2.1.graph

/-- Both existing requests have witnessed semantic admission. In particular,
neither initial validity nor request evaluation is a premise of this attachment. -/
theorem certified_verified (safety negate permitted : Bool) (depth : Nat) :
    Semantic.Verified (Publication.external ops.arguments) 7 (call safety negate 1).source
      (call safety negate 1).request.arguments meaning (action safety negate 1 depth permitted)
      (initial safety negate 1) (fun id after => after.read id = some (if negate then (0 : Word) - 1 else 0)) := by
  have graph := initial_graph safety negate
  have valid : Interner.Invariant meaning (call safety negate 1).constructed.graph := by
    rw [graph]; exact initial_valid safety
  apply prepared_verified safety negate 1 depth valid _ ?_ permitted
  rw [graph]
  have reads := (initial_snapshot safety).1
  simp only [Prod.mk.injEq] at reads
  obtain ⟨r0, _, _, _, r4⟩ := reads
  cases negate
  · change (⟨1, some 21, 0⟩ : Item).eval meaning (WordConstantTests.ready safety 1).graph.read [4] 0 = some 0
    simp only [Cache.Item.eval, Cache.readArguments, r4] <;> rfl
  · change (⟨1, some 3, 0⟩ : Item).eval meaning (WordConstantTests.ready safety 1).graph.read [0, 4] 0 = some ((0 : Word) - 1)
    simp only [Cache.Item.eval, Cache.readArguments, r0, r4] <;> rfl

/-- The original fixture statement remains a projection of the same execution. -/
theorem certified_words (safety negate permitted : Bool) (depth : Nat) :
    Semantic.Ensures meaning (call safety negate 1).constructed.graph (ran safety negate 1 depth permitted).1
      (ran safety negate 1 depth permitted).2.world.graph
      (fun id after => after.read id = some (if negate then (0 : Word) - 1 else 0)) :=
  (certified_verified safety negate permitted depth).2

attribute [local irreducible] ran

/-- Both existing requests execute the native recursive child and return its
growth failure through the actual cleanup, in both native safety layouts. -/
theorem ordinary_failure (safety negate : Bool) :
    ((ran safety negate 1 1).1, (ran safety negate 1 1).2.scope) =
      (.error (.language .outOfMemory), ⟨none, none, false⟩) := by
  cases safety <;> cases negate <;> insertion_kernel_rfl

/-- A permitted growth produces the checked ISZERO word. The closed caller
scope retains the normalized owner transferred to publication. This is the
same native invocation covered by certified_words. -/
theorem successful_word (safety : Bool) :
    ((ran safety false 1 1 true).1, (ran safety false 1 1 true).2.world.graph.read 5,
      (ran safety false 1 1 true).2.scope) =
      (.ok 5, some 0, ⟨none, some (call safety false 1).normalized, true⟩) := by
  cases safety <;> insertion_kernel_rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.FindWordsTests
