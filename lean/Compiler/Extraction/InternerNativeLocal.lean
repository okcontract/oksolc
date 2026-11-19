/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeGraphFrame
import Compiler.Extraction.InternerNativeRecursion

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeLocal
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- The shared dispatcher helper with the actual recursive constructor family.
The source query/selector is unchanged; the selected continuation owns the
native local copy, optional overwrite, complete constructor and outer cleanup. -/
def run (base : PairInput.Context σ) (owner usizeBits depth : Nat) (opcode : Opcode)
    (nested repeated : NodeId) (first : Bool) (debug : AssemblyItem.Fields.Values) : GraphAction σ (Option NodeId) :=
  fun before => Nested.dropRepeatedLocal (NativeReads.reads owner before.memory.memory)
    (NativeRecursion.unfold base owner usizeBits depth).localOperation opcode nested repeated first debug (NativeReads.query owner) before

theorem snapshot (base : PairInput.Context σ) (owner usizeBits depth : Nat) (opcode : Opcode)
    (nested repeated : NodeId) (first : Bool) (debug : AssemblyItem.Fields.Values) (before : World σ) :
    run base owner usizeBits depth opcode nested repeated first debug before =
      (Nested.dropRepeatedLocal (NativeReads.reads owner before.memory.memory)
        (NativeRecursion.unfold base owner usizeBits depth).localOperation opcode nested repeated first debug) before :=
  (Recursive.QueryTiming.drop_repeated before (NativeReads.reads owner before.memory.memory)
    (NativeReads.query owner) (fun _ => rfl) _ opcode nested repeated first debug).1

theorem selected (base : PairInput.Context σ) (owner usizeBits depth : Nat) (opcode : Opcode)
    (nested repeated left right : NodeId) (first : Bool) (debug : AssemblyItem.Fields.Values)
    (before : World σ) (source : ArgumentSlice) (index : Nat)
    (query : (NativeReads.reads owner before.memory.memory).operation nested opcode = .ok (some source))
    (items : source.items = [left, right])
    (chosen : Nested.repeatedIndex (NativeReads.reads owner before.memory.memory) left right repeated = some index) :
    run base owner usizeBits (depth + 1) opcode nested repeated first debug before =
      (do let id ← ViewInput.localOperation
            (NativeRecursion.context base owner usizeBits (NativeRecursion.unfold base owner usizeBits depth) debug)
            opcode (view source) left right repeated index first debug
          pure (some id)) before := by
  simp only [snapshot, Nested.dropRepeatedLocal, query, Nested.readAction, items, chosen,
    bind, Effect.bind, pure, Effect.pure]
  rw [NativeRecursion.local_succ base owner usizeBits depth source left right items]

/-- The actual native graph supplies the source view. Every successful local
copy derives its input, key separation and retained graph facts before the
complete recursive constructor is entered. Preparation failures retain their
reached world and skip the constructor. Both selector loads and the admitted
scalar-ID comparison are derived too; the recursive postcondition remains open. -/
theorem input_contract (base : PairInput.Context (Publication.Effects σ))
    (usizeBits depth : Nat) (opcode : Opcode) (nested repeated left right : NodeId)
    (first : Bool) (debug : AssemblyItem.Fields.Values) (before : World (Publication.Effects σ))
    (source : ArgumentSlice) (index : Nat) (safety : Bool) (owner capacity : Nat)
    (data : Compiler.ZigAir.Memory.Address) (rows : List Storage.Cell)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (query : (Interner.representativeReads before.graph).operation nested opcode = .ok (some source))
    (items : source.items = [left, right])
    (chosen : Nested.repeatedIndex (Interner.representativeReads before.graph) left right repeated = some index) :
    Operation.run before.memory.memory (Owner.headerAddress ⟨owner, 0⟩) nested opcode =
        .ok (.ok (some (Operation.returned source))) ∧
    Good (view source) source.items before ∧
    ShiftInput.operand (view source) 1 before = (.ok right, before) ∧
    ShiftInput.operand (view source) 0 before = (.ok left, before) ∧
    (if right == repeated then some 1 else if left == repeated then some 0 else none) = some index ∧
    (let args := if first then [left, right].set index repeated else [left, right]
     match LocalArguments.zigLocal (view source) index repeated first before with
     | (.error fault, reached) =>
       run base owner usizeBits (depth + 1) opcode nested repeated first debug before = (.error fault, reached)
     | (.ok target, reached) =>
       Arguments.Prepared args before target reached ∧
       NativeGraph.Facts safety base.allocator owner data capacity reached rows ∧
       (∀ key old, reached.memory.effects.keys key = some old → key.arguments ≠ [] →
         target.length ≠ 0 → target.allocation ≠ old.address) ∧
       run base owner usizeBits (depth + 1) opcode nested repeated first debug before =
         (let called := TemporaryArguments.unwind before.memory.memory.nextId
           (ConstructorItem.operation base.external base.budget base.allocator
             ((NativeRecursion.context base owner usizeBits (NativeRecursion.unfold base owner usizeBits depth) debug).primitives target)
             base.queries target opcode args debug reached)
          (called.1.map some, called.2))) := by
  have logical : Storage.operationProgram.run rows nested opcode = .ok (some source) := by
    simpa only [Interner.representativeReads, facts.projected, Nested.storageReads] using query
  have native := facts.operations nested opcode
  rw [logical] at native
  obtain ⟨slice, _, observed, good, _⟩ := facts.queried_input nested opcode (Operation.returned source) native
  have same := (BorrowedQuery.accepted base.allocator nested opcode before slice observed).1
  rw [query] at same
  cases Option.some.inj (Except.ok.inj same)
  have sourceGood : Good (view source) [left, right] before := items ▸ good
  have nativeIndex : (if right == repeated then some 1 else if left == repeated then some 0 else none) = some index := by
    simpa only [Nested.repeatedIndex, Nested.sameExpression, Interner.representativeReads,
      facts.projected, Nested.storageReads] using chosen
  refine ⟨native, good, ShiftInput.operand_good _ _ _ sourceGood 1 (by change 1 < 2; decide),
    ShiftInput.operand_good _ _ _ sourceGood 0 (by change 0 < 2; decide), nativeIndex, ?_⟩
  have routed := selected base owner usizeBits depth opcode nested repeated left right first debug before source index (by simpa only [facts.reads] using query) items (by simpa only [facts.reads] using chosen)
  have inside := Nested.repeated_index_bound _ left right repeated index chosen
  cases prepared : LocalArguments.zigLocal (view source) index repeated first before with
  | mk result reached =>
    cases result with
    | error fault =>
      change run base owner usizeBits (depth + 1) opcode nested repeated first debug before = (.error fault, reached)
      rw [routed]
      simp only [bind, Effect.bind, ViewInput.local_rejected _ _ _ _ _ _ _ _ _ _ _ _ prepared]
    | ok target =>
      have ready := ViewInput.local_input (view source) target left right repeated index first before reached
        (items ▸ good) inside prepared
      have retained := facts.frame (after := reached) ready.good.1
        ((congrArg Interner.Heap.representatives ready.graph).trans facts.projected)
        (congrArg Interner.Heap.table ready.graph) (congrArg Publication.Effects.keys ready.effects)
        (fun id cell found _ => ready.frame id cell found) (fun id block found => ready.heap ▸ found)
      refine ⟨ready, retained, ?_, ?_⟩
      · intro key old found nonempty length
        exact ready.key_apart _ _ _ _ facts.valid base.allocator key facts.live old
          (by rw [ready.effects] at found; exact found) nonempty length
      · rw [routed]
        simp only [bind, Effect.bind, ViewInput.local_prepared _ _ _ _ _ _ _ _ _ _ _ _ prepared]
        cases called : TemporaryArguments.unwind before.memory.memory.nextId
          (ConstructorItem.operation base.external base.budget base.allocator
            ((NativeRecursion.context base owner usizeBits (NativeRecursion.unfold base owner usizeBits depth) debug).primitives target)
            base.queries target opcode (if first then [left, right].set index repeated else [left, right]) debug reached) with
        | mk result after =>
          cases result <;> dsimp only [NativeRecursion.context] at called ⊢ <;> rw [called] <;> rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeLocal
