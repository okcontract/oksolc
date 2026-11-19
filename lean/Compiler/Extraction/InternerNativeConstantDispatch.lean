/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeDispatch
import Compiler.Extraction.InternerNativeMissWords

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Recursive

theorem ordinary_map (result : Except Fault α) (f : α → β) : ordinary (result.map f) = ordinary result := by
  cases result <;> rfl

/-- Successful pure folding forwards its computed word to the actual constant
child. Every child outcome, including OOM and rejected faults, stops the rule
chain with that child's exact reached world. No allocation outcome is fixed. -/
theorem constant_dispatch_result (reads : Nested.Reads)
    (children : Associative.Constructors Debug (GraphAction σ)) (usizeBits : Nat)
    (instruction : Opcode) (arguments : List NodeId) (debug : Debug)
    (before : World σ) (values : List Word) (computed : Word)
    (bounded : arguments.length ≤ 3) (nonempty : arguments ≠ [])
    (collected : Dispatch.collectConstants reads arguments = .ok (some values))
    (folded : Folding.run Folding.helpers Folding.clauses instruction values = .ok (some computed))
    (operand : Nested.OperandRead (GraphAction σ) := Nested.logicalOperand) (address : Nat := 0) :
    (Dispatch.simplifyWithInputs reads children usizeBits instruction arguments debug operand address) before =
      ((children.constant computed debug before).1.map some, (children.constant computed debug before).2) := by
  have length : ¬ arguments.length > 3 := by omega
  have empty : arguments.isEmpty = false := by
    cases arguments with
    | nil => exact False.elim (nonempty rfl)
    | cons _ _ => rfl
  have first : (Dispatch.constantStage reads children instruction arguments debug) before =
      ((children.constant computed debug before).1.map some, (children.constant computed debug before).2) := by
    simp only [Dispatch.constantStage, length, empty, Bool.false_eq_true, or_self, ↓reduceIte, collected,
      Nested.readAction, folded, Dispatch.arithmetic, bind, Effect.bind, pure, Effect.pure]
    cases ran : children.constant computed debug before with
    | mk result after => cases result <;> rfl
  unfold Dispatch.simplifyWithInputs Dispatch.simplifyOptionsWithInputs
  simp only [Dispatch.orNext, bind, Effect.bind, first]
  cases ran : children.constant computed debug before with
  | mk result after => cases result <;> rfl

/-- Mapping the returned value retains the same physical failure classification
and graph. Ordinary OOM still requires the child's invariant and stability. -/
theorem ensures_map (meaning : Meaning) (before after : Interner.Heap) (result : Except Fault α)
    (f : α → β) (post : α → Interner.Heap → Prop) (target : β → Interner.Heap → Prop)
    (checked : Semantic.Ensures meaning before result after post)
    (mapped : ∀ value, post value after → target (f value) after) :
    Semantic.Ensures meaning before (result.map f) after target := by
  cases result with
  | error fault => exact checked
  | ok value => exact fun ordinary =>
      ⟨(checked ordinary).1, (checked ordinary).2.1, mapped value (checked ordinary).2.2⟩

/-- The first stage preserves words directly from the native constant-child
induction hypothesis. Allocator state remains in the actual world; no projected
constructor model or observational agreement premise is needed. -/
theorem constant_dispatch_words (other : Meaning) (reads : Nested.Reads)
    (children : Associative.Constructors Debug (GraphAction σ)) (usizeBits : Nat)
    (instruction : Opcode) (arguments : List NodeId) (debug : Debug)
    (before : World σ) (values collectedValues : List Word) (expected computed : Word) (sequence : BitVec 32)
    (bounded : arguments.length ≤ 3) (nonempty : arguments ≠ [])
    (collected : Dispatch.collectConstants reads arguments = .ok (some collectedValues))
    (folded : Folding.run Folding.helpers Folding.clauses instruction collectedValues = .ok (some computed))
    (sound : Nested.Sound (Folding.wordMeaning other) before.graph.read reads)
    (actual : readArguments before.graph.read arguments = some values)
    (denotation : (Folding.wordMeaning other).operation instruction sequence values = some expected)
    (proper : Semantic.Ensures (Folding.wordMeaning other) before.graph
      (children.constant computed debug before).1 (children.constant computed debug before).2.graph
      (fun id after => after.read id = some computed))
    (operand : Nested.OperandRead (GraphAction σ) := Nested.logicalOperand) (address : Nat := 0) :
    let executed := (Dispatch.simplifyWithInputs reads children usizeBits instruction arguments debug operand address) before
    Semantic.Ensures (Folding.wordMeaning other) before.graph executed.1 executed.2.graph
      (fun found after => ∀ id, found = some id → after.read id = some expected) := by
  have same := Dispatch.folded_value other before.graph.read reads sound instruction arguments values expected computed sequence
    actual denotation collected folded
  dsimp only
  rw [constant_dispatch_result reads children usizeBits instruction arguments debug before collectedValues computed
    bounded nonempty collected folded operand address]
  apply ensures_map _ _ _ _ some _ _ proper
  intro value read id found
  cases Option.some.inj found
  exact same ▸ read

section Native
attribute [local irreducible] Dispatch.simplifyWithInputs

variable (safety : Bool) (owner usizeBits : Nat) (base : PairInput.Context (Publication.Effects σ))
    (children : Constructors (Publication.Effects σ)) (debug : AssemblyItem.Fields.Values)
    (source : Compiler.ZigAir.Memory.WordArray.View) (address : Compiler.ZigAir.Memory.Address)
    (native : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (before : World (Publication.Effects σ)) {rows : List Storage.Cell}
    {data : Compiler.ZigAir.Memory.Address} {capacity : Nat}
    (collectedValues : List Word) (computed : Word)

local notation "p" => ShiftInput.Context.primitives (context base owner usizeBits children debug) source address native

/-- Native graph facts supply the actual collection query. The original
dispatcher performs it before invoking the same proper constant child. -/
theorem dispatcher_constant_result
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (bounded : key.arguments.length ≤ 3) (nonempty : key.arguments ≠ [])
    (collected : Dispatch.collectConstants (Nested.storageReads rows) key.arguments = .ok (some collectedValues))
    (folded : Folding.run Folding.helpers Folding.clauses key.instruction collectedValues = .ok (some computed)) :
    (p).simplify key normalized before =
      ((children.constant computed debug before).1.map some, (children.constant computed debug before).2) := by
  rw [dispatcher_snapshot, facts.reads, Interner.representativeReads, facts.projected]
  exact constant_dispatch_result _ children usizeBits key.instruction key.arguments debug before collectedValues computed
    bounded nonempty collected folded NativeRecursion.operand normalized.address

/-- Proper-child frame and word preservation suffice for this complete native
dispatch branch. The observations concern only the pure collection/fold; the
child's result, resource state and reached graph remain its actual execution. -/
theorem dispatcher_constant_verified
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (bounded : key.arguments.length ≤ 3) (nonempty : key.arguments ≠ [])
    (collected : Dispatch.collectConstants (Nested.storageReads rows) key.arguments = .ok (some collectedValues))
    (folded : Folding.run Folding.helpers Folding.clauses key.instruction collectedValues = .ok (some computed))
    (other : Meaning) (expected : Word) (operation : key.kind = 1)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (evaluated : key.eval (Folding.wordMeaning other) before.graph.read = some expected)
    (ready : World (Publication.Effects σ) → Prop)
    (childFrame : ordinary (children.constant computed debug before).1 = true → ready (children.constant computed debug before).2)
    (childWords : Semantic.Ensures (Folding.wordMeaning other) before.graph
      (children.constant computed debug before).1 (children.constant computed debug before).2.graph
      (fun id after => after.read id = some computed)) :
    (ordinary ((p).simplify key normalized before).1 = true → ready ((p).simplify key normalized before).2) ∧
    Semantic.Ensures (Folding.wordMeaning other) before.graph ((p).simplify key normalized before).1
      ((p).simplify key normalized before).2.graph (fun found after => ∀ id, found = some id → after.read id = some expected) := by
  have ran := dispatcher_constant_result safety owner usizeBits base children debug source address native key normalized
    before collectedValues computed facts bounded nonempty collected folded
  refine ⟨?_, ?_⟩
  · simpa only [ran, ordinary_map] using childFrame
  · have sound : Nested.Sound (Folding.wordMeaning other) before.graph.read (Nested.storageReads rows) := by
      simpa only [Interner.representativeReads, facts.projected] using
        Interner.representative_reads_sound (Folding.wordMeaning other) before.graph valid
    cases actual : readArguments before.graph.read key.arguments with
    | none => simp [Key.eval, actual] at evaluated
    | some values =>
      rw [dispatcher_snapshot, facts.reads, Interner.representativeReads, facts.projected]
      exact constant_dispatch_words other _ children usizeBits key.instruction key.arguments debug before values collectedValues
        expected computed key.sequence bounded nonempty collected folded sound actual
        (by simpa only [Key.eval, actual, operation] using evaluated) childWords NativeRecursion.operand normalized.address

/-- Consume the direct native dispatch result through the existing owned-miss
frame and word composition. Publication and failure cleanup use the child's
reached world. There is no logical child model or projection premise. -/
theorem miss_constant_verified
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (bounded : key.arguments.length ≤ 3) (nonempty : key.arguments ≠ [])
    (collected : Dispatch.collectConstants (Nested.storageReads rows) key.arguments = .ok (some collectedValues))
    (folded : Folding.run Folding.helpers Folding.clauses key.instruction collectedValues = .ok (some computed))
    (other : Meaning) (expected : Word) (operation : key.kind = 1)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (evaluated : key.eval (Folding.wordMeaning other) before.graph.read = some expected)
    (ready frame : World (Publication.Effects σ) → Prop) (initial : ready before)
    (request : Interner.Request) (lookup : Handle) (deterministic : Bool)
    (selected : (deterministic && (request.item.kind == 1)) = true)
    (frames : MissFrames base.external base.allocator p ready frame key normalized lookup deterministic true)
    (words : MissWords base.external base.allocator p ready (Folding.wordMeaning other) expected
      key normalized lookup deterministic true)
    (childFrame : ordinary (children.constant computed debug before).1 = true → ready (children.constant computed debug before).2)
    (childWords : Semantic.Ensures (Folding.wordMeaning other) before.graph
      (children.constant computed debug before).1 (children.constant computed debug before).2.graph
      (fun id after => after.read id = some computed)) :
    let ran := Interner.findCode.controlMiss (OwnedCall.execution base.external base.allocator p) request key deterministic
      ⟨before, ⟨some lookup, some normalized, false⟩⟩
    let actual := OwnedCall.finish base.external base.allocator ran.1 ran.2
    FramePost frame actual ∧ Semantic.Ensures (Folding.wordMeaning other) before.graph actual.1 actual.2.world.graph
      (fun id after => after.read id = some expected) := by
  have dispatch := dispatcher_constant_verified safety owner usizeBits base children debug source address native key normalized
    before collectedValues computed facts bounded nonempty collected folded other expected operation valid evaluated ready childFrame childWords
  exact ⟨miss_frame base.external base.allocator p ready frame request key normalized lookup deterministic before initial
      (by simpa only [selected] using frames) (fun _ => dispatch.1),
    miss_words base.external base.allocator p ready (Folding.wordMeaning other) expected request key normalized lookup deterministic
      before initial valid evaluated (by simpa only [selected] using words) (fun _ => dispatch.1) (fun _ => dispatch.2)⟩

end Native

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
