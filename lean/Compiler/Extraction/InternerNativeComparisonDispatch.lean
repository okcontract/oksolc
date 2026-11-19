/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeUnaryDispatch
import Compiler.Extraction.DispatchComparisonProofs

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul

/-- Complete native comparison dispatch, including folding, both rule tables,
signed fallback and ordinary failure. No selected read or branch is assumed. -/
theorem comparison_dispatch_verified (other : Meaning) (reads : Nested.Reads)
    (children : Associative.Constructors Debug (GraphAction σ)) (usizeBits : Nat)
    (op : Folding.Op) (comparison : Dispatch.BooleanOperation op) (left right : NodeId)
    (debug : Debug) (before : World σ) (ready : World σ → Prop) (initial : ready before)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (proper : BuilderRules (Semantic.builderLogic (Folding.wordMeaning other) ready)
      (Dispatch.algebraicBuilder children) debug)
    (sound : Nested.Sound (Folding.wordMeaning other) before.graph.read reads)
    (a b : Word) (lhs : before.graph.read left = some a) (rhs : before.graph.read right = some b)
    (operand : Nested.OperandRead (GraphAction σ)) (address : Nat) :
    let ran := (Dispatch.simplifyWithInputs reads children usizeBits op.opcode [left, right] debug operand address) before
    (ordinary ran.1 = true → ready ran.2) ∧
    Semantic.Ensures (Folding.wordMeaning other) before.graph ran.1 ran.2.graph
      (fun found after => ∀ id, found = some id → after.read id = some (op.value a b 0)) := by
  exact binary_dispatch_verified other reads children usizeBits op.opcode left right debug before ready initial valid proper
    sound a b (op.value a b 0) 0 lhs rhs (Dispatch.comparison_word_value other op comparison 0 a b) operand address
    (Dispatch.Preservation.binary_comparison_safe
      (Semantic.builderLogic (Folding.wordMeaning other) ready) (Semantic.readRules _ ready)
      other reads children debug proper before ⟨initial, valid⟩ sound op comparison left right a b
      Dispatch.defaultOptions usizeBits operand lhs rhs)

section Native
attribute [local irreducible] Dispatch.simplifyWithInputs
variable (safety : Bool) (owner usizeBits : Nat) (base : PairInput.Context (Publication.Effects σ))
    (children : Constructors (Publication.Effects σ)) (debug : AssemblyItem.Fields.Values)
    (source : Compiler.ZigAir.Memory.WordArray.View) (address : Compiler.ZigAir.Memory.Address)
    (native : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (before : World (Publication.Effects σ)) {rows : List Storage.Cell}
    {data : Compiler.ZigAir.Memory.Address} {capacity : Nat} (left right : NodeId)
    (op : Folding.Op) (comparison : Dispatch.BooleanOperation op)
include comparison

local notation "p" => ShiftInput.Context.primitives (context base owner usizeBits children debug) source address native

theorem dispatcher_comparison_verified
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (arguments : key.arguments = [left, right]) (instruction : key.instruction = op.opcode)
    (other : Meaning) (expected : Word) (operation : key.kind = 1)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (evaluated : key.eval (Folding.wordMeaning other) before.graph.read = some expected)
    (ready : World (Publication.Effects σ) → Prop) (initial : ready before)
    (proper : BuilderRules (Semantic.builderLogic (Folding.wordMeaning other) ready)
      (Dispatch.algebraicBuilder children) debug) :
    (ordinary ((p).simplify key normalized before).1 = true → ready ((p).simplify key normalized before).2) ∧
    Semantic.Ensures (Folding.wordMeaning other) before.graph ((p).simplify key normalized before).1
      ((p).simplify key normalized before).2.graph (fun found after => ∀ id, found = some id → after.read id = some expected) := by
  apply dispatcher_binary_verified safety owner usizeBits base children debug source address native key normalized before
    left right facts arguments other expected operation valid evaluated ready initial proper
  intro a b lhs rhs denotation sound
  rw [instruction] at denotation ⊢
  have same := Option.some.inj ((Dispatch.comparison_word_value other op comparison key.sequence a b).symm.trans denotation)
  subst expected
  exact Dispatch.Preservation.binary_comparison_safe
    (Semantic.builderLogic (Folding.wordMeaning other) ready) (Semantic.readRules _ ready)
    other _ children debug proper before ⟨initial, valid⟩ sound op comparison left right a b
    Dispatch.defaultOptions usizeBits NativeRecursion.operand lhs rhs

/-- Consume complete comparison preservation through the existing native
owned-miss insertion, publication and cleanup contracts. -/
theorem miss_comparison_verified
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (arguments : key.arguments = [left, right]) (instruction : key.instruction = op.opcode)
    (other : Meaning) (expected : Word) (operation : key.kind = 1)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (evaluated : key.eval (Folding.wordMeaning other) before.graph.read = some expected)
    (ready frame : World (Publication.Effects σ) → Prop) (initial : ready before)
    (proper : BuilderRules (Semantic.builderLogic (Folding.wordMeaning other) ready)
      (Dispatch.algebraicBuilder children) debug)
    (request : Interner.Request) (lookup : Handle) (deterministic : Bool)
    (active : (deterministic && (request.item.kind == 1)) = true)
    (frames : MissFrames base.external base.allocator p ready frame key normalized lookup deterministic true)
    (words : MissWords base.external base.allocator p ready (Folding.wordMeaning other) expected
      key normalized lookup deterministic true) :
    let ran := Interner.findCode.controlMiss (OwnedCall.execution base.external base.allocator p) request key deterministic
      ⟨before, ⟨some lookup, some normalized, false⟩⟩
    let actual := OwnedCall.finish base.external base.allocator ran.1 ran.2
    FramePost frame actual ∧ Semantic.Ensures (Folding.wordMeaning other) before.graph actual.1 actual.2.world.graph
      (fun id after => after.read id = some expected) := by
  have dispatch := dispatcher_comparison_verified safety owner usizeBits base children debug source address native key normalized before
    left right op comparison facts arguments instruction other expected operation valid evaluated ready initial proper
  exact ⟨miss_frame base.external base.allocator p ready frame request key normalized lookup deterministic before initial
      (by simpa only [active] using frames) (fun _ => dispatch.1),
    miss_words base.external base.allocator p ready (Folding.wordMeaning other) expected request key normalized lookup deterministic
      before initial valid evaluated (by simpa only [active] using words) (fun _ => dispatch.1) (fun _ => dispatch.2)⟩
end Native
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
