/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeUnaryDispatch
import Compiler.Extraction.DispatchSignExtendProofs

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul

/-- Complete native SIGNEXTEND dispatch, including folding, both tables,
loads after recursive constants, and the independent SAR interpretation. No selected read or branch is assumed. -/
theorem signextend_dispatch_verified (other : Meaning) (reads : Nested.Reads)
    (children : Associative.Constructors Debug (GraphAction σ)) (usizeBits : Nat)
    (left right : NodeId)
    (debug : Debug) (before : World σ) (ready : World σ → Prop) (initial : ready before)
    (valid : Interner.Invariant (ArithmeticShift.meaning other) before.graph)
    (proper : BuilderRules (Semantic.builderLogic (ArithmeticShift.meaning other) ready)
      (Dispatch.algebraicBuilder children) debug)
    (signextend : Dispatch.Preservation.OperationRule (Semantic.builderLogic (ArithmeticShift.meaning other) ready) children debug .signextend)
    (sar : Dispatch.Preservation.SarRule (Semantic.builderLogic (ArithmeticShift.meaning other) ready) children debug)
    (sound : Nested.Sound (ArithmeticShift.meaning other) before.graph.read reads)
    (a b : Word) (lhs : before.graph.read left = some a) (rhs : before.graph.read right = some b)
    (operand : Nested.OperandRead (GraphAction σ)) (address : Nat)
    (inputs : ∀ middle, ready middle ∧ Interner.Invariant (ArithmeticShift.meaning other) middle.graph →
      Dispatch.UnaryPreservation.Inputs (Semantic.builderLogic (ArithmeticShift.meaning other) ready) reads operand middle) :
    let ran := (Dispatch.simplifyWithInputs reads children usizeBits Dispatch.opSIGNEXTEND [left, right] debug operand address) before
    (ordinary ran.1 = true → ready ran.2) ∧
    Semantic.Ensures (ArithmeticShift.meaning other) before.graph ran.1 ran.2.graph
      (fun found after => ∀ id, found = some id → after.read id = some (Folding.Op.signextend.value a b 0)) := by
  exact binary_dispatch_verified (ArithmeticShift.shiftMeaning other) reads children usizeBits Dispatch.opSIGNEXTEND left right debug before ready initial valid proper
    sound a b (Folding.Op.signextend.value a b 0) 0 lhs rhs (Folding.word_meaning_operation (ArithmeticShift.shiftMeaning other) .signextend 0 [a, b]) operand address
    (Dispatch.Preservation.binary_signextend_safe
      (Semantic.builderLogic (ArithmeticShift.meaning other) ready) (Semantic.readRules _ ready)
      other reads children debug proper signextend sar before ⟨initial, valid⟩ sound operand inputs left right a b
      Dispatch.defaultOptions usizeBits lhs rhs)

section Native
attribute [local irreducible] Dispatch.simplifyWithInputs
variable (safety : Bool) (owner usizeBits : Nat) (base : PairInput.Context (Publication.Effects σ))
    (children : Constructors (Publication.Effects σ)) (debug : AssemblyItem.Fields.Values)
    (source : Compiler.ZigAir.Memory.WordArray.View) (sourceValues : List NodeId) (address : Compiler.ZigAir.Memory.Address)
    (native : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (before : World (Publication.Effects σ)) {rows : List Storage.Cell}
    {data : Compiler.ZigAir.Memory.Address} {capacity : Nat} (left right : NodeId)

local notation "p" => ShiftInput.Context.primitives (context base owner usizeBits children debug) source address native

theorem dispatcher_signextend_verified
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (arguments : key.arguments = [left, right]) (instruction : key.instruction = Dispatch.opSIGNEXTEND)
    (other : Meaning) (expected : Word) (operation : key.kind = 1)
    (valid : Interner.Invariant (ArithmeticShift.meaning other) before.graph)
    (evaluated : key.eval (ArithmeticShift.meaning other) before.graph.read = some expected)
    (ready : World (Publication.Effects σ) → Prop) (initial : ready before)
    (proper : BuilderRules (Semantic.builderLogic (ArithmeticShift.meaning other) ready)
      (Dispatch.algebraicBuilder children) debug)
    (signextend : Dispatch.Preservation.OperationRule (Semantic.builderLogic (ArithmeticShift.meaning other) ready) children debug .signextend)
    (sar : Dispatch.Preservation.SarRule (Semantic.builderLogic (ArithmeticShift.meaning other) ready) children debug)
    (framed : ∀ world, ready world → InputFrame safety base.allocator owner rows source sourceValues normalized world) :
    (ordinary ((p).simplify key normalized before).1 = true → ready ((p).simplify key normalized before).2) ∧
    Semantic.Ensures (ArithmeticShift.meaning other) before.graph ((p).simplify key normalized before).1
      ((p).simplify key normalized before).2.graph (fun found after => ∀ id, found = some id → after.read id = some expected) := by
  apply dispatcher_binary_verified safety owner usizeBits base children debug source address native key normalized before
    left right facts arguments (ArithmeticShift.shiftMeaning other) expected operation valid evaluated ready initial proper
  intro a b lhs rhs denotation sound
  rw [instruction] at denotation ⊢
  have word : (ArithmeticShift.meaning other).operation Dispatch.opSIGNEXTEND key.sequence [a, b] = some (Folding.Op.signextend.value a b 0) := by
    exact Folding.word_meaning_operation (ArithmeticShift.shiftMeaning other) .signextend key.sequence [a, b]
  have same := Option.some.inj (word.symm.trans denotation)
  subst expected
  exact Dispatch.Preservation.binary_signextend_safe
    (Semantic.builderLogic (ArithmeticShift.meaning other) ready) (Semantic.readRules _ ready)
    other _ children debug proper signextend sar before ⟨initial, valid⟩ sound NativeRecursion.operand
    (fun middle invariant => InputFrame.semantic_inputs (ArithmeticShift.meaning other) ready framed
      before.graph facts.projected middle invariant) left right a b Dispatch.defaultOptions usizeBits lhs rhs

/-- Consume complete SIGNEXTEND preservation through the existing native
owned-miss insertion, publication and cleanup contracts. -/
theorem miss_signextend_verified
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (arguments : key.arguments = [left, right]) (instruction : key.instruction = Dispatch.opSIGNEXTEND)
    (other : Meaning) (expected : Word) (operation : key.kind = 1)
    (valid : Interner.Invariant (ArithmeticShift.meaning other) before.graph)
    (evaluated : key.eval (ArithmeticShift.meaning other) before.graph.read = some expected)
    (ready frame : World (Publication.Effects σ) → Prop) (initial : ready before)
    (proper : BuilderRules (Semantic.builderLogic (ArithmeticShift.meaning other) ready)
      (Dispatch.algebraicBuilder children) debug)
    (signextend : Dispatch.Preservation.OperationRule (Semantic.builderLogic (ArithmeticShift.meaning other) ready) children debug .signextend)
    (sar : Dispatch.Preservation.SarRule (Semantic.builderLogic (ArithmeticShift.meaning other) ready) children debug)
    (framed : ∀ world, ready world → InputFrame safety base.allocator owner rows source sourceValues normalized world)
    (request : Interner.Request) (lookup : Handle) (deterministic : Bool)
    (active : (deterministic && (request.item.kind == 1)) = true)
    (frames : MissFrames base.external base.allocator p ready frame key normalized lookup deterministic true)
    (words : MissWords base.external base.allocator p ready (ArithmeticShift.meaning other) expected
      key normalized lookup deterministic true) :
    let ran := Interner.findCode.controlMiss (OwnedCall.execution base.external base.allocator p) request key deterministic
      ⟨before, ⟨some lookup, some normalized, false⟩⟩
    let actual := OwnedCall.finish base.external base.allocator ran.1 ran.2
    FramePost frame actual ∧ Semantic.Ensures (ArithmeticShift.meaning other) before.graph actual.1 actual.2.world.graph
      (fun id after => after.read id = some expected) := by
  have dispatch := dispatcher_signextend_verified safety owner usizeBits base children debug source sourceValues address native key normalized before
    left right facts arguments instruction other expected operation valid evaluated ready initial proper signextend sar framed
  exact ⟨miss_frame base.external base.allocator p ready frame request key normalized lookup deterministic before initial
      (by simpa only [active] using frames) (fun _ => dispatch.1),
    miss_words base.external base.allocator p ready (ArithmeticShift.meaning other) expected request key normalized lookup deterministic
      before initial valid evaluated (by simpa only [active] using words) (fun _ => dispatch.1) (fun _ => dispatch.2)⟩
end Native
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
