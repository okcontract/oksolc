/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeBuilder
import Compiler.Extraction.InternerNativeConstantDispatch

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul

/-- Default binary dispatch consists of its complete folding and binary
stages. It preserves the actual outcome and reached world at either stage. -/
theorem binary_dispatch_result (reads : Nested.Reads)
    (children : Associative.Constructors Debug (GraphAction σ)) (usizeBits : Nat)
    (instruction : Opcode) (left right : NodeId) (debug : Debug) (before : World σ)
    (operand : Nested.OperandRead (GraphAction σ)) (address : Nat) :
    (Dispatch.simplifyWithInputs reads children usizeBits instruction [left, right] debug operand address) before =
      Dispatch.orNext (Dispatch.constantStage reads children instruction [left, right] debug)
        (Dispatch.binaryStageWithInputs reads children usizeBits instruction left right debug Dispatch.defaultOptions operand) before := by
  unfold Dispatch.simplifyWithInputs Dispatch.simplifyOptionsWithInputs
  simp only [Dispatch.orNext, bind, Effect.bind, pure, Dispatch.defaultOptions]
  cases first : (Dispatch.constantStage reads children instruction [left, right] debug) before with
  | mk result middle => cases result with
    | error fault => rfl
    | ok option => cases option with
      | some found => rfl
      | none =>
        change Dispatch.orNext (Dispatch.binaryStageWithInputs reads children usizeBits instruction left right debug Dispatch.defaultOptions operand)
          (Dispatch.orNext (pure none) (pure none)) middle =
            (Dispatch.binaryStageWithInputs reads children usizeBits instruction left right debug Dispatch.defaultOptions operand) middle
        simp only [Dispatch.orNext, bind, Effect.bind, pure]
        cases next : (Dispatch.binaryStageWithInputs reads children usizeBits instruction left right debug Dispatch.defaultOptions operand) middle with
        | mk result after => cases result with
          | error fault => rfl
          | ok option => cases option <;> rfl

/-- Shared complete binary composition. A local binary-stage proof is consumed
immediately after the source-derived folding miss; child errors keep their world. -/
theorem binary_dispatch_verified (other : Meaning) (reads : Nested.Reads)
    (children : Associative.Constructors Debug (GraphAction σ)) (usizeBits : Nat)
    (instruction : Opcode) (left right : NodeId) (debug : Debug) (before : World σ)
    (ready : World σ → Prop) (initial : ready before)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (proper : BuilderRules (Semantic.builderLogic (Folding.wordMeaning other) ready)
      (Dispatch.algebraicBuilder children) debug)
    (sound : Nested.Sound (Folding.wordMeaning other) before.graph.read reads)
    (a b expected : Word) (sequence : BitVec 32)
    (lhs : before.graph.read left = some a) (rhs : before.graph.read right = some b)
    (denotation : (Folding.wordMeaning other).operation instruction sequence [a, b] = some expected)
    (operand : Nested.OperandRead (GraphAction σ)) (address : Nat)
    (next : Semantic.NativeSafe (Folding.wordMeaning other) ready
      (Dispatch.binaryStageWithInputs reads children usizeBits instruction left right debug Dispatch.defaultOptions operand)
      before (fun result after => ∀ id, result = some id → after.graph.read id = some expected)) :
    let ran := (Dispatch.simplifyWithInputs reads children usizeBits instruction [left, right] debug operand address) before
    (ordinary ran.1 = true → ready ran.2) ∧
    Semantic.Ensures (Folding.wordMeaning other) before.graph ran.1 ran.2.graph
      (fun found after => ∀ id, found = some id → after.read id = some expected) := by
  have first := Dispatch.Preservation.constant_stage_safe
    (Semantic.builderLogic (Folding.wordMeaning other) ready) (Semantic.readRules _ ready)
    other reads children instruction [left, right] [a, b] expected sequence debug before ⟨initial, valid⟩ sound
    (by change readArguments before.graph.read [left, right] = some [a, b]; simp [readArguments, lhs, rhs])
    denotation (fun _ _ _ _ _ => proper.constant _ before ⟨initial, valid⟩)
  have checked := Dispatch.Preservation.or_next_safe (Semantic.builderLogic (Folding.wordMeaning other) ready)
    _ _ before (fun id after => after.graph.read id = some expected) first next
  dsimp only
  rw [binary_dispatch_result]
  exact ⟨fun ordinary => (checked ordinary).1, Semantic.NativeSafe.ensures _ _ _ _ _ checked⟩

/-- The selected constant-rule table branch runs the original extracted apply
body. Later rules and operand reads do not run after any replacement outcome. -/
theorem algebraic_dispatch_result (reads : Nested.Reads)
    (children : Associative.Constructors Debug (GraphAction σ)) (usizeBits : Nat)
    (instruction : Opcode) (left right : NodeId) (debug : Debug) (before : World σ)
    (lc rc : Option Word) (replacement : Replacement)
    (collected : Dispatch.collectConstants reads [left, right] = .ok none)
    (leftRead : reads.constant left = .ok lc) (rightRead : reads.constant right = .ok rc)
    (selected : zigSelect instruction .constants ⟨lc, rc, false⟩ = some replacement)
    (operand : Nested.OperandRead (GraphAction σ) := Nested.logicalOperand) (address : Nat := 0) :
    (Dispatch.simplifyWithInputs reads children usizeBits instruction [left, right] debug operand address) before =
      ((zigApply replacement (Dispatch.algebraicBuilder children) left right debug before).1.map some,
        (zigApply replacement (Dispatch.algebraicBuilder children) left right debug before).2) := by
  have first : (Dispatch.constantStage reads children instruction [left, right] debug) before = (.ok none, before) := by
    simp only [Dispatch.constantStage, collected]
    rfl
  have second : (Dispatch.binaryStageWithInputs reads children usizeBits instruction left right debug
      Dispatch.defaultOptions operand) before =
      ((zigApply replacement (Dispatch.algebraicBuilder children) left right debug before).1.map some,
        (zigApply replacement (Dispatch.algebraicBuilder children) left right debug before).2) := by
    simp only [Dispatch.binaryStageWithInputs, leftRead, rightRead, Nested.readAction, selected,
      bind, Effect.bind, pure, Effect.pure]
    cases ran : zigApply replacement (Dispatch.algebraicBuilder children) left right debug before with
    | mk result after => cases result <;> rfl
  rw [binary_dispatch_result]
  simp only [Dispatch.orNext, bind, Effect.bind, first, second]

/-- Reliable native reads select the already-proved table denotation. The
shared replacement proof supplies both reached frames and words, including
ordinary failure after a successful earlier child. -/
theorem algebraic_dispatch_verified (other : Meaning) (reads : Nested.Reads)
    (children : Associative.Constructors Debug (GraphAction σ)) (usizeBits : Nat)
    (instruction : Opcode) (left right : NodeId) (debug : Debug) (before : World σ)
    (lc rc : Option Word) (replacement : Replacement)
    (collected : Dispatch.collectConstants reads [left, right] = .ok none)
    (leftRead : reads.constant left = .ok lc) (rightRead : reads.constant right = .ok rc)
    (selected : zigSelect instruction .constants ⟨lc, rc, false⟩ = some replacement)
    (ready : World σ → Prop) (initial : ready before)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (proper : BuilderRules (Semantic.builderLogic (Folding.wordMeaning other) ready)
      (Dispatch.algebraicBuilder children) debug)
    (sound : Nested.Sound (Folding.wordMeaning other) before.graph.read reads)
    (a b expected : Word) (sequence : BitVec 32)
    (lhs : before.graph.read left = some a) (rhs : before.graph.read right = some b)
    (denotation : (Folding.wordMeaning other).operation instruction sequence [a, b] = some expected)
    (operand : Nested.OperandRead (GraphAction σ) := Nested.logicalOperand) (address : Nat := 0) :
    let ran := (Dispatch.simplifyWithInputs reads children usizeBits instruction [left, right] debug operand address) before
    (ordinary ran.1 = true → ready ran.2) ∧
    Semantic.Ensures (Folding.wordMeaning other) before.graph ran.1 ran.2.graph
      (fun found after => ∀ id, found = some id → after.read id = some expected) := by
  have reliable := Dispatch.constant_facts_reliable _ _ reads sound left right a b lhs rhs lc rc leftRead rightRead
  have checked := Dispatch.Preservation.algebraic_selected_safe
    (Semantic.builderLogic (Folding.wordMeaning other) ready) other children debug proper before ⟨initial, valid⟩
    instruction sequence .constants ⟨lc, rc, false⟩ left right a b expected lhs rhs reliable replacement selected denotation
  have result := And.intro (fun ordinary => (checked ordinary).1)
    (Semantic.NativeSafe.ensures (Folding.wordMeaning other) ready _ before
      (fun found after => ∀ id, found = some id → after.read id = some expected) checked)
  dsimp only
  rw [algebraic_dispatch_result reads children usizeBits instruction left right debug before lc rc replacement
    collected leftRead rightRead selected operand address]
  cases ran : zigApply replacement (Dispatch.algebraicBuilder children) left right debug before with
  | mk outcome after =>
    cases outcome <;> simpa only [bind, Effect.bind, pure, Effect.pure, ran, Except.map] using result

section Native
attribute [local irreducible] Dispatch.simplifyWithInputs
variable (safety : Bool) (owner usizeBits : Nat) (base : PairInput.Context (Publication.Effects σ))
    (children : Constructors (Publication.Effects σ)) (debug : AssemblyItem.Fields.Values)
    (source : Compiler.ZigAir.Memory.WordArray.View) (address : Compiler.ZigAir.Memory.Address)
    (native : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (before : World (Publication.Effects σ)) {rows : List Storage.Cell}
    {data : Compiler.ZigAir.Memory.Address} {capacity : Nat}
    (left right : NodeId) (lc rc : Option Word) (replacement : Replacement)

local notation "p" => ShiftInput.Context.primitives (context base owner usizeBits children debug) source address native

/-- Derive the actual binary words and source queries once for all default
native binary consumers. Each consumer discharges only its own binary stage. -/
theorem dispatcher_binary_verified
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (arguments : key.arguments = [left, right])
    (other : Meaning) (expected : Word) (operation : key.kind = 1)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (evaluated : key.eval (Folding.wordMeaning other) before.graph.read = some expected)
    (ready : World (Publication.Effects σ) → Prop) (initial : ready before)
    (proper : BuilderRules (Semantic.builderLogic (Folding.wordMeaning other) ready)
      (Dispatch.algebraicBuilder children) debug)
    (next : ∀ a b, before.graph.read left = some a → before.graph.read right = some b →
      (Folding.wordMeaning other).operation key.instruction key.sequence [a, b] = some expected →
      Nested.Sound (Folding.wordMeaning other) before.graph.read (Nested.storageReads rows) →
      Semantic.NativeSafe (Folding.wordMeaning other) ready
        (Dispatch.binaryStageWithInputs (Nested.storageReads rows) children usizeBits key.instruction left right debug
          Dispatch.defaultOptions NativeRecursion.operand) before
        (fun result after => ∀ id, result = some id → after.graph.read id = some expected)) :
    (ordinary ((p).simplify key normalized before).1 = true → ready ((p).simplify key normalized before).2) ∧
    Semantic.Ensures (Folding.wordMeaning other) before.graph ((p).simplify key normalized before).1
      ((p).simplify key normalized before).2.graph (fun found after => ∀ id, found = some id → after.read id = some expected) := by
  have sound : Nested.Sound (Folding.wordMeaning other) before.graph.read (Nested.storageReads rows) := by
    simpa only [Interner.representativeReads, facts.projected] using
      Interner.representative_reads_sound (Folding.wordMeaning other) before.graph valid
  cases lhs : before.graph.read left with
  | none => simp [Key.eval, arguments, readArguments, lhs] at evaluated
  | some a =>
    cases rhs : before.graph.read right with
    | none => simp [Key.eval, arguments, readArguments, lhs, rhs] at evaluated
    | some b =>
      have denotation : (Folding.wordMeaning other).operation key.instruction key.sequence [a, b] = some expected := by
        simpa only [Key.eval, arguments, readArguments, lhs, rhs, operation] using evaluated
      rw [dispatcher_snapshot, facts.reads, Interner.representativeReads, facts.projected, arguments]
      exact binary_dispatch_verified other _ children usizeBits key.instruction left right debug before ready initial valid proper
        sound a b expected key.sequence lhs rhs denotation NativeRecursion.operand normalized.address
        (next a b lhs rhs denotation sound)

theorem dispatcher_algebraic_verified
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (arguments : key.arguments = [left, right])
    (collected : Dispatch.collectConstants (Nested.storageReads rows) [left, right] = .ok none)
    (leftRead : (Nested.storageReads rows).constant left = .ok lc)
    (rightRead : (Nested.storageReads rows).constant right = .ok rc)
    (selected : zigSelect key.instruction .constants ⟨lc, rc, false⟩ = some replacement)
    (other : Meaning) (expected : Word) (operation : key.kind = 1)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (evaluated : key.eval (Folding.wordMeaning other) before.graph.read = some expected)
    (ready : World (Publication.Effects σ) → Prop) (initial : ready before)
    (proper : BuilderRules (Semantic.builderLogic (Folding.wordMeaning other) ready)
      (Dispatch.algebraicBuilder children) debug) :
    (ordinary ((p).simplify key normalized before).1 = true → ready ((p).simplify key normalized before).2) ∧
    Semantic.Ensures (Folding.wordMeaning other) before.graph ((p).simplify key normalized before).1
      ((p).simplify key normalized before).2.graph (fun found after => ∀ id, found = some id → after.read id = some expected) := by
  have sound : Nested.Sound (Folding.wordMeaning other) before.graph.read (Nested.storageReads rows) := by
    simpa only [Interner.representativeReads, facts.projected] using
      Interner.representative_reads_sound (Folding.wordMeaning other) before.graph valid
  cases lhs : before.graph.read left with
  | none => simp [Key.eval, arguments, readArguments, lhs] at evaluated
  | some a =>
    cases rhs : before.graph.read right with
    | none => simp [Key.eval, arguments, readArguments, lhs, rhs] at evaluated
    | some b =>
      rw [dispatcher_snapshot, facts.reads, Interner.representativeReads, facts.projected, arguments]
      exact algebraic_dispatch_verified other _ children usizeBits key.instruction left right debug before lc rc replacement
        collected leftRead rightRead selected ready initial valid proper sound a b expected key.sequence lhs rhs
        (by simpa only [Key.eval, arguments, readArguments, lhs, rhs, operation] using evaluated)
        NativeRecursion.operand normalized.address

/-- Consume the selected rule's sequential native child proof through the same
owned-miss publication and cleanup contracts as the constant-fold branch. -/
theorem miss_algebraic_verified
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (arguments : key.arguments = [left, right])
    (collected : Dispatch.collectConstants (Nested.storageReads rows) [left, right] = .ok none)
    (leftRead : (Nested.storageReads rows).constant left = .ok lc)
    (rightRead : (Nested.storageReads rows).constant right = .ok rc)
    (selected : zigSelect key.instruction .constants ⟨lc, rc, false⟩ = some replacement)
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
  have dispatch := dispatcher_algebraic_verified safety owner usizeBits base children debug source address native key normalized before
    left right lc rc replacement facts arguments collected leftRead rightRead selected other expected operation valid evaluated ready initial proper
  exact ⟨miss_frame base.external base.allocator p ready frame request key normalized lookup deterministic before initial
      (by simpa only [active] using frames) (fun _ => dispatch.1),
    miss_words base.external base.allocator p ready (Folding.wordMeaning other) expected request key normalized lookup deterministic
      before initial valid evaluated (by simpa only [active] using words) (fun _ => dispatch.1) (fun _ => dispatch.2)⟩
end Native
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
