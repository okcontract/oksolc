/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeAlgebraicDispatch
import Compiler.Extraction.DispatchUnaryProofs

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Dispatch.UnaryPreservation

namespace ConstructorItem.NativeRecursion

/-- A proved native read projection supplies semantic preservation directly.
This uses only the indexed read relation, not a projected constructor model. -/
theorem inputs_of_projection (meaning : Meaning) (ready : World σ → Prop)
    (reads : Nested.Reads) (input : Nested.OperandRead (GraphAction σ))
    (related : Dispatch.Effects.Inputs (Recursive.projection ready) reads input)
    (before : World σ) (valid : ready before ∧ Interner.Invariant meaning before.graph) :
    Inputs (Semantic.builderLogic meaning ready) reads input before := by
  intro id opcode source query index annotation item completed
  have observed := related.queried id opcode source query index annotation item before valid.1 completed
  have result : (input source index annotation before).1 = .ok annotation := by
    simpa only [Nested.logicalOperand, pure, Effect.pure, Except.mapError] using observed.2.1
  have graph : (input source index annotation before).2.graph = before.graph := observed.2.2
  refine ⟨observed.1, ?_, ?_, ?_⟩
  · simpa only [graph] using valid.2
  · intro old value found
    simpa only [graph] using found
  · simp only [result]

/-- The existing parent-frame theorem derives loads from original query
slices at every valid reached state, including after append and relocation. -/
theorem InputFrame.semantic_inputs {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : Compiler.ZigAir.Memory.WordArray.View} {values : List NodeId} {normalized : ArgumentSlice}
    (meaning : Meaning) (ready : World (Publication.Effects σ) → Prop)
    (framed : ∀ world, ready world → InputFrame safety allocator owner rows source values normalized world)
    (heap : Interner.Heap) (projected : heap.representatives = some rows)
    (before : World (Publication.Effects σ)) (valid : ready before ∧ Interner.Invariant meaning before.graph) :
    Inputs (Semantic.builderLogic meaning ready) (Nested.storageReads rows) operand before := by
  apply inputs_of_projection meaning ready _ operand _ before valid
  simpa only [Interner.representativeReads, projected] using InputFrame.queries ready framed heap projected

/-- Native graph facts derive the unary initializer load at the queried source
and in-bounds index. Its logical annotation cannot supply the native value. -/
theorem unary_inputs (safety : Bool) (allocator owner : Nat) (before : World (Publication.Effects σ))
    {rows : List Storage.Cell} {data : Compiler.ZigAir.Memory.Address} {capacity : Nat}
    (facts : NativeGraph.Facts safety allocator owner data capacity before rows)
    (meaning : Meaning) (ready : World (Publication.Effects σ) → Prop)
    (initial : ready before) (valid : Interner.Invariant meaning before.graph) :
    Inputs (Semantic.builderLogic meaning ready) (Nested.storageReads rows) operand before := by
  intro id opcode source query index annotation item
  obtain ⟨inside, atIndex⟩ := List.getElem?_eq_some_iff.mp item
  have loaded := (facts.operand id opcode source query index inside annotation).2
  rw [atIndex] at loaded
  change Semantic.NativeSafe meaning ready (operand source index annotation) before (fun loaded _ => loaded = annotation)
  simp only [Semantic.NativeSafe, loaded]
  exact fun _ => ⟨initial, valid, fun _ _ found => found, trivial⟩

/-- The complete singleton dispatcher composes its folding and unary stages.
Default dispatch has no binary or revision-specific continuation for this shape. -/
theorem singleton_dispatch_result (reads : Nested.Reads)
    (children : Associative.Constructors Debug (GraphAction σ)) (usizeBits : Nat)
    (instruction : Opcode) (id : NodeId) (debug : Debug) (before : World σ)
    (operand : Nested.OperandRead (GraphAction σ)) (address : Nat) :
    (Dispatch.simplifyWithInputs reads children usizeBits instruction [id] debug operand address) before =
      Dispatch.orNext (Dispatch.constantStage reads children instruction [id] debug)
        (Dispatch.unaryStageWithInputs reads children instruction id debug operand) before := by
  unfold Dispatch.simplifyWithInputs Dispatch.simplifyOptionsWithInputs
  simp only [Dispatch.orNext, bind, Effect.bind, pure, Dispatch.defaultOptions]
  cases first : (Dispatch.constantStage reads children instruction [id] debug) before with
  | mk result middle => cases result with
    | error fault => rfl
    | ok option => cases option with
      | some found => rfl
      | none =>
        change Dispatch.orNext (Dispatch.unaryStageWithInputs reads children instruction id debug operand) (pure none) middle = _
        simp only [Dispatch.orNext, bind, Effect.bind]
        cases next : (Dispatch.unaryStageWithInputs reads children instruction id debug operand) middle with
        | mk result after => cases result with
          | error fault => rfl
          | ok option => cases option <;> rfl

/-- After the constant miss, the singleton dispatcher is exactly its unary
body. Its returned miss, match or fault retains the body's reached world. -/
theorem unary_dispatch_result (reads : Nested.Reads)
    (children : Associative.Constructors Debug (GraphAction σ)) (usizeBits : Nat)
    (instruction : Opcode) (id : NodeId) (debug : Debug) (before : World σ)
    (collected : Dispatch.collectConstants reads [id] = .ok none)
    (operand : Nested.OperandRead (GraphAction σ)) (address : Nat) :
    (Dispatch.simplifyWithInputs reads children usizeBits instruction [id] debug operand address) before =
      (Dispatch.unaryStageWithInputs reads children instruction id debug operand) before := by
  have first : (Dispatch.constantStage reads children instruction [id] debug) before = (.ok none, before) := by
    simp only [Dispatch.constantStage, collected]
    rfl
  rw [singleton_dispatch_result]
  simp only [Dispatch.orNext, bind, Effect.bind, first]

/-- Full native singleton preservation, with no assumed folding outcome. The
shared prefix and unary proofs retain exact child effects and ordinary failures. -/
theorem unary_dispatch_verified (other : Meaning) (reads : Nested.Reads)
    (children : Associative.Constructors Debug (GraphAction σ)) (usizeBits : Nat)
    (instruction : Opcode) (id : NodeId) (debug : Debug) (before : World σ)
    (ready : World σ → Prop) (initial : ready before)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (proper : Children (Semantic.builderLogic (Folding.wordMeaning other) ready) reads children debug)
    (sound : Nested.Sound (Folding.wordMeaning other) before.graph.read reads)
    (value expected : Word) (sequence : BitVec 32) (actual : before.graph.read id = some value)
    (denotation : (Folding.wordMeaning other).operation instruction sequence [value] = some expected)
    (constant : Dispatch.Preservation.ConstantChild (Semantic.builderLogic (Folding.wordMeaning other) ready)
      reads children instruction [id] debug before expected)
    (operand : Nested.OperandRead (GraphAction σ)) (address : Nat)
    (inputs : Inputs (Semantic.builderLogic (Folding.wordMeaning other) ready) reads operand before) :
    let ran := (Dispatch.simplifyWithInputs reads children usizeBits instruction [id] debug operand address) before
    (ordinary ran.1 = true → ready ran.2) ∧
    Semantic.Ensures (Folding.wordMeaning other) before.graph ran.1 ran.2.graph
      (fun found after => ∀ result, found = some result → after.read result = some expected) := by
  have first := Dispatch.Preservation.constant_stage_safe
    (Semantic.builderLogic (Folding.wordMeaning other) ready) (Semantic.readRules _ ready)
    other reads children instruction [id] [value] expected sequence debug before ⟨initial, valid⟩ sound
    (by change readArguments before.graph.read [id] = some [value]; simp [readArguments, actual]) denotation constant
  have next := Dispatch.UnaryPreservation.unary_stage_safe
    (Semantic.builderLogic (Folding.wordMeaning other) ready) (Semantic.readRules _ ready)
    other reads children debug proper before ⟨initial, valid⟩ sound instruction id value expected sequence actual denotation operand inputs
  have checked := Dispatch.Preservation.or_next_safe (Semantic.builderLogic (Folding.wordMeaning other) ready)
    _ _ before (fun result after => after.graph.read result = some expected) first next
  dsimp only
  rw [singleton_dispatch_result reads children usizeBits instruction id debug before operand address]
  exact ⟨fun ordinary => (checked ordinary).1, Semantic.NativeSafe.ensures _ _ _ _ _ checked⟩

section Native
attribute [local irreducible] Dispatch.simplifyWithInputs
variable (safety : Bool) (owner usizeBits : Nat) (base : PairInput.Context (Publication.Effects σ))
    (children : Constructors (Publication.Effects σ)) (debug : AssemblyItem.Fields.Values)
    (source : Compiler.ZigAir.Memory.WordArray.View) (address : Compiler.ZigAir.Memory.Address)
    (native : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (before : World (Publication.Effects σ)) {rows : List Storage.Cell}
    {data : Compiler.ZigAir.Memory.Address} {capacity : Nat} (id : NodeId)

local notation "p" => ShiftInput.Context.primitives (context base owner usizeBits children debug) source address native

theorem dispatcher_unary_verified
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (arguments : key.arguments = [id])
    (other : Meaning) (expected : Word) (operation : key.kind = 1)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (evaluated : key.eval (Folding.wordMeaning other) before.graph.read = some expected)
    (ready : World (Publication.Effects σ) → Prop) (initial : ready before)
    (proper : Children (Semantic.builderLogic (Folding.wordMeaning other) ready) (Nested.storageReads rows) children debug)
    (constant : Dispatch.Preservation.ConstantChild (Semantic.builderLogic (Folding.wordMeaning other) ready)
      (Nested.storageReads rows) children key.instruction [id] debug before expected) :
    (ordinary ((p).simplify key normalized before).1 = true → ready ((p).simplify key normalized before).2) ∧
    Semantic.Ensures (Folding.wordMeaning other) before.graph ((p).simplify key normalized before).1
      ((p).simplify key normalized before).2.graph (fun found after => ∀ result, found = some result → after.read result = some expected) := by
  have sound : Nested.Sound (Folding.wordMeaning other) before.graph.read (Nested.storageReads rows) := by
    simpa only [Interner.representativeReads, facts.projected] using
      Interner.representative_reads_sound (Folding.wordMeaning other) before.graph valid
  cases actual : before.graph.read id with
  | none => simp [Key.eval, arguments, readArguments, actual] at evaluated
  | some value =>
    rw [dispatcher_snapshot, facts.reads, Interner.representativeReads, facts.projected, arguments]
    exact unary_dispatch_verified other _ children usizeBits key.instruction id debug before ready initial valid proper
      sound value expected key.sequence actual (by simpa only [Key.eval, arguments, readArguments, actual, operation] using evaluated)
      constant operand normalized.address (unary_inputs safety base.allocator owner before facts _ ready initial valid)

/-- Immediately consume the complete unary stage through the existing native
owned-miss frame, publication, insertion and cleanup contracts. -/
theorem miss_unary_verified
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (arguments : key.arguments = [id])
    (other : Meaning) (expected : Word) (operation : key.kind = 1)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (evaluated : key.eval (Folding.wordMeaning other) before.graph.read = some expected)
    (ready frame : World (Publication.Effects σ) → Prop) (initial : ready before)
    (proper : Children (Semantic.builderLogic (Folding.wordMeaning other) ready) (Nested.storageReads rows) children debug)
    (constant : Dispatch.Preservation.ConstantChild (Semantic.builderLogic (Folding.wordMeaning other) ready)
      (Nested.storageReads rows) children key.instruction [id] debug before expected)
    (request : Interner.Request) (lookup : Handle) (deterministic : Bool)
    (active : (deterministic && (request.item.kind == 1)) = true)
    (frames : MissFrames base.external base.allocator p ready frame key normalized lookup deterministic true)
    (words : MissWords base.external base.allocator p ready (Folding.wordMeaning other) expected
      key normalized lookup deterministic true) :
    let ran := Interner.findCode.controlMiss (OwnedCall.execution base.external base.allocator p) request key deterministic
      ⟨before, ⟨some lookup, some normalized, false⟩⟩
    let actual := OwnedCall.finish base.external base.allocator ran.1 ran.2
    FramePost frame actual ∧ Semantic.Ensures (Folding.wordMeaning other) before.graph actual.1 actual.2.world.graph
      (fun result after => after.read result = some expected) := by
  have dispatch := dispatcher_unary_verified safety owner usizeBits base children debug source address native key normalized before
    id facts arguments other expected operation valid evaluated ready initial proper constant
  exact ⟨miss_frame base.external base.allocator p ready frame request key normalized lookup deterministic before initial
      (by simpa only [active] using frames) (fun _ => dispatch.1),
    miss_words base.external base.allocator p ready (Folding.wordMeaning other) expected request key normalized lookup deterministic
      before initial valid evaluated (by simpa only [active] using words) (fun _ => dispatch.1) (fun _ => dispatch.2)⟩
end Native
end ConstructorItem.NativeRecursion
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
