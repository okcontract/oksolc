/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeConstructorWords
import Compiler.Extraction.InternerEnclosingFrames
import Compiler.Extraction.InternerNativeSignExtendDispatch

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- The existing constructor result supplies a builder postcondition at the
actual returned world. Its enclosing frame is retained on ordinary failure too. -/
theorem ConstructorPost.nativeSafe {meaning : Meaning} {frame ready : World σ → Prop}
    {before : World σ} {action : GraphAction σ NodeId} {expected : Word}
    (checked : ConstructorPost meaning frame before.graph (action before) expected)
    (retained : ∀ world, frame world → ready world) :
    Semantic.NativeSafe meaning ready action before (fun id after => after.graph.read id = some expected) := by
  intro completed
  exact ⟨retained _ (checked completed).1, (checked completed).2 completed⟩

/-- Local entry obligations for the actual constant and literal-operation
constructors. These are the existing reached-miss interfaces, not completed
child outcomes or a new constructor model. Literal preparation remains native. -/
structure StepEntryFrames (safety : Bool) (owner usizeBits : Nat)
    (base : PairInput.Context (Publication.Effects σ)) (children : Constructors (Publication.Effects σ))
    (env : AddressMask.Environment) (other : Meaning) (debug : AssemblyItem.Fields.Values)
    (ready : World (Publication.Effects σ) → Prop) : Prop where
  constant : ∀ value before rows data capacity,
    ready before → Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph →
    NativeGraph.Facts safety base.allocator owner data capacity before rows →
    EntryFrames safety owner usizeBits base children ⟨0, 0, 0⟩
      (Interner.constructorCode.constantRequest value) debug before rows ready env other
  operation : ∀ opcode ids before rows data capacity,
    ready before → Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph →
    NativeGraph.Facts safety base.allocator owner data capacity before rows →
    ∀ source prepared, Arguments.prepare ids before = (.ok source, prepared) →
    Arguments.Prepared ids before source prepared →
    EntryFrames safety owner usizeBits base children source
      (Interner.constructorCode.operationRequest opcode ids) debug prepared rows ready env other

section Rules
variable (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (base : PairInput.Context (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (children : Constructors (Publication.Effects σ))
    (env : AddressMask.Environment) (other : Meaning) (debug : AssemblyItem.Fields.Values)
    (ready : World (Publication.Effects σ) → Prop)

local notation "meaning" => Dispatch.wordDispatchMeaning env other
local notation "nativeBase" => callerContext ops allocate safety owner meaning base growth
local notation "nativeChildren" => step nativeBase owner usizeBits children

variable (admitted : Admitted ops.arguments) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (graphs : ∀ world, ready world → ∃ rows data capacity, NativeGraph.Facts safety base.allocator owner data capacity world rows)
    (entries : StepEntryFrames safety owner usizeBits
      (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth)
      children env other debug ready)
include admitted typed graphs entries

theorem step_constant_safe (pushes : Associative.Pushes other) (literals : Insertion.Native.PushValues other)
    (value : Word) (before : World (Publication.Effects σ))
    (valid : ready before ∧ Interner.Invariant meaning before.graph) :
    Semantic.NativeSafe meaning ready ((nativeChildren).constant value debug) before
      (fun id after => after.graph.read id = some value) := by
  obtain ⟨rows, data, capacity, facts⟩ := graphs before valid.1
  have checked := step_constant_native_verified ops allocate safety owner usizeBits base growth children env other
    facts admitted typed valid.2 value pushes literals
    (entries.constant value before rows data capacity valid.1 valid.2 facts)
  exact checked.nativeSafe (fun _ reached => reached.2)

/-- Native literal allocation, item preparation and return are discharged by
the existing all-entry theorem; the caller's enclosing stack derives cleanup. -/
theorem step_operation_safe (stack : Enclosing safety base.allocator owner ready)
    (opcode : Opcode) (ids : List NodeId) (values : List Word) (expected : Word)
    (before : World (Publication.Effects σ))
    (valid : ready before ∧ Interner.Invariant meaning before.graph)
    (actual : readArguments before.graph.read ids = some values)
    (evaluated : (meaning).operation opcode Interner.constructorCode.sequence values = some expected) :
    Semantic.NativeSafe meaning ready ((nativeChildren).operation opcode ids debug) before
      (fun id after => after.graph.read id = some expected) := by
  obtain ⟨rows, data, capacity, facts⟩ := graphs before valid.1
  have request : (Interner.constructorCode.operationRequest opcode ids).item.eval meaning before.graph.read
      ids Interner.constructorCode.sequence = some expected := by
    simpa [Interner.constructorCode, Interner.ConstructorCode.operationRequest, Scalar.run, Item.eval, actual] using evaluated
  have checked := step_operation_native_verified ops allocate safety owner usizeBits base growth children env other
    facts admitted typed valid.2 opcode ids request
    (entries.operation opcode ids before rows data capacity valid.1 valid.2 facts)
    (stack.cleanup valid.1 before.memory.memory.nextId (Nat.le_refl _))
  exact checked.nativeSafe (fun _ reached => reached.2)

theorem step_operation_rule (stack : Enclosing safety base.allocator owner ready) (op : Folding.Op) :
    Dispatch.Preservation.OperationRule (Semantic.builderLogic meaning ready) nativeChildren debug op := by
  intro ids values value before valid actual evaluated
  exact step_operation_safe ops allocate safety owner usizeBits base growth children env other debug ready admitted typed graphs entries stack
    op.opcode ids values value before valid actual
    ((Folding.word_meaning_operation (Dispatch.wordBaseMeaning env other) op Interner.constructorCode.sequence values).trans evaluated)

theorem step_builder_rules (stack : Enclosing safety base.allocator owner ready)
    (pushes : Associative.Pushes other) (literals : Insertion.Native.PushValues other) :
    BuilderRules (Semantic.builderLogic meaning ready) (Dispatch.algebraicBuilder nativeChildren) debug :=
  Dispatch.Preservation.builderRules_of_operations (Semantic.builderLogic meaning ready) nativeChildren debug
    (step_constant_safe ops allocate safety owner usizeBits base growth children env other debug ready admitted typed graphs entries pushes literals)
    (step_operation_rule ops allocate safety owner usizeBits base growth children env other debug ready admitted typed graphs entries stack)

theorem step_sar_rule (stack : Enclosing safety base.allocator owner ready) :
    Dispatch.Preservation.SarRule (Semantic.builderLogic meaning ready) nativeChildren debug := by
  intro left right amount word before valid lhs rhs
  change before.graph.read left = some amount at lhs
  change before.graph.read right = some word at rhs
  exact step_operation_safe ops allocate safety owner usizeBits base growth children env other debug ready admitted typed graphs entries stack
    ArithmeticShift.opcode [left, right] [amount, word] (ArithmeticShift.value amount word) before valid
    (by simp [readArguments, lhs, rhs])
    (ArithmeticShift.operation (AddressMask.addressMeaning env other) Interner.constructorCode.sequence [amount, word])
end Rules

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
