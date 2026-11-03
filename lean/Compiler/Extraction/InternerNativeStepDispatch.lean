/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeStepBuilder
import Compiler.Extraction.InternerEnclosingNativeStepFrame

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

variable (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (base : PairInput.Context (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ))
    (env : AddressMask.Environment) (other : Meaning) (debug : AssemblyItem.Fields.Values)
    (rows : List Storage.Cell) (source : View) (values : List NodeId) (normalized : ArgumentSlice)
    (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue)
    (parent : World (Publication.Effects σ) → Prop)

local notation "meaning" => Dispatch.wordDispatchMeaning env other
local notation "nativeBase" => callerContext ops allocate safety owner meaning base growth
local notation "ready" => CallFrame safety base.allocator owner rows source values normalized address native parent

/-- A concrete live call derives the graph and indexed-input premises. Its
actual child entry proofs retain that same call through allocation and return. -/
theorem CallFrame.step_rules (children : Constructors (Publication.Effects σ))
    (stack : Enclosing safety base.allocator owner parent)
    (admitted : Admitted ops.arguments) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (pushes : Associative.Pushes other) (literals : Insertion.Native.PushValues other)
    (entries : StepEntryFrames safety owner usizeBits nativeBase children env other debug ready) :
    let callbacks := step nativeBase owner usizeBits children
    BuilderRules (Semantic.builderLogic meaning ready) (Dispatch.algebraicBuilder callbacks) debug ∧
      (∀ op, Dispatch.Preservation.OperationRule (Semantic.builderLogic meaning ready) callbacks debug op) ∧
      Dispatch.Preservation.SarRule (Semantic.builderLogic meaning ready) callbacks debug := by
  have graphs : ∀ world, ready world → ∃ current data capacity, NativeGraph.Facts safety base.allocator owner data capacity world current := by
    intro world frame
    obtain ⟨added, data, capacity, facts, _⟩ := frame.1.1
    exact ⟨rows ++ added, data, capacity, facts⟩
  exact ⟨step_builder_rules ops allocate safety owner usizeBits base growth children env other debug ready
      admitted typed graphs entries (.call stack) pushes literals,
    step_operation_rule ops allocate safety owner usizeBits base growth children env other debug ready
      admitted typed graphs entries (.call stack),
    step_sar_rule ops allocate safety owner usizeBits base growth children env other debug ready
      admitted typed graphs entries (.call stack)⟩

/-- Consume the shared SIGNEXTEND proof with actual recursive constructors.
Child callback laws and post-child input reads follow from native entry data;
suffix words follow from the actual insertion/publication implementations.
Original caller provenance and the shared native insertion reducer derive the
miss frame. Only lower-child entry duties remain. -/
theorem miss_signextend_unfold_verified (depth : Nat)
    (stack : Enclosing safety base.allocator owner parent)
    (admitted : Admitted ops.arguments) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (pushes : Associative.Pushes other) (literals : Insertion.Native.PushValues other)
    (entries : StepEntryFrames safety owner usizeBits nativeBase (unfold nativeBase owner usizeBits depth) env other debug ready)
    (before : World (Publication.Effects σ)) (initial : ready before)
    {data : Compiler.ZigAir.Memory.Address} {capacity : Nat}
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (key : Key) (left right : NodeId) (arguments : key.arguments = [left, right])
    (instruction : key.instruction = Dispatch.opSIGNEXTEND) (operation : key.kind = 1)
    (expected : Word) (valid : Interner.Invariant meaning before.graph)
    (evaluated : key.eval meaning before.graph.read = some expected)
    (aligned : key.arguments = normalized.items) (sequence : BitVec 32)
    (bound : keyCode.run native.item normalized.items sequence = some key)
    (request : Interner.Request) (sourceArguments : request.arguments = values)
    (lookup : Handle) (deterministic : Bool)
    {originBefore : World (Publication.Effects σ)} {originTaken : State (Publication.Effects σ)}
    {originValues : List NodeId} (originInitial : parent originBefore)
    (origin : Caller.Origin base.allocator source request originValues originBefore originTaken normalized lookup)
    (active : (deterministic && (request.item.kind == 1)) = true) :
    let p := (context nativeBase owner usizeBits (unfold nativeBase owner usizeBits (depth + 1)) debug).primitives source address native
    let ran := Interner.findCode.controlMiss (OwnedCall.execution (Publication.external ops.arguments) base.allocator p)
      request key deterministic ⟨before, ⟨some lookup, some normalized, false⟩⟩
    let actual := OwnedCall.finish (Publication.external ops.arguments) base.allocator ran.1 ran.2
    FramePost (GraphFrame safety base.allocator owner rows parent) actual ∧
      Semantic.Ensures meaning before.graph actual.1 actual.2.world.graph (fun id after => after.read id = some expected) := by
  have kind := Compiler.Extraction.Recursive.make_key_kind ⟨native.item, normalized.items, sequence⟩ normalized.items key
    (by simp only [Interner.makeKey, bound])
  have domain : (native.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues := by
    rw [← kind, operation]; decide
  have frames := stack.native_miss_frames originInitial origin rows address native ops allocate growth meaning
    ((context nativeBase owner usizeBits (unfold nativeBase owner usizeBits (depth + 1)) debug).primitives source address native)
    rfl rfl key deterministic true admitted aligned domain
  rw [sourceArguments] at frames
  have rules := CallFrame.step_rules ops allocate safety owner usizeBits base growth env other debug rows source values normalized address native parent
    (unfold nativeBase owner usizeBits depth) stack admitted typed pushes literals entries
  exact miss_signextend_verified safety owner usizeBits nativeBase
    (unfold nativeBase owner usizeBits (depth + 1)) debug source values address native key normalized before left right facts arguments instruction
    (AddressMask.addressMeaning env other) expected operation valid evaluated ready (GraphFrame safety base.allocator owner rows parent)
    initial rules.1 (rules.2.1 .signextend) rules.2.2 (fun _ frame => frame.1) request lookup deterministic active frames
    (native_miss_words ops allocate safety owner meaning base growth usizeBits
      (unfold nativeBase owner usizeBits (depth + 1)) debug source address native rows values normalized parent
      key lookup deterministic true expected aligned sequence bound (fun _ => literals))

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
