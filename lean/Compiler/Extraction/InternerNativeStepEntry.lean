/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeStepDispatch
import Compiler.Extraction.InternerNativeConstantEntry

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- SIGNEXTEND's noncommutative input keeps the original argument order. The
actual normalization and key encoder derive the native dispatch selection. -/
theorem signextend_request_key (request : Interner.Request) (values : List NodeId) (key : Key)
    (left right : NodeId) (kind : request.item.kind = 1)
    (instruction : request.item.instruction = some Dispatch.opSIGNEXTEND)
    (arguments : request.arguments = [left, right])
    (normalized : normalizeCode.run InsertionSort.sortIds request.item request.arguments = some values)
    (keyed : Interner.makeKey request values = .ok key) :
    key.arguments = [left, right] ∧ key.instruction = Dispatch.opSIGNEXTEND ∧ key.kind = 1 := by
  have valuesEqual : values = [left, right] := by
    simpa [normalizeCode, NormalizeCode.run, Test.run, kind, instruction, arguments, Dispatch.opSIGNEXTEND] using normalized.symm
  have encoded := keyed
  simp [Interner.makeKey, keyCode, KeyCode.run, Test.run, Scalar.run, kind, instruction, valuesEqual] at encoded
  subst key
  exact ⟨rfl, rfl, rfl⟩


section Entry
variable (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (base : PairInput.Context (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (env : AddressMask.Environment) (other : Meaning)
    (debug : AssemblyItem.Fields.Values) (source : View) (request : Interner.Request)
    (before : World (Publication.Effects σ)) (rows : List Storage.Cell)
    (parent : World (Publication.Effects σ) → Prop)

local notation "meaning" => Dispatch.wordDispatchMeaning env other
local notation "nativeBase" => callerContext ops allocate safety owner meaning base growth

-- Compose execution lemmas without expanding the interpreters during unification.
attribute [local irreducible] invoke step unfold Interner.FindCode.controlMiss OwnedCall.finish

/-- All entry routes for an actual SIGNEXTEND invocation share the existing
entry proof. Actual native misses consume the proper-depth child entry laws;
normalization derives the key selection. Constant entries follow from native
insertion frames; only operation children retain entry-model obligations.
No successful entry or separate model for the current entry is assumed.
Nondeterministic classification skips simplification. -/
theorem invocation_signextend_unfold_verified (depth : Nat)
    (stack : Enclosing safety base.allocator owner parent) (initial : parent before)
    {data : Compiler.ZigAir.Memory.Address} {capacity : Nat}
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (represented : Represents before.memory.memory source request.arguments)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys)
    (array : ArraySource source before.memory.memory)
    (admitted : Admitted ops.arguments) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (pushes : Associative.Pushes other) (literals : Insertion.Native.PushValues other)
    (left right : NodeId) (kind : request.item.kind = 1)
    (instruction : request.item.instruction = some Dispatch.opSIGNEXTEND)
    (arguments : request.arguments = [left, right])
    (expected : Word) (valid : Interner.Invariant meaning before.graph)
    (evaluated : request.item.eval meaning before.graph.read request.arguments request.sequence = some expected)
    (operations : ∀ site : ProtocolTrace.TakenSite σ, site.Reached nativeBase source request debug before →
      site.deterministic = true →
      StepEntryFrames.Operations safety owner usizeBits nativeBase (unfold nativeBase owner usizeBits depth) env other debug
        (CallFrame safety base.allocator owner rows source request.arguments site.normalized site.address
          (input request.item debug) parent)) :
    let children := unfold nativeBase owner usizeBits (depth + 1)
    let actual := invoke (Publication.external ops.arguments) base.budget base.allocator
      ((context nativeBase owner usizeBits children debug).primitives source) base.queries source request debug before
    InvocationPost meaning (GraphFrame safety base.allocator owner rows parent) before.graph actual expected ∧
      (∀ opcode borrowed, request = Interner.constructorCode.operationRequest opcode borrowed.items → source = view borrowed →
        let ran := (step nativeBase owner usizeBits children).borrowedOperation borrowed.address opcode borrowed.items debug before
        ordinary ran.1 = true → GraphFrame safety base.allocator owner rows parent ran.2 ∧
          Semantic.Ensures meaning before.graph ran.1 ran.2.graph (fun id after => after.read id = some expected)) := by
  have domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues := by
    rw [kind]; decide
  have retained : ∀ after, Valid after.memory → after.graph = before.graph → Retains before after → parent after :=
    fun _ good same kept => stack.retained initial good same kept
  apply step_invocation_verified_miss safety owner usizeBits capacity nativeBase ops.arguments
    (unfold nativeBase owner usizeBits (depth + 1)) source request debug before data rows parent env other expected
    rfl facts represented privateSource array admitted domain typed valid evaluated retained
    (fun constructed address made => stack.locals initial _ _ (Nat.le_refl _) (by
      have prepared := (prepare_success request.item debug before constructed address facts.valid domain typed made).2
      rw [prepared.nextId]; omega))
  intro site reached
  obtain ⟨item, _, parentConstructed, frame, takenFacts⟩ := reached.native_inputs facts privateSource array domain typed retained
  have keyValue := reached.key_value item env other expected valid evaluated
  have selection := signextend_request_key request site.values site.key left right kind instruction arguments
    reached.input.origin.normalized reached.keyed
  cases deterministic : site.deterministic with
  | true =>
    have entries := StepEntryFrames.of_operations ops allocate safety owner usizeBits base growth
      (unfold nativeBase owner usizeBits depth) env other debug _ (.call stack) admitted typed
      (operations site reached deterministic)
    have checked := miss_signextend_unfold_verified ops allocate safety owner usizeBits base growth env other debug rows source
      request.arguments site.normalized site.address (input request.item debug) parent depth stack admitted typed pushes literals
      entries site.taken.world frame takenFacts site.key left right selection.1 selection.2.1 selection.2.2
      expected keyValue.1 keyValue.2 reached.input.publication.aligned request.sequence reached.input.keyed request rfl site.lookup
      site.deterministic parentConstructed reached.input.origin (by simp only [deterministic, kind]; rfl)
    simpa only [deterministic] using checked
  | false =>
    let p := (context nativeBase owner usizeBits (unfold nativeBase owner usizeBits (depth + 1)) debug).primitives
      source site.address (input request.item debug)
    let ready := CallFrame safety base.allocator owner rows source request.arguments site.normalized site.address
      (input request.item debug) parent
    have frames := stack.native_miss_frames parentConstructed reached.input.origin rows site.address (input request.item debug)
      ops allocate growth meaning p rfl rfl site.key site.deterministic (site.deterministic && (request.item.kind == 1))
      admitted reached.input.publication.aligned domain
    have words := native_miss_words ops allocate safety owner meaning base growth usizeBits
      (unfold nativeBase owner usizeBits (depth + 1)) debug source site.address (input request.item debug) rows request.arguments
      site.normalized parent site.key site.lookup site.deterministic (site.deterministic && (request.item.kind == 1))
      expected reached.input.publication.aligned request.sequence reached.input.keyed (by
        intro impossible
        change request.item.kind = 2#32 at impossible
        rw [kind] at impossible
        contradiction)
    have framed := miss_frame (Publication.external ops.arguments) base.allocator p ready (GraphFrame safety base.allocator owner rows parent)
        request site.key site.normalized site.lookup site.deterministic site.taken.world frame frames
        (by simp only [deterministic, Bool.false_and, Bool.false_eq_true, false_implies])
    have semantic := miss_words (Publication.external ops.arguments) base.allocator p ready meaning expected request site.key site.normalized
        site.lookup site.deterministic site.taken.world frame keyValue.1 keyValue.2 words
        (by simp only [deterministic, Bool.false_and, Bool.false_eq_true, false_implies])
        (by simp only [deterministic, Bool.false_and, Bool.false_eq_true, false_implies])
    simpa only [deterministic] using And.intro framed semantic
end Entry

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
