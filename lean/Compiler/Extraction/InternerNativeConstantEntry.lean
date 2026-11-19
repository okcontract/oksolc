/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeStepBuilder
import Compiler.Extraction.InternerNativeInactiveEntry

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- The unchanged operation field of `StepEntryFrames`, including actual
literal preparation. Constants do not need this child correspondence duty. -/
def StepEntryFrames.Operations (safety : Bool) (owner usizeBits : Nat)
    (base : PairInput.Context (Publication.Effects σ)) (children : Constructors (Publication.Effects σ))
    (env : AddressMask.Environment) (other : Meaning) (debug : AssemblyItem.Fields.Values)
    (ready : World (Publication.Effects σ) → Prop) : Prop :=
  ∀ opcode ids before rows data capacity,
    ready before → Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph →
    NativeGraph.Facts safety base.allocator owner data capacity before rows →
    ∀ source prepared, Arguments.prepare ids before = (.ok source, prepared) →
    Arguments.Prepared ids before source prepared →
    EntryFrames safety owner usizeBits base children source
      (Interner.constructorCode.operationRequest opcode ids) debug prepared rows ready env other

/-- Construct the existing builder-entry interface. Constant requests have
kind 2, so their source guard excludes every recursive child callback. Original
parent retention, cleanup and native miss frames are derived by the shared
inactive-entry theorem; only operation entries retain child-model duties. -/
theorem StepEntryFrames.of_operations (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (base : PairInput.Context (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (children : Constructors (Publication.Effects σ))
    (env : AddressMask.Environment) (other : Meaning) (debug : AssemblyItem.Fields.Values)
    (ready : World (Publication.Effects σ) → Prop) (stack : Enclosing safety base.allocator owner ready)
    (admitted : Admitted ops.arguments) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (operations : StepEntryFrames.Operations safety owner usizeBits
      (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth)
      children env other debug ready) :
    StepEntryFrames safety owner usizeBits
      (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth)
      children env other debug ready where
  constant := by
    intro value before rows data capacity initial _ facts
    exact stack.inactive_entry_frames ops allocate safety owner usizeBits base growth children env other debug
      ⟨0, 0, 0⟩ (Interner.constructorCode.constantRequest value) before rows ready initial facts.valid
      (by change (2 : Int) ∈ AssemblyItem.itemTagValues; decide) admitted typed
      (by intros; simp [Interner.ConstructorCode.constantRequest])
  operation := operations

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
