/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeStepEntry
import Compiler.Extraction.InternerNativeSignExtendTests
import Compiler.Extraction.InternerNativeResourceAdmissionTests
import Compiler.Extraction.InternerRecursiveResourceMiss
import Compiler.Extraction.InternerNativeAllocationIdentityTests
import Compiler.Extraction.InternerNativeFrameInductionTests
import Compiler.Extraction.InternerNativeAllocationEntryTests
import Compiler.Extraction.InternerAllocationCallerReplay
import Compiler.Extraction.InternerCheckpointConstructorBodies
import Compiler.Extraction.InternerAllocationRecursiveReplayTests
import Compiler.Extraction.InternerAllocationWordTests
import Compiler.Extraction.InternerAllocationNativeConstructors
import Compiler.Extraction.InternerAllocationInvocationWords
import Compiler.Extraction.InternerNativeInvocationAdmission
import Compiler.Extraction.InternerNativeFindWordsTests
import Compiler.Extraction.InternerCallerProtocolHistoryTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeStepTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open NativeRecursion Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Exercise the capacity control branch without manufacturing billions of
native rows. This query override is a regression, not production admission. -/
def full (base : PairInput.Context σ) : PairInput.Context σ :=
  { base with queries := { base.queries with atCapacity := fun _ => true } }

theorem entry_at_capacity (safety : Bool) (owner usizeBits : Nat)
    (base : PairInput.Context (Publication.Effects σ)) (children : Constructors (Publication.Effects σ))
    (env : AddressMask.Environment) (other : Meaning) (debug : AssemblyItem.Fields.Values)
    (parent : World (Publication.Effects σ) → Prop) (stack : Enclosing safety base.allocator owner parent)
    (before : World (Publication.Effects σ)) (initial : parent before)
    (rows : List Storage.Cell) (source : View) (request : Interner.Request)
    (valid : Valid before.memory) (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (typed : AssemblyItem.Initializers.DebugTyped debug) :
    EntryFrames safety owner usizeBits (full base) children source request debug before rows parent env other where
  retained := fun _ good same kept => stack.retained initial good same kept
  localParent := by
    intro constructed address made
    have prepared := (prepare_success request.item debug before constructed address valid domain typed made).2
    exact stack.locals initial _ _ (Nat.le_refl _) (by rw [prepared.nextId]; omega)
  taken := by
    intro constructed address pointer memory values prepared taken key normalized lookup deterministic made room
    cases room

/-- Every entry premise is constructed from initial native validity, the actual
literal preparation, and the impossible reached-miss guard. No completed child
outcome or correspondence model is assumed. -/
theorem entries_at_capacity (safety : Bool) (owner usizeBits : Nat)
    (base : PairInput.Context (Publication.Effects σ)) (children : Constructors (Publication.Effects σ))
    (env : AddressMask.Environment) (other : Meaning) (debug : AssemblyItem.Fields.Values)
    (parent : World (Publication.Effects σ) → Prop) (stack : Enclosing safety base.allocator owner parent)
    (typed : AssemblyItem.Initializers.DebugTyped debug) :
    StepEntryFrames safety owner usizeBits (full base) children env other debug parent where
  constant := by
    intro value before rows data capacity initial semantic facts
    exact entry_at_capacity safety owner usizeBits base children env other debug parent stack before initial
      rows _ _ facts.valid (by change (2 : Int) ∈ AssemblyItem.itemTagValues; decide) typed
  operation := by
    intro opcode ids before rows data capacity initial semantic facts source prepared made actual
    have reached := stack.retained initial actual.good.1 actual.graph
      ⟨congrArg Publication.Effects.keys actual.effects, actual.frame, fun _ _ found => actual.heap ▸ found⟩
    exact entry_at_capacity safety owner usizeBits base children env other debug parent stack prepared reached
      rows source _ actual.good.1 (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) typed

theorem capacity_rules (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (base : PairInput.Context (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (children : Constructors (Publication.Effects σ))
    (env : AddressMask.Environment) (other : Meaning) (debug : AssemblyItem.Fields.Values)
    (rows : List Storage.Cell) (source : View) (values : List NodeId) (normalized : ArgumentSlice)
    (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue)
    (parent : World (Publication.Effects σ) → Prop) (stack : Enclosing safety base.allocator owner parent)
    (admitted : Admitted ops.arguments) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (pushes : Associative.Pushes other) (literals : Insertion.Native.PushValues other) :
    let meaning := Dispatch.wordDispatchMeaning env other
    let ready := CallFrame safety base.allocator owner rows source values normalized address native parent
    let callbacks := step (callerContext ops allocate safety owner meaning (full base) growth) owner usizeBits children
    BuilderRules (Semantic.builderLogic meaning ready) (Dispatch.algebraicBuilder callbacks) debug ∧
      (∀ op, Dispatch.Preservation.OperationRule (Semantic.builderLogic meaning ready) callbacks debug op) ∧
      Dispatch.Preservation.SarRule (Semantic.builderLogic meaning ready) callbacks debug :=
  CallFrame.step_rules ops allocate safety owner usizeBits (full base) growth env other debug rows source values normalized address native parent
    children stack admitted typed pushes literals
    (StepEntryFrames.of_operations ops allocate safety owner usizeBits (full base) growth children env other debug _
      (.call stack) admitted typed
      (entries_at_capacity safety owner usizeBits (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth)
        children env other debug _ (.call stack) typed).operation)

open NativeAllocationAdmissionTests (before)
open RecursiveTests (debug)

def callbacks (safety : Bool) := unfold (full (ReachablePrefixTests.base safety)) 6 64 1
def constant (safety : Bool) := (callbacks safety).constant 1 debug (before safety true)
def operation (safety : Bool) := (callbacks safety).operation 3 [4, 4] debug (before safety true)

attribute [local irreducible] constant operation before

/-- Capacity returns after item preparation. Literal operations additionally
allocate and retire their argument array. Neither path reaches the allocator. -/
theorem constant_observed (safety : Bool) :
    ((constant safety).1, (constant safety).2.memory.memory.nextId,
      (constant safety).2.memory.memory.heap.lookup (before safety true).memory.memory.nextId,
      (constant safety).2.memory.effects) =
    (.error (.language .capacity), (before safety true).memory.memory.nextId + 1,
      none, (before safety true).memory.effects) := by
  cases safety <;> insertion_kernel_rfl

theorem operation_observed (safety : Bool) :
    ((operation safety).1, (operation safety).2.memory.memory.nextId,
      (operation safety).2.memory.memory.heap.lookup (before safety true).memory.memory.nextId,
      (operation safety).2.memory.memory.heap.lookup ((before safety true).memory.memory.nextId + 1),
      (operation safety).2.memory.effects) =
    (.error (.language .capacity), (before safety true).memory.memory.nextId + 2,
      none, none, (before safety true).memory.effects) := by
  cases safety <;> insertion_kernel_rfl

theorem parent_operand_survives (safety : Bool) :
    ((NativeReads.reads 6 (constant safety).2.memory.memory).constant 4,
      (NativeReads.reads 6 (operation safety).2.memory.memory).constant 4) =
    (.ok (some 0), .ok (some 0)) := by
  cases safety <;> insertion_kernel_rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeStepTests
