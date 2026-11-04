/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCheckpointConstructorReplay
import Compiler.Extraction.InternerAllocationSourceReplay

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Recursive Caller.ProtocolTrace Interner.InvocationTrace

def requestModel (meaning : Meaning) (usizeBits : Nat) (seed : Interner.Primitives)
    (stream : List ProtocolEvent) (mismatch : Insertion.Native.Fault)
    (children : Associative.Constructors AssemblyItem.Fields.Values)
    (debug : AssemblyItem.Fields.Values) (initialId : Nat) (request : Interner.Request) : Interner.Action NodeId :=
  Interner.Scoped.find (resources stream (.preparation .incomplete))
    (ConstructorItem.ProtocolTrace.CheckpointEntry.model meaning usizeBits debug children seed stream mismatch initialId request.item) request

def bodyModels (meaning : Meaning) (usizeBits : Nat) (seed : Interner.Primitives)
    (stream : List ProtocolEvent) (mismatch : Insertion.Native.Fault)
    (children : Associative.Constructors AssemblyItem.Fields.Values) : Models where
  operation := fun opcode values debug ids => requestModel meaning usizeBits seed stream mismatch children debug
    (ids.1 + if values.isEmpty then 0 else 1) (Interner.constructorCode.operationRequest opcode values)
  constant := fun value debug ids => requestModel meaning usizeBits seed stream mismatch children debug ids.1
    (Interner.constructorCode.constantRequest value)
  materialize := fun _ value debug ids => requestModel meaning usizeBits seed stream mismatch children debug ids.1
    (Interner.constructorCode.constantRequest value)
  borrowedOperation := fun _ opcode values debug ids => requestModel meaning usizeBits seed stream mismatch children debug ids.1
    (Interner.constructorCode.operationRequest opcode values)
  localOperation := fun opcode source selected repeated first debug ids => requestModel meaning usizeBits seed stream mismatch children debug
    (ids.1 + 1) (Interner.constructorCode.operationRequest opcode (if first then source.items.set selected repeated else source.items))

def exhaustedModels : Models where
  operation := fun _ _ _ _ heap => (.error .unsupported, heap)
  constant := fun _ _ _ heap => (.error .unsupported, heap)
  materialize := fun _ _ _ _ heap => (.error .unsupported, heap)
  borrowedOperation := fun _ _ _ _ _ heap => (.error .unsupported, heap)
  localOperation := fun _ _ _ _ _ _ _ heap => (.error .unsupported, heap)

def recursiveModels (meaning : Meaning) (usizeBits : Nat) (seed : Interner.Primitives)
    (stream : List ProtocolEvent) (mismatch : Insertion.Native.Fault) : Nat → Models
  | 0 => exhaustedModels
  | depth + 1 => bodyModels meaning usizeBits seed stream mismatch (streamReplay stream (recursiveModels meaning usizeBits seed stream mismatch depth))

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Recursive
open Caller.ProtocolTrace (ProtocolEvent)

/-- The canonical resource relation, quantified over the live frames needed by
recursive calls. The model family is fixed by the caller's rebased complete stream. -/
def RecursiveSources (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (meaning : Meaning)
    (base : PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (debug : AssemblyItem.Fields.Values) (depth : Nat) (models : List ProtocolEvent → Models) : Prop :=
  ∀ (leading stream : List ProtocolEvent) (root : ChildTrace.TracedWorld σ ProtocolEvent)
    (rows : List Storage.Cell) (source : View) (values : List NodeId) (normalized : ArgumentSlice)
    (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue)
    (parent : World (Publication.Effects σ) → Prop),
    Enclosing safety base.allocator owner parent →
    (Resource.projection ChildTrace.history stream (cursorGraph (MissStream.childCursor leading.length root))
      (Frame root (CallFrame safety base.allocator owner rows source values normalized address native parent))).SourceConstructorsAt
      (Nested.storageReads rows) debug (children ops allocate safety owner meaning base growth usizeBits depth)
      (replay leading stream root (models (rebase leading (ChildTrace.history root).length stream)))

/-- Exhaustion is a retained nonordinary rejection. This base case does not
stand in for ordinary allocation failures of a real constructor body. -/
theorem recursive_sources_zero (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (meaning : Meaning)
    (base : PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (debug : AssemblyItem.Fields.Values) :
    RecursiveSources ops allocate safety owner usizeBits meaning base growth debug 0 (fun _ => exhaustedModels) := by
  intro leading stream root rows source values normalized address native parent stack
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro opcode ids tag
    exact ⟨fun before => ⟨_, rfl⟩, fun before initial inside completed => by cases completed⟩
  · intro value tag
    exact ⟨fun before => ⟨_, rfl⟩, fun before initial inside completed => by cases completed⟩
  · intro id value tag
    exact ⟨fun before => ⟨_, rfl⟩, fun before initial inside completed => by cases completed⟩
  · intro id queried slice found opcode tag
    exact ⟨fun before => ⟨_, rfl⟩, fun before initial inside completed => by cases completed⟩
  · intro id opcode slice found shape selected bound repeated first tag
    exact ⟨fun before => ⟨_, rfl⟩, fun before initial inside completed => by cases completed⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
