/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerAllocationRecursiveWords

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Recursive Caller.ProtocolTrace Interner.InvocationTrace

variable (env : AddressMask.Environment) (other : Meaning) (usizeBits : Nat)
    (seed : Interner.Primitives) (stream : List ProtocolEvent) (mismatch : Insertion.Native.Fault)
    (pushes : Associative.Pushes other) (pushValues : Insertion.Native.PushValues other) (depth : Nat)

include pushes pushValues

/-- Complete operation requests need not be among the dispatcher's folding
opcodes. Their evaluated request, rather than an opcode-specific law, supplies
the expected value. Recursive child words are already closed by induction. -/
theorem recursive_operation_safe (opcode : Opcode) (values : List NodeId) (debug : AssemblyItem.Fields.Values)
    (before : Interner.Heap) (expected : Word)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before)
    (evaluated : (Interner.constructorCode.operationRequest opcode values).item.eval
      (Dispatch.wordDispatchMeaning env other) before.read values 0 = some expected) :
    Interner.Safe (Dispatch.wordDispatchMeaning env other)
      ((streamReplay stream (recursiveModels (Dispatch.wordDispatchMeaning env other) usizeBits seed stream mismatch depth)).operation
        opcode values debug) before (fun id after => after.read id = some expected) := by
  cases depth with
  | zero =>
    exact enter_bind_safe _ stream _ before _ valid
      (fun _ cursor => Interner.Safe.fail _ _ .unsupported _ (valid.with_cursor cursor))
  | succ depth =>
    exact entry_request_safe env other usizeBits seed stream mismatch pushValues _
      (recursive_words env other usizeBits seed stream mismatch pushes pushValues depth) debug _ _ before expected valid evaluated

theorem recursive_constant_safe (value : Word) (debug : AssemblyItem.Fields.Values) (before : Interner.Heap)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before) :
    Interner.Safe (Dispatch.wordDispatchMeaning env other)
      ((streamReplay stream (recursiveModels (Dispatch.wordDispatchMeaning env other) usizeBits seed stream mismatch depth)).constant
        value debug) before (fun id after => after.read id = some value) :=
  (recursive_words env other usizeBits seed stream mismatch pushes pushValues depth).correct.constant value debug before valid

theorem recursive_materialize_safe (original : NodeId) (value : Word) (debug : AssemblyItem.Fields.Values) (before : Interner.Heap)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before) :
    Interner.Safe (Dispatch.wordDispatchMeaning env other)
      ((streamReplay stream (recursiveModels (Dispatch.wordDispatchMeaning env other) usizeBits seed stream mismatch depth)).materialize
        original value debug) before (fun id after => after.read id = some value) :=
  (recursive_words env other usizeBits seed stream mismatch pushes pushValues depth).correct.materialize original value debug before valid

/-- Borrowing changes native ownership, not the logical request. The native
consumer separately retains the actual source-query guard. -/
theorem recursive_borrowed_safe (address : Nat) (opcode : Opcode) (values : List NodeId)
    (debug : AssemblyItem.Fields.Values) (before : Interner.Heap) (expected : Word)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before)
    (evaluated : (Interner.constructorCode.operationRequest opcode values).item.eval
      (Dispatch.wordDispatchMeaning env other) before.read values 0 = some expected) :
    Interner.Safe (Dispatch.wordDispatchMeaning env other)
      ((streamReplay stream (recursiveModels (Dispatch.wordDispatchMeaning env other) usizeBits seed stream mismatch depth)).borrowedOperation
        address opcode values debug) before (fun id after => after.read id = some expected) := by
  cases depth with
  | zero =>
    exact enter_bind_safe _ stream _ before _ valid
      (fun _ cursor => Interner.Safe.fail _ _ .unsupported _ (valid.with_cursor cursor))
  | succ depth =>
    exact entry_request_safe env other usizeBits seed stream mismatch pushValues _
      (recursive_words env other usizeBits seed stream mismatch pushes pushValues depth) debug _ _ before expected valid evaluated

/-- The local request uses exactly the selected overwrite when `first` holds.
It does not silently substitute the original operands. -/
theorem recursive_local_safe (opcode : Opcode) (source : ArgumentSlice) (selected : Nat) (repeated : NodeId) (first : Bool)
    (debug : AssemblyItem.Fields.Values) (before : Interner.Heap) (expected : Word)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before)
    (evaluated : (Interner.constructorCode.operationRequest opcode
      (if first then source.items.set selected repeated else source.items)).item.eval
      (Dispatch.wordDispatchMeaning env other) before.read
      (if first then source.items.set selected repeated else source.items) 0 = some expected) :
    Interner.Safe (Dispatch.wordDispatchMeaning env other)
      ((streamReplay stream (recursiveModels (Dispatch.wordDispatchMeaning env other) usizeBits seed stream mismatch depth)).localOperation
        opcode source selected repeated first debug) before (fun id after => after.read id = some expected) := by
  cases depth with
  | zero =>
    exact enter_bind_safe _ stream _ before _ valid
      (fun _ cursor => Interner.Safe.fail _ _ .unsupported _ (valid.with_cursor cursor))
  | succ depth =>
    exact entry_request_safe env other usizeBits seed stream mismatch pushValues _
      (recursive_words env other usizeBits seed stream mismatch pushes pushValues depth) debug _ _ before expected valid evaluated

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
