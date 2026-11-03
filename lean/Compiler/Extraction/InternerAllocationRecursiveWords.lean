/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerAllocationWordModels

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Recursive Caller.ProtocolTrace Interner.InvocationTrace

/-- The dispatcher's three word obligations, for one and the same child family. -/
structure Words (env : AddressMask.Environment) (other : Meaning)
    (children : Associative.Constructors AssemblyItem.Fields.Values) : Prop where
  correct : Associative.ConstructorSound (Dispatch.wordBaseMeaning env other) children
  addresses : AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) children.operation
  shifts : ArithmeticShift.Constructs (AddressMask.addressMeaning env other) children.operation

variable (env : AddressMask.Environment) (other : Meaning) (usizeBits : Nat)
    (seed : Interner.Primitives) (stream : List ProtocolEvent) (mismatch : Insertion.Native.Fault)

/-- One entry proof for every evaluated request, including operations outside
the folding dispatcher. The actual entry event supplies the identity pair. -/
theorem entry_request_safe (pushValues : Insertion.Native.PushValues other)
    (children : Associative.Constructors AssemblyItem.Fields.Values) (words : Words env other children)
    (debug : AssemblyItem.Fields.Values) (initialId : Nat × Nat → Nat)
    (request : Interner.Request) (before : Interner.Heap) (value : Word)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.read request.arguments request.sequence = some value) :
    Interner.Safe (Dispatch.wordDispatchMeaning env other)
      (enter stream >>= fun ids => requestModel (Dispatch.wordDispatchMeaning env other) usizeBits seed stream mismatch
        children debug (initialId ids) request) before (fun id after => after.read id = some value) := by
  apply enter_bind_safe _ stream _ before _ valid
  intro ids cursor
  exact requestModel_safe env other usizeBits seed stream mismatch children words.correct words.addresses words.shifts
    debug (initialId ids) request _ value (valid.with_cursor cursor) (fun _ => pushValues) evaluated

/-- The general step uses actual request encodings, scoped normalization, traced
publication and insertion. Each constructor's identity arithmetic is retained;
all seven word obligations share the same request proof. -/
theorem body_words (pushes : Associative.Pushes other) (pushValues : Insertion.Native.PushValues other)
    (children : Associative.Constructors AssemblyItem.Fields.Values) (words : Words env other children) :
    Words env other (streamReplay stream
      (bodyModels (Dispatch.wordDispatchMeaning env other) usizeBits seed stream mismatch children)) := by
  have requestSafe := entry_request_safe env other usizeBits seed stream mismatch pushValues children words
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro op ids values value debug before valid arguments evaluated
    exact requestSafe debug _ _ before value valid
      (Nested.word_operation_request_sound (Dispatch.wordBaseMeaning env other) before.read op ids values value arguments evaluated)
  · intro value debug before valid
    apply requestSafe debug _ _ before value valid
    simpa [Interner.constructorCode, Interner.ConstructorCode.constantRequest, Scalar.run, Item.eval,
      readArguments, Folding.wordMeaning] using pushes value
  · intro original value debug before valid
    apply requestSafe debug _ _ before value valid
    simpa [Interner.constructorCode, Interner.ConstructorCode.constantRequest, Scalar.run, Item.eval,
      readArguments, Folding.wordMeaning] using pushes value
  · intro address op ids values value debug before valid arguments evaluated
    exact requestSafe debug _ _ before value valid
      (Nested.word_operation_request_sound (Dispatch.wordBaseMeaning env other) before.read op ids values value arguments evaluated)
  · intro op source selected repeated first values value debug before valid arguments evaluated
    exact requestSafe debug _ _ before value valid
      (Nested.word_operation_request_sound (Dispatch.wordBaseMeaning env other) before.read op _ values value arguments evaluated)
  · intro kind debug before valid
    rw [← Dispatch.word_dispatch_address_model] at valid ⊢
    apply requestSafe debug _ _ before (kind.value env) valid
    change (Dispatch.wordDispatchMeaning env other).operation kind.opcode 0 [] = some (kind.value env)
    rw [Dispatch.word_dispatch_address_model]
    exact AddressMask.address_operation env (ArithmeticShift.shiftMeaning other) kind 0 []
  · intro left right amount value debug before valid lhs rhs
    apply requestSafe debug _ _ before (ArithmeticShift.value amount value) valid
    simpa [Interner.constructorCode, Interner.ConstructorCode.operationRequest, Scalar.run, Item.eval,
      readArguments, lhs, rhs, ArithmeticShift.eval] using
      ArithmeticShift.operation (AddressMask.addressMeaning env other) 0 [amount, value]

/-- Every finite replay preserves words, including callback errors, mismatched
streams and recursion exhaustion. Child correctness is derived by induction;
no native result, final heap or proper-child word contract is a premise. -/
theorem recursive_words (pushes : Associative.Pushes other) (pushValues : Insertion.Native.PushValues other)
    (depth : Nat) :
    Words env other (streamReplay stream
      (recursiveModels (Dispatch.wordDispatchMeaning env other) usizeBits seed stream mismatch depth)) := by
  induction depth with
  | zero =>
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro op ids values value debug before valid _ _
      exact enter_bind_safe _ stream _ before _ valid (fun _ cursor => Interner.Safe.fail _ _ .unsupported _ (valid.with_cursor cursor))
    · intro value debug before valid
      exact enter_bind_safe _ stream _ before _ valid (fun _ cursor => Interner.Safe.fail _ _ .unsupported _ (valid.with_cursor cursor))
    · intro original value debug before valid
      exact enter_bind_safe _ stream _ before _ valid (fun _ cursor => Interner.Safe.fail _ _ .unsupported _ (valid.with_cursor cursor))
    · intro address op ids values value debug before valid _ _
      exact enter_bind_safe _ stream _ before _ valid (fun _ cursor => Interner.Safe.fail _ _ .unsupported _ (valid.with_cursor cursor))
    · intro op source selected repeated first values value debug before valid _ _
      exact enter_bind_safe _ stream _ before _ valid (fun _ cursor => Interner.Safe.fail _ _ .unsupported _ (valid.with_cursor cursor))
    · intro kind debug before valid
      exact enter_bind_safe _ stream _ before _ valid (fun _ cursor => Interner.Safe.fail _ _ .unsupported _ (valid.with_cursor cursor))
    · intro left right amount value debug before valid _ _
      exact enter_bind_safe _ stream _ before _ valid (fun _ cursor => Interner.Safe.fail _ _ .unsupported _ (valid.with_cursor cursor))
  | succ depth ih => exact body_words env other usizeBits seed stream mismatch pushes pushValues _ ih

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
