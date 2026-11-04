/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.NestedProofs
import Compiler.Extraction.ConstructorProofs

namespace Compiler.Extraction.Nested
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.Extraction.Interner Contract.Yul

abbrev OperationBuilder (Debug : Type) (m : Type → Type := Action) := Opcode → List NodeId → Debug → m NodeId

/-- A named local retains its source allocation and selected overwrite slot.
The logical projection below erases only storage, not the selected operands. -/
abbrev LocalOperationBuilder (Debug : Type) (m : Type → Type := Action) :=
  Opcode → ArgumentSlice → Nat → NodeId → Bool → Debug → m NodeId

def localArguments (source : ArgumentSlice) (selected : Nat) (repeated : NodeId) (first : Bool) : List NodeId :=
  if first then source.items.set selected repeated else source.items

def localBuilder (build : OperationBuilder Debug m) : LocalOperationBuilder Debug m :=
  fun opcode source selected repeated first debug => build opcode (localArguments source selected repeated first) debug

/-- Reads leave the graph untouched. A modeled safety fault is never converted
into an ordinary missing match or an allocation error. -/
def readAction {m : Type → Type} [Monad m] [MonadLift (Except Interner.Error) m] (result : Except ReadError α) : m α :=
  match result with
  | .ok value => pure value
  | .error .invalidId => monadLift (Except.error (ε := Interner.Error) .invalidId)
  | .error .invalidOptional => monadLift (Except.error (ε := Interner.Error) .invalidOptional)
  | .error .safetyFault => monadLift (Except.error (ε := Interner.Error) .safetyFault)

/-- Evaluate a read-only query at its source position. Logical clients use an
entry snapshot; native clients supply the reads of the reached memory. -/
abbrev QueryRead (m : Type → Type) := {α : Type} → (Reads → Except ReadError α) → m α

/-- Reuse the extracted native constructor for every opcode, not a second
implementation of interning. Debug locations are outside the value projection. -/
def internerBuilder (p : Primitives) : OperationBuilder Debug := fun opcode ids _ =>
  findCode.run p (constructorCode.operationRequest opcode ids)

def Constructs (other : Meaning) (build : OperationBuilder Debug) : Prop :=
  ∀ (op : Folding.Op) ids values value debug before, Invariant (Folding.wordMeaning other) before →
    readArguments before.read ids = some values → op.eval values = some value →
    Safe (Folding.wordMeaning other) (build op.opcode ids debug) before
      (fun id after => after.read id = some value)

def LocalConstructs (other : Meaning) (build : LocalOperationBuilder Debug) : Prop :=
  ∀ (op : Folding.Op) source selected repeated first values value debug before,
    Invariant (Folding.wordMeaning other) before →
    readArguments before.read (localArguments source selected repeated first) = some values →
    op.eval values = some value →
    Safe (Folding.wordMeaning other) (build op.opcode source selected repeated first debug) before
      (fun id after => after.read id = some value)

theorem local_constructs (other : Meaning) (build : OperationBuilder Debug) (sound : Constructs other build) :
    LocalConstructs other (localBuilder build) := by
  intro op source selected repeated first values value debug before valid arguments evaluated
  exact sound op _ values value debug before valid arguments evaluated

theorem word_operation_request_sound (other : Meaning) (read : Read) (op : Folding.Op)
    (ids : List NodeId) (values : List Word) (value : Word)
    (arguments : readArguments read ids = some values) (denotation : op.eval values = some value) :
    let request := constructorCode.operationRequest op.opcode ids
    request.item.eval (Folding.wordMeaning other) read request.arguments request.sequence = some value := by
  simpa [constructorCode, ConstructorCode.operationRequest, Scalar.run, Item.eval,
    arguments, Folding.word_meaning_operation] using denotation

theorem interner_constructs (other : Meaning) (p : Primitives)
    (contracts : Contracts (Folding.wordMeaning other) p) :
    Constructs other (internerBuilder p : OperationBuilder Debug) := by
  intro op ids values value debug before valid arguments denotation
  exact find_safe (Folding.wordMeaning other) p contracts _ before value valid
    (word_operation_request_sound other before.read op ids values value arguments denotation)

theorem read_action_bind_safe (meaning : Meaning) (before : Heap) (result : Except ReadError α)
    (next : α → Action β) (post : β → Heap → Prop) (valid : Invariant meaning before)
    (continuation : ∀ value, result = .ok value → Safe meaning (next value) before post) :
    Safe meaning (readAction result >>= next) before post := by
  cases result with
  | ok value => exact continuation value rfl
  | error error => cases error <;> exact Safe.fail meaning before _ post valid

end Compiler.Extraction.Nested
