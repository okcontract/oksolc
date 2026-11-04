/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchDefaultProofs
import Compiler.Extraction.Normalization
import Compiler.Extraction.ObservedHeap

namespace Compiler.Extraction.Recursive
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
set_option linter.unusedSimpArgs false

abbrev Find := Request → Action NodeId

def FindSound (meaning : Meaning) (find : Find) : Prop :=
  ∀ request before value, Invariant meaning before →
    request.item.eval meaning before.read request.arguments request.sequence = some value →
    Safe meaning (find request) before (fun id after => after.read id = some value)

/-- Constructors use the extracted request encoding. Debug information is
outside this value projection, as in the existing implemented constructors. -/
def constructors (find : Find) : Constructors Debug where
  operation := fun opcode ids _ => find (constructorCode.operationRequest opcode ids)
  constant := fun value _ => find (constructorCode.constantRequest value)
  materialize := fun _ value _ => find (constructorCode.constantRequest value)

theorem constructors_interner (p : Primitives) :
    constructors (findCode.run p) = (implementedConstructors p : Constructors Debug) := rfl

theorem constructors_sound (other : Meaning) (pushes : Pushes other) (find : Find)
    (sound : FindSound (Folding.wordMeaning other) find) :
    ConstructorSound other (constructors find : Constructors Debug) := by
  constructor
  · intro op ids values value debug before valid arguments evaluated
    exact sound _ before value valid (word_operation_request_sound other before.read op ids values value arguments evaluated)
  · intro value debug before valid
    apply sound _ before value valid
    simpa [constructorCode, ConstructorCode.constantRequest, Scalar.run, Item.eval,
      readArguments, Folding.wordMeaning] using pushes value
  · intro original value debug before valid
    apply sound _ before value valid
    simpa [constructorCode, ConstructorCode.constantRequest, Scalar.run, Item.eval,
      readArguments, Folding.wordMeaning] using pushes value
  · intro address op ids values value debug before valid arguments evaluated
    exact sound _ before value valid (word_operation_request_sound other before.read op ids values value arguments evaluated)
  · intro op source selected repeated first values value debug before valid arguments evaluated
    exact sound _ before value valid (word_operation_request_sound other before.read op _ values value arguments evaluated)

theorem constructors_address (env : AddressMask.Environment) (other : Meaning) (find : Find)
    (sound : FindSound (AddressMask.meaning env other) find) :
    AddressMask.Constructs env other (constructors find : Constructors Debug).operation := by
  intro kind debug before valid
  apply sound _ before (kind.value env) valid
  change (AddressMask.meaning env other).operation kind.opcode 0 [] = some (kind.value env)
  exact AddressMask.address_operation env other kind 0 []

theorem constructors_sar (other : Meaning) (find : Find)
    (sound : FindSound (ArithmeticShift.meaning other) find) :
    ArithmeticShift.Constructs other (constructors find : Constructors Debug).operation := by
  intro left right amount value debug before valid lhs rhs
  apply sound _ before (ArithmeticShift.value amount value) valid
  simpa [constructorCode, ConstructorCode.operationRequest, Scalar.run, Item.eval,
    readArguments, lhs, rhs, ArithmeticShift.eval] using ArithmeticShift.operation other 0 [amount, value]

/-- Only ordinary primitive obligations remain here. The seed's simplify
callback is overwritten by the recursive step and has no correctness premise. -/
structure PrimitiveContracts (meaning : Meaning) (p : Primitives) : Prop where
  normalize : Normalizes meaning p
  insert : ∀ key deterministic before value, Invariant meaning before → key.eval meaning before.read = some value →
    Safe meaning (p.insert key deterministic) before (fun id after => after.read id = some value)
  publish : Publishes meaning p

/-- This guard defines the callback on non-operation keys, which the extracted
interner never passes to simplification. Its irrelevance is proved separately. -/
def operationOnly (action : Key → Action (Option NodeId)) (key : Key) : Action (Option NodeId) :=
  if key.kind = 1 then action key else pure none

theorem make_key_kind (request : Request) (args : List NodeId) (key : Key)
    (made : makeKey request args = .ok key) : key.kind = request.item.kind := by
  unfold makeKey at made
  cases encoded : keyCode.run request.item args request.sequence with
  | none => simp [encoded] at made
  | some produced =>
    simp only [encoded, Except.ok.injEq] at made
    subst produced
    unfold KeyCode.run at encoded
    cases guard : keyCode.instructionTest.run request.item with
    | false =>
      simp only [guard, Bool.false_eq_true, ↓reduceIte, Option.bind_some, Option.some.injEq] at encoded
      rw [← Option.some.inj encoded]
      rfl
    | true =>
      simp only [guard, ↓reduceIte] at encoded
      cases instruction : request.item.instruction with
      | none => simp [instruction] at encoded
      | some opcode =>
        simp only [instruction, Option.bind_some, Option.some.injEq] at encoded
        rw [← Option.some.inj encoded]
        rfl

theorem miss_operation_only (p : Primitives) (request : Request) (key : Key) (deterministic : Bool)
    (kind : key.kind = request.item.kind) :
    findCode.miss { p with simplify := operationOnly p.simplify } request key deterministic =
      findCode.miss p request key deterministic := by
  by_cases operation : request.item.kind = 1
  · simp [FindCode.miss, operationOnly, kind, operation]
  · have absent : (request.item.kind == 1) = false := beq_eq_false_iff_ne.mpr operation
    simp only [FindCode.miss, absent, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

theorem owned_operation_only (p : Primitives) (request : Request) (args : List NodeId) (deterministic : Bool) :
    findCode.owned { p with simplify := operationOnly p.simplify } request args deterministic =
      findCode.owned p request args deterministic := by
  unfold FindCode.owned
  apply congrArg (fun next : Unit → Action NodeId => liftLocal (p.takeOwned args) >>= next)
  funext ignored
  cases made : makeKey request args with
  | error error => rfl
  | ok key =>
    exact miss_operation_only p request key deterministic (make_key_kind request args key made)

/-- Extending the callback with an operation-key guard does not change any
execution of the extracted interner, including failures and cache hits. -/
theorem find_operation_only (p : Primitives) (request : Request) :
    findCode.run { p with simplify := operationOnly p.simplify } request = findCode.run p request := by
  unfold FindCode.run
  apply congrArg (fun next : Heap → Action NodeId => get >>= next)
  funext before
  by_cases capacity : p.atCapacity before = true
  · simp only [capacity, ↓reduceIte]
  · simp only [capacity, ↓reduceIte]
    apply congrArg (fun next : List NodeId → Action NodeId => liftLocal (p.normalize request) >>= next)
    funext args
    apply congrArg (fun next : Bool → Action NodeId => lift (p.deterministic request.item) >>= next)
    funext deterministic
    cases deterministic with
    | false => exact owned_operation_only p request args false
    | true =>
      apply congrArg (fun next : Key → Action NodeId => lift (makeKey request args) >>= next)
      funext key
      cases before.table key with
      | some id => rfl
      | none => exact owned_operation_only p request args true

def simplifier (reads : Heap → Reads) (find : Find) (usizeBits : Nat) : Key → Action (Option NodeId) :=
  operationOnly (fun key before =>
    Dispatch.simplify (reads before) (constructors find) usizeBits key.instruction key.arguments () before)

def step (p : Primitives) (reads : Heap → Reads) (usizeBits : Nat) (find : Find) : Find :=
  findCode.run { p with simplify := simplifier reads find usizeBits }

theorem step_source_body (p : Primitives) (reads : Heap → Reads) (usizeBits : Nat) (find : Find) :
    step p reads usizeBits find = findCode.run { p with simplify := (fun key before =>
      Dispatch.simplify (reads before) (constructors find) usizeBits key.instruction key.arguments () before) } := by
  funext request
  exact find_operation_only { p with simplify := (fun key before =>
    Dispatch.simplify (reads before) (constructors find) usizeBits key.instruction key.arguments () before) } request

theorem step_ignores_seed_simplifier (p : Primitives) (ignored : Key → Action (Option NodeId))
    (reads : Heap → Reads) (usizeBits : Nat) (find : Find) :
    step { p with simplify := ignored } reads usizeBits find = step p reads usizeBits find := rfl

theorem step_safe (env : AddressMask.Environment) (other : Meaning) (pushes : Pushes other)
    (p : Primitives) (primitive : PrimitiveContracts (Dispatch.wordDispatchMeaning env other) p)
    (reads : Heap → Reads)
    (coherent : ∀ before, Invariant (Dispatch.wordDispatchMeaning env other) before →
      Sound (Dispatch.wordDispatchMeaning env other) before.read (reads before))
    (usizeBits : Nat) (find : Find) (recursive : FindSound (Dispatch.wordDispatchMeaning env other) find) :
    FindSound (Dispatch.wordDispatchMeaning env other) (step p reads usizeBits find) := by
  have words := constructors_sound (Dispatch.wordBaseMeaning env other) pushes find recursive (Debug := Unit)
  have addresses := constructors_address env (ArithmeticShift.shiftMeaning other) find
    (by simpa only [Dispatch.word_dispatch_address_model] using recursive) (Debug := Unit)
  have shifts := constructors_sar (AddressMask.addressMeaning env other) find recursive (Debug := Unit)
  have contracts : Contracts (Dispatch.wordDispatchMeaning env other)
      { p with simplify := simplifier reads find usizeBits } := by
    constructor
    · exact primitive.normalize
    · intro key before value valid evaluated
      by_cases operation : key.kind = 1
      · have safe := Dispatch.default_key_simplify_safe env other (reads before) (constructors find)
          words addresses shifts before valid (coherent before valid) key operation value () usizeBits evaluated
        simpa only [simplifier, operationOnly, operation, ↓reduceIte] using safe
      · simpa only [simplifier, operationOnly, operation, ↓reduceIte] using
          (Safe.pure (Dispatch.wordDispatchMeaning env other) before none
            (fun result after => ∀ id, result = some id → after.read id = some value) valid (by simp))
    · exact primitive.insert
    · exact primitive.publish
  intro request before value valid evaluated
  exact find_safe _ _ contracts request before value valid evaluated

/-- A finite unfolding of the actual recursive body. `unsupported` at depth
zero is an explicit incomplete observation, not a native compiler error or a
successful fallback. There is no fixed verification bound: all depths are
quantified by the preservation theorem. -/
def unfold (p : Primitives) (reads : Heap → Reads) (usizeBits : Nat) : Nat → Find
  | 0 => fun _ => fail .unsupported
  | depth + 1 => step p reads usizeBits (unfold p reads usizeBits depth)

theorem unfold_safe (env : AddressMask.Environment) (other : Meaning) (pushes : Pushes other)
    (p : Primitives) (primitive : PrimitiveContracts (Dispatch.wordDispatchMeaning env other) p)
    (reads : Heap → Reads)
    (coherent : ∀ before, Invariant (Dispatch.wordDispatchMeaning env other) before →
      Sound (Dispatch.wordDispatchMeaning env other) before.read (reads before))
    (usizeBits depth : Nat) :
    FindSound (Dispatch.wordDispatchMeaning env other) (unfold p reads usizeBits depth) := by
  induction depth with
  | zero =>
    intro request before value valid _
    exact Safe.fail _ before .unsupported _ valid
  | succ depth ih => exact step_safe env other pushes p primitive reads coherent usizeBits _ ih

/-- The semantic normalization premise is discharged by the extracted code.
The remaining normalization boundary is its successful-result refinement and
the copy/sort permutation contract, including allocation and borrow framing. -/
theorem unfold_normalized_safe (env : AddressMask.Environment) (other : Meaning) (pushes : Pushes other)
    (p : Primitives) (sort : List NodeId → List NodeId)
    (permutation : ∀ ids, (sort ids).Perm ids) (normalization : NormalizationRefines sort p)
    (insertSafe : ∀ key deterministic before value, Invariant (Dispatch.wordDispatchMeaning env other) before →
      key.eval (Dispatch.wordDispatchMeaning env other) before.read = some value →
      Safe (Dispatch.wordDispatchMeaning env other) (p.insert key deterministic) before
        (fun id after => after.read id = some value))
    (publishSafe : Publishes (Dispatch.wordDispatchMeaning env other) p)
    (reads : Heap → Reads)
    (coherent : ∀ before, Invariant (Dispatch.wordDispatchMeaning env other) before →
      Sound (Dispatch.wordDispatchMeaning env other) before.read (reads before))
    (usizeBits depth : Nat) :
    FindSound (Dispatch.wordDispatchMeaning env other) (unfold p reads usizeBits depth) :=
  unfold_safe env other pushes p
    ⟨normalizes_of_source (Dispatch.wordBaseMeaning env other) sort permutation p normalization,
      insertSafe, publishSafe⟩ reads coherent usizeBits depth

/-- Source-bound representative reads are justified by the heap invariant.
There is no separate coherent-oracle premise. Physical memory refinement and
the remaining primitive contracts are still required. -/
theorem unfold_representatives_safe (env : AddressMask.Environment) (other : Meaning) (pushes : Pushes other)
    (p : Primitives) (primitive : PrimitiveContracts (Dispatch.wordDispatchMeaning env other) p)
    (usizeBits depth : Nat) :
    FindSound (Dispatch.wordDispatchMeaning env other) (unfold p representativeReads usizeBits depth) :=
  unfold_safe env other pushes p primitive representativeReads
    (fun heap valid => representative_reads_sound _ heap valid) usizeBits depth

/-- Finite observations of the recursively composed model. An exhausted
unfolding, or an unsupported primitive result, is retained as incomplete and
cannot witness this relation. Native memory/read refinement is separate. -/
def Executes (p : Primitives) (reads : Heap → Reads) (usizeBits : Nat)
    (request : Request) (before : Heap) (result : Except Error NodeId) (after : Heap) : Prop :=
  ∃ depth, unfold p reads usizeBits depth request before = (result, after) ∧ result ≠ .error .unsupported

theorem executes_safe (env : AddressMask.Environment) (other : Meaning) (pushes : Pushes other)
    (p : Primitives) (primitive : PrimitiveContracts (Dispatch.wordDispatchMeaning env other) p)
    (reads : Heap → Reads)
    (coherent : ∀ before, Invariant (Dispatch.wordDispatchMeaning env other) before →
      Sound (Dispatch.wordDispatchMeaning env other) before.read (reads before))
    (usizeBits : Nat) (request : Request) (before after : Heap) (result : Except Error NodeId)
    (value : Word) (valid : Invariant (Dispatch.wordDispatchMeaning env other) before)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.read
      request.arguments request.sequence = some value)
    (execution : Executes p reads usizeBits request before result after) :
    Invariant (Dispatch.wordDispatchMeaning env other) after ∧ Stable before after ∧
      (match (generalizing := false) result with | .error _ => True | .ok id => after.read id = some value) := by
  obtain ⟨depth, ran, _⟩ := execution
  have safe := unfold_safe env other pushes p primitive reads coherent usizeBits depth
    request before value valid evaluated result after ran
  cases result <;> exact safe

theorem unsupported_not_execution (p : Primitives) (reads : Heap → Reads) (usizeBits : Nat)
    (request : Request) (before after : Heap) :
    ¬Executes p reads usizeBits request before (.error .unsupported) after := by
  rintro ⟨_, _, complete⟩
  exact complete rfl

end Compiler.Extraction.Recursive
