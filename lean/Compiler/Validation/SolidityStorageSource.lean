/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Validation.SolidityContract
import Compiler.Validation.SolidityABI
import Compiler.Validation.SolidityStorageLayout
import Contract.Evm.Projection

/-! The stateful statement spine reuses the existing Solidity word expressions
and ABI model. Names/layout are independently admitted from the complete source;
the compiler's storage-layout output is not an assumption. This fragment has
private word/Boolean fields, assignments, comparisons, branches, returns and
reverts. Declaration-order packing is derived by the shared layout model. -/
namespace Compiler.Validation.SolidityStorage
open Contract.Evm SolidityFunction SolidityCall
open Contract.Interaction (Word wordBytes)
open Stateful (Slots)

/-- Compatibility predicate for the original nonpayable word ABI. The typed
function model below uses `SolidityABI.Source.Accepts` through `Function.call`. -/
def Accepts (source : Source) (input : Input) : Prop :=
  input.value = 0 ∧ SolidityCall.AcceptsArguments source input

instance (source : Source) (input : Input) : Decidable (Accepts source input) :=
  inferInstanceAs (Decidable (_ ∧ _))

inductive Comparison where
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr

def Comparison.test : Comparison → Word → Word → Bool
  | .eq, a, b => decide (a = b)
  | .ne, a, b => decide (a ≠ b)
  | .lt, a, b => decide (a < b)
  | .le, a, b => decide (a ≤ b)
  | .gt, a, b => decide (b < a)
  | .ge, a, b => decide (b ≤ a)

inductive Condition where
  | literal (value : Bool)
  | boolean (value : SolidityWord.Expr)
  | compare (comparison : Comparison) (left right : SolidityWord.Expr)
  | not (value : Condition)
  | and (left right : Condition)
  | or (left right : Condition)

inductive Statement where
  | assign (slot : Nat) (value : SolidityWord.Expr)
  | ret (value : SolidityWord.Expr)
  | assignBool (field : Nat) (value : Condition)
  | stop
  | revert
  | branch (condition : Condition) (yes no : List Statement)

structure Function where
  abi : Source
  body : List Statement
  parameterTypes : List SolidityABI.Parameter := abi.parameters.map (fun _ => .word)
  returnsWord : Bool := true

/-- Names feed the existing expression evaluator; these types independently
determine selector and argument canonicality. Certificates check equal arity. -/
def Function.call (function : Function) : SolidityABI.Source :=
  { name := function.abi.name, parameters := function.parameterTypes, payable := function.abi.payable }

structure Receive where
  body : List Statement
  checked : Bool := true

structure ContractSource where
  variables : Layout
  functions : List Function
  receive : Option Receive := none

def locals (variables : Layout) (source : Source) (input : Input) (cells : Slots)
    (name : String) : Word :=
  if name ∈ source.parameters then source.locals input name else
    variables.read name cells

def expression (variables : Layout) (source : Source) (input : Input)
    (cells : Slots) (expr : SolidityWord.Expr) : Except (List UInt8) Word :=
  if source.checked then expr.evalChecked (locals variables source input cells)
  else .ok (expr.eval (locals variables source input cells))

/-- Boolean operands are evaluated left to right with short-circuiting. A
skipped operand cannot panic, even in a checked function or constructor. -/
def Condition.eval (variables : Layout) (source : Source) (input : Input)
    (cells : Slots) : Condition → Except (List UInt8) Bool
  | .literal value => .ok value
  | .boolean value => match expression variables source input cells value with
    | .error bytes => .error bytes
    | .ok word => .ok (decide (word ≠ 0))
  | .compare comparison left right =>
    match expression variables source input cells left with
    | .error bytes => .error bytes
    | .ok a => match expression variables source input cells right with
      | .error bytes => .error bytes
      | .ok b => .ok (comparison.test a b)
  | .not value => match value.eval variables source input cells with
    | .error bytes => .error bytes
    | .ok result => .ok (!result)
  | .and left right => match left.eval variables source input cells with
    | .error bytes => .error bytes
    | .ok false => .ok false
    | .ok true => right.eval variables source input cells
  | .or left right => match left.eval variables source input cells with
    | .error bytes => .error bytes
    | .ok true => .ok true
    | .ok false => right.eval variables source input cells

inductive Outcome where
  | returned (bytes : List UInt8) (storage : Slots)
  | reverted (bytes : List UInt8)
  | fault

inductive Flow where
  | next (storage : Slots)
  | halt (outcome : Outcome)

/- Statement order and branch selection are explicit. Arithmetic faults in a
condition stop before either arm; returns skip the remaining statements. RHS
evaluation precedes the static-write exception. The frame discards all writes
on either revert or exception. Expressions have no side effects and only one
panic code, so their unspecified operand order is unobservable here. -/
mutual
def statements (variables : Layout) (source : Source) (input : Input)
    (isStatic : Bool) (body : List Statement) (cells : Slots) : Flow :=
  match body with
  | [] => .next cells
  | first :: rest =>
    match statement variables source input isStatic first cells with
    | .next after => statements variables source input isStatic rest after
    | .halt result => .halt result
termination_by sizeOf body

def statement (variables : Layout) (source : Source) (input : Input)
    (isStatic : Bool) (stmt : Statement) (cells : Slots) : Flow :=
  match stmt with
  | .assign slot expr =>
    match expression variables source input cells expr with
    | .error bytes => .halt (.reverted bytes)
    | .ok value => if isStatic then .halt .fault else
        match variables.write slot value cells with
        | none => .halt .fault
        | some after => .next after
  | .assignBool field condition =>
    match condition.eval variables source input cells with
    | .error bytes => .halt (.reverted bytes)
    | .ok value => if isStatic then .halt .fault else
        match variables.write field (PackedBool.encode value) cells with
        | none => .halt .fault
        | some after => .next after
  | .stop => .halt (.returned [] cells)
  | .revert => .halt (.reverted [])
  | .ret expr =>
    match expression variables source input cells expr with
    | .error bytes => .halt (.reverted bytes)
    | .ok value => .halt (.returned (wordBytes value) cells)
  | .branch condition yes no =>
    match condition.eval variables source input cells with
    | .error bytes => .halt (.reverted bytes)
    | .ok selected => if selected then statements variables source input isStatic yes cells
                     else statements variables source input isStatic no cells
termination_by sizeOf stmt
end

/-- A shared body evaluator supplies the declared default return bytes only
on fallthrough; explicit returns, reverts and faults keep their own outcomes. -/
def bodyResult (variables : Layout) (abi : Source) (body : List Statement)
    (defaultReturn : List UInt8) (input : Input) (cells : Slots) (isStatic : Bool) : Outcome :=
  match statements variables abi input isStatic body cells with
  | .halt result => result
  | .next after => .returned defaultReturn after

def Function.result (variables : Layout) (source : Function) (input : Input)
    (cells : Slots) (isStatic : Bool) : Outcome :=
  bodyResult variables source.abi source.body (if source.returnsWord then wordBytes 0 else []) input cells isStatic

def Function.outcome (variables : Layout) (source : Function) (input : Input)
    (cells : Slots) (isStatic : Bool) : Outcome :=
  if source.call.Accepts input then source.result variables input cells isStatic else .reverted []

def Receive.result (variables : Layout) (source : Receive) (input : Input)
    (cells : Slots) (isStatic : Bool) : Outcome :=
  bodyResult variables
    { name := "receive", parameters := [], body := .literal 0, checked := source.checked, payable := true }
    source.body [] input cells isStatic

def select (source : ContractSource) (input : Input) : Option Function :=
  source.functions.find? fun function => decide
    (loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 function.call.selector)

def emptyOutcome (source : ContractSource) (input : Input) (cells : Slots) (isStatic : Bool) : Outcome :=
  match source.receive with
  | none => .reverted []
  | some receiver => receiver.result source.variables input cells isStatic

def outcome (source : ContractSource) (input : Input) (cells : Slots) (isStatic : Bool) : Outcome :=
  if input.calldata.length = 0 then emptyOutcome source input cells isStatic else
    if input.calldata.length < 4 then .reverted [] else
      match select source input with
      | none => .reverted []
      | some function => function.outcome source.variables input cells isStatic

/-- Gas, access warming and signed refunds are exact target observations. They
are not guessed by the source evaluator or required to survive optimization
unchanged. The checked trace fixes them, while this relation fixes source return
bytes and the entire persistent store. Reverting intermediate state is hidden
only because the shared frame semantics proves complete rollback. -/
def Conforms (expected : Outcome) (trace : Guarded.Trace Stateful.Effects) : Prop :=
  match expected with
  | .fault => trace = .fault
  | .returned bytes cells => ∃ used needed warm refund,
      trace = .finished used needed ⟨.returned bytes, cells, warm, refund⟩
  | .reverted bytes => ∃ used needed cells warm refund,
      trace = .finished used needed ⟨.reverted bytes, cells, warm, refund⟩

/-- Discharge eliminated earlier writes in the complete `overwrite` artifact;
the last value still fixes the entire store, including every other key. -/
theorem write_overwrite (cells : Slots) (key first last : Word) :
    Stateful.write (Stateful.write cells key first) key last = Stateful.write cells key last := by
  funext other
  by_cases same : other = key <;> simp [Stateful.write, same]

/-- Constructor optimization can remove an initializer overwritten after a
write to another slot. The whole store agrees, including when the keys alias. -/
theorem write_shadow (cells : Slots) (key other first middle last : Word) :
    Stateful.write (Stateful.write (Stateful.write cells key first) other middle) key last =
      Stateful.write (Stateful.write cells other middle) key last := by
  funext slot
  by_cases same : slot = key <;> simp [Stateful.write, same]

end Compiler.Validation.SolidityStorage
