/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryAir
import Compiler.ZigAir.MemoryScalarBytes
import Compiler.ZigAir.MemoryRecordFields
import Compiler.ZigAir.MemoryByteRange

/-! Aggregate registers reuse the heap's sparse typed leaves. Missing leaves
remain uninitialized through assignment, load and return; scalar reads still
use `Memory.load`. The admitted aggregate transfers are whole root objects.
Nested transfers remain outside this client. Integer byte-array casts preserve
their checked subobject address; array-to-slice conversion retains its extent.
There is one heap, allocator, scalar interpreter and structured control engine.
Source/AIR translation and native backend preservation remain separate. -/
namespace Compiler.ZigAir.AggregateAir
open Memory

inductive Register where
  | value (value : Value)
  | aggregate (type : Ty) (cells : Cells)
  /-- Captured anonymous empty byte storage. Its byte sequence is observable;
  pointer identity, pointer projection and heap storage remain unsupported. This
  is not a heap Value and cannot alias or initialize an allocation. -/
  | emptyBytes
  /-- Evaluated byte-array value, without pointer identity or padding. -/
  | bytes (data : List (BitVec 8))
  deriving DecidableEq, Repr

def aggregateType : Ty → Bool
  | type@(.aggregate ..) => type.layout.isSome
  | _ => false

def Register.type : Register → Ty
  | .value primitive => primitive.type
  | .aggregate owner _ => owner
  | .bytes data => .array data.length (.scalar (.int false 8))
  | .emptyBytes => .slice false (.scalar (.int false 8))

def Register.valid : Register → Bool
  | .value primitive => primitive.valid
  | .aggregate owner cells => aggregateType owner && cells.valid owner
  | .bytes _ => true
  | .emptyBytes => true

def Register.hasType (value : Register) (type : Ty) : Bool :=
  decide (value.type = type) && value.valid

abbrev Env := Control.Env Register

def values (env : Env) : MemoryAir.Env := fun id =>
  match env id with | some (.value value) => some value | _ => none

inductive Ref where
  | local (id : Nat)
  | constant (value : Register)
  deriving DecidableEq, Repr

def Ref.eval (ref : Ref) (env : Env) : Except Fault Register := do
  let value ← match ref with
    | .constant value => .ok value
    | .local id => match env id with | some value => .ok value | none => .error .malformed
  if value.valid then .ok value else .error .malformed

def Ref.value (ref : Ref) (env : Env) : Except Fault Value := do
  match ← ref.eval env with
  | .value value => .ok value
  | .emptyBytes => .error .unsupported
  | _ => .error .malformed

/-- A whole-object transfer requires the exact root declaration. It neither
reads undefined leaves as scalars nor manufactures padding bytes. -/
def load (state : State) (pointer : Value) : Except Fault Register := do
  let .pointer (.pointer _ _ child) address := pointer | .error .malformed
  if aggregateType child then
    let some layout := child.layout | .error .unsupported
    let cell ← access state address layout false
    if address.offset ≠ 0 ∨ cell.type ≠ child then .error .unsupported else
    if !cell.cells.valid child then .error .malformed else
    .ok (.aggregate child cell.cells)
  else return .value (← Memory.load state pointer)

def store (state : State) (pointer : Value) (value : Register) : Except Fault State := do
  match value with
  | .value value => Memory.store state pointer value
  | .emptyBytes => .error .unsupported
  | .bytes _ => .error .unsupported
  | .aggregate type cells =>
    let .pointer (.pointer writable _ child) address := pointer | .error .malformed
    if !writable then .error .readOnly else
    if child ≠ type ∨ !aggregateType type ∨ !cells.valid type then .error .malformed else
    let some layout := child.layout | .error .unsupported
    let cell ← access state address layout true
    if address.offset ≠ 0 ∨ cell.type ≠ child then .error .unsupported else
    .ok { state with heap := state.heap.replace address.allocation { cell with cells } }

/-- Retain the declared array bound in addition to the existing provenance,
alignment and element-extent checks. -/
def arrayElementPointer (state : State) (pointer : Value) (index : Nat) : Except Fault Value := do
  let .pointer (.pointer writable false owner@(.array length child)) address := pointer | .error .malformed
  if index ≥ length then .error .sourceBounds else
  let some layout := owner.layout | .error .unsupported
  let cell ← access state address layout false
  if !acceptsView cell.type address.offset owner then .error .unsupported else
  let base ← Memory.pointerCast state (.pointer writable true child) pointer
  Memory.elementPointer state base index

inductive Prim where
  | argument (index : Nat)
  /-- Retain an already typed register when captured metadata weakens only
  alignment. The decoder must check that the erased source/target types agree. -/
  | copy (value : Ref)
  /-- Primitive-only references are interpreted by the existing memory AIR.
  Aggregate registers cannot be consumed by these operations. -/
  | memory (operation : MemoryAir.Prim)
  | load (pointer : Ref)
  | store (pointer value : Ref)
  | fieldPointer (pointer : Ref) (offset : Nat)
  | arrayElementPointer (pointer index : Ref)
  | scalarByteArray (writable : Bool) (alignment count : Nat) (pointer : Ref)
  | arrayToSlice (pointer : Ref)
  | loadBytes (pointer : Ref)
  | bytesToWord (value : Ref)
  | booleanNot (value : Ref)
  | unreachable
  deriving DecidableEq, Repr

def Prim.transition (prim : Prim) (args : List Register) (env : Env) (state : State) :
    Except Fault (Register × State) := do
  match prim with
  | .argument index =>
    let some value := args[index]? | .error .malformed
    .ok (value, state)
  | .copy value => return (← value.eval env, state)
  | .memory operation =>
    let (value, after) ← operation.transition [] (values env) state
    .ok (.value value, after)
  | .load pointer => return (← AggregateAir.load state (← pointer.value env), state)
  | .store pointer value =>
    let after ← AggregateAir.store state (← pointer.value env) (← value.eval env)
    .ok (.value (.scalar .unit), after)
  | .fieldPointer pointer offset => return (.value (← Memory.fieldPointer state (← pointer.value env) offset), state)
  | .arrayElementPointer pointer index =>
    let .scalar (.int false 64 number) ← index.value env | .error .malformed
    return (.value (← AggregateAir.arrayElementPointer state (← pointer.value env) number.toNat), state)
  | .scalarByteArray writable alignment count pointer =>
    return (.value (← ScalarBytes.arrayCast state writable alignment count (← pointer.value env)), state)
  | .arrayToSlice pointer =>
    return (.value (← ScalarBytes.arrayToSlice (← pointer.value env)), state)
  | .loadBytes pointer =>
    let .pointer (.pointer _ false (.array count (.scalar (.int false 8)))) address ←
      pointer.value env | .error .malformed
    return (.bytes (← ByteRange.read state address count), state)
  | .bytesToWord value =>
    let .bytes bytes ← value.eval env | .error .malformed
    if bytes.length ≠ 8 then .error .malformed else
    let word := bytes.foldr (fun byte (rest : BitVec 64) => byte.zeroExtend 64 ||| (rest <<< 8)) 0
    return (.value (.scalar (.int false 64 word.toNat)), state)
  | .booleanNot value =>
    let .scalar (.bool flag) ← value.value env | .error .malformed
    return (.value (.scalar (.bool (!flag))), state)
  | .unreachable => .error (.scalar .illegalBehavior)

def Prim.eval (prim : Prim) (args : List Register) (env : Env) (state : State) : Except Fault Register × State :=
  match prim.transition args env state with
  | .ok (value, after) => (.ok value, after)
  | .error fault => (.error fault, state)

def semantics : Control.Semantics Ty Prim Ref Register Fault State where
  hasType := Register.hasType
  truth := fun value => match value with | .value (.scalar (.bool flag)) => some flag | _ => none
  evalRef := Ref.eval
  evalPrim := Prim.eval
  malformed := .malformed

abbrev Code := Control.Code Ty Prim Ref

structure Program where
  parameters : List Ty
  returnType : Ty
  body : Code
  deriving DecidableEq, Repr

def Program.finish (returnType : Ty) (mark : Nat) : Control.Outcome Register Fault State → Except Fault Register × State
  | .returned value after =>
    (if value.hasType returnType then .ok value else .error .malformed, cleanup mark after)
  | .fault reason after => (.error reason, cleanup mark after)
  | .jumped _ _ _ after => (.error .malformed, cleanup mark after)

def Program.run (program : Program) (args : List Register) (state : State) : Except Fault Register × State :=
  if state.valid && args.length = program.parameters.length &&
      (args.zip program.parameters).all (fun (value, type) => value.hasType type) then
    Program.finish program.returnType state.nextId (program.body.eval semantics args (fun _ => none) state)
  else (.error .malformed, state)

end Compiler.ZigAir.AggregateAir
