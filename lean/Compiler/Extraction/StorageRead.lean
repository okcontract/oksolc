/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.StorageIR
import Compiler.Extraction.CacheIR

namespace Compiler.Extraction.Storage
open Compiler.Algebraic Contract.Yul

/-- The same item representation used by the interner, with the representative's
owned argument slice and observation sequence. `otherValue` requires a separate
denotation invariant; it is never read as a constant. Physical borrow validity
is separate from this value projection. -/
structure Cell where
  item : Cache.Item
  otherValue : Word
  itemAddress : Nat
  arguments : List NodeId := []
  sequence : BitVec 32 := 0
  argumentsAddress : Nat := 0

def Cell.isPush (cell : Cell) : Bool := cell.item.kind == 2
def Cell.dataValue (cell : Cell) : Word := cell.item.data

def Cell.value (cell : Cell) : Word := if cell.isPush then cell.dataValue else cell.otherValue

inductive Bound where
  | ge | gt
  deriving DecidableEq, Repr

def Bound.reject (id size : Nat) : Bound → Bool
  | .ge => decide (id ≥ size)
  | .gt => decide (id > size)

inductive Index where
  | requested
  | literal (index : Nat)
  deriving DecidableEq, Repr

def Index.eval (id : NodeId) : Index → Nat
  | .requested => id.toNat
  | .literal value => value

structure Lookup where
  bound : Bound
  index : Index
  deriving DecidableEq, Repr

inductive ReadError where
  | invalidId | safetyFault | invalidOptional
  deriving DecidableEq, Repr

/-- The safety-fault outcome is distinct from the native explicit error. An
incorrect bounds predicate cannot acquire a proof by mapping both to null. -/
def Lookup.run (program : Lookup) (cells : List Cell) (id : NodeId) : Except ReadError Cell :=
  if program.bound.reject id.toNat cells.length then .error .invalidId
  else match cells[program.index.eval id]? with
    | none => .error .safetyFault
    | some cell => .ok cell

structure ConstantRead where
  lookup : Lookup
  rejectOnPush : Bool
  deriving DecidableEq, Repr

def ConstantRead.run (program : ConstantRead) (cells : List Cell) (id : NodeId) :
    Except ReadError (Option Word) :=
  match program.lookup.run cells id with
  | .error .invalidId => .ok none
  | .error error => .error error
  | .ok cell => if cell.isPush == program.rejectOnPush then .ok none else .ok (some cell.dataValue)

def readValue (cells : List Cell) (id : NodeId) : Option Word :=
  cells[id.toNat]?.map Cell.value

/-- Slice descriptor copied by operationArguments; the backing allocation is
separate from the growable representative array. -/
structure ArgumentSlice where
  address : Nat
  items : List NodeId
  deriving DecidableEq, Repr

def Cell.argumentSlice (cell : Cell) : ArgumentSlice := ⟨cell.argumentsAddress, cell.arguments⟩

inductive ArgumentsSource where
  | stored | empty

def ArgumentsSource.run (source : ArgumentsSource) (cell : Cell) : ArgumentSlice :=
  match source with
  | .stored => cell.argumentSlice
  | .empty => ⟨0, []⟩

structure OperationRead where
  lookup : Lookup
  rejectOnOperation : Bool
  rejectOnEqualOpcode : Bool
  arguments : ArgumentsSource

def OperationRead.run (program : OperationRead) (cells : List Cell) (id : NodeId)
    (opcode : BitVec 8) : Except ReadError (Option ArgumentSlice) :=
  match program.lookup.run cells id with
  | .error .invalidId => .ok none
  | .error error => .error error
  | .ok cell =>
    if (cell.item.kind == 1) == program.rejectOnOperation then .ok none else
    match cell.item.instruction with
    | none => .error .invalidOptional
    | some instruction =>
      if (instruction == opcode) == program.rejectOnEqualOpcode then .ok none
      else .ok (some (program.arguments.run cell))

end Compiler.Extraction.Storage
