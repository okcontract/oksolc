/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.Graph
import Compiler.Algebraic.Rules

/-! Value semantics of the interner key and normalization boundary. Slice
arguments denote contents, not addresses. A missing instruction on an Operation
is an invalid borrow/optional unwrap, represented by `none`, never a valid key.
Allocation and sort implementations remain explicit primitive contracts. -/
namespace Compiler.Extraction.Cache
open Compiler.Algebraic Contract.Yul

abbrev Kind := BitVec 32
abbrev Opcode := BitVec 8
abbrev Read := NodeId → Option Word

structure Item where
  kind : Kind
  instruction : Option Opcode
  data : Word
  deriving DecidableEq, Repr

structure Key where
  kind : Kind
  instruction : Opcode
  data : Word
  arguments : List NodeId
  sequence : BitVec 32
  deriving DecidableEq, Repr

inductive Test where
  | operation | notOperation
  deriving DecidableEq

def Test.run (test : Test) (item : Item) : Bool :=
  match test with
  | .operation => item.kind == 1
  | .notOperation => item.kind != 1

inductive Scalar (α : Type) where
  | input | literal (value : α)

def Scalar.run (code : Scalar α) (value : α) : α :=
  match code with
  | .input => value
  | .literal value => value

structure KeyCode where
  kind : Scalar Kind
  instructionTest : Test
  dataTest : Test
  operationData : Scalar Word
  otherData : Scalar Word
  sequence : Scalar (BitVec 32)

def KeyCode.run (code : KeyCode) (item : Item) (arguments : List NodeId) (sequence : BitVec 32) : Option Key := do
  let opcode ← if code.instructionTest.run item then item.instruction else some 0
  pure ⟨code.kind.run item.kind, opcode,
    (if code.dataTest.run item then code.operationData else code.otherData).run item.data,
    arguments, code.sequence.run sequence⟩

inductive Field where
  | kind | instruction | data | arguments | sequence
  deriving DecidableEq, Repr

def Field.equal (field : Field) (a b : Key) : Bool :=
  match field with
  | .kind => a.kind == b.kind
  | .instruction => a.instruction == b.instruction
  | .data => a.data == b.data
  | .arguments => a.arguments == b.arguments
  | .sequence => a.sequence == b.sequence

def equal (fields : List Field) (a b : Key) : Bool := fields.all (fun field => field.equal a b)

structure NormalizeCode where
  commutative : List Opcode
  guard : Test
  threshold : Nat

def NormalizeCode.run (code : NormalizeCode) (sort : List NodeId → List NodeId)
    (item : Item) (arguments : List NodeId) : Option (List NodeId) := do
  let commutative ← if code.guard.run item then do
    let opcode ← item.instruction
    pure (code.commutative.contains opcode)
    else pure false
  pure (if commutative && decide (code.threshold ≤ arguments.length) then sort arguments else arguments)

/-- Interpretation of instruction/context epochs is separate from key encoding.
This theorem boundary must not equate different storage/memory versions. -/
structure Meaning where
  operation : Opcode → BitVec 32 → List Word → Option Word
  atom : Kind → Word → BitVec 32 → List Word → Option Word

def readArguments (read : Read) : List NodeId → Option (List Word)
  | [] => some []
  | id :: rest => do
    let value ← read id
    let values ← readArguments read rest
    pure (value :: values)

def Item.eval (meaning : Meaning) (read : Read) (item : Item)
    (arguments : List NodeId) (sequence : BitVec 32) : Option Word := do
  let values ← readArguments read arguments
  if item.kind = 1 then do
    let opcode ← item.instruction
    meaning.operation opcode sequence values
  else meaning.atom item.kind item.data sequence values

def Key.eval (meaning : Meaning) (read : Read) (key : Key) : Option Word := do
  let values ← readArguments read key.arguments
  if key.kind = 1 then meaning.operation key.instruction key.sequence values
  else meaning.atom key.kind key.data key.sequence values

abbrev Table := Key → Option NodeId

/-- Every cached ID exists and has the denotation of its key. This includes
argument validity; an absent denotation cannot establish an equivalence. -/
def Valid (meaning : Meaning) (read : Read) (table : Table) : Prop :=
  ∀ key id, table key = some id → ∃ value, key.eval meaning read = some value ∧ read id = some value

def put (fields : List Field) (table : Table) (key : Key) (id : NodeId) : Table :=
  fun query => if equal fields query key then some id else table query

end Compiler.Extraction.Cache
