/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeReads
import Compiler.Extraction.InternerQueryTiming

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray

abbrev Constructors (σ : Type) := Associative.Constructors AssemblyItem.Fields.Values (GraphAction σ)

/-- The shared dispatcher retains the queried allocation and source index.
The logical annotation cannot supply a native value or conceal a failed read. -/
def operand : Nested.OperandRead (GraphAction σ) := fun source index _ =>
  ShiftInput.operand (view source) index

/-- Supply only the proper recursive children to the existing full dispatcher.
The source view, constructor-local item, insertion and publication remain the
original context's operations. Each call captures its own debug fields. -/
def context (base : PairInput.Context σ) (owner usizeBits : Nat) (children : Constructors σ)
    (debug : AssemblyItem.Fields.Values) : PairInput.Context σ :=
  { base with primitives := fun source address native =>
    { base.primitives source address native with
      simplify := fun key source before => Dispatch.simplifyWithInputs (NativeReads.reads owner before.memory.memory)
        children usizeBits key.instruction key.arguments debug operand source.address (NativeReads.query owner) before } }

/-- The recursive family uses the shared source dispatcher with actual native
loads. Neither an annotation nor the seed simplifier can replace that reader. -/
theorem dispatcher_inputs (base : PairInput.Context σ) (owner usizeBits : Nat) (children : Constructors σ)
    (debug : AssemblyItem.Fields.Values) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (native : AssemblyClone.NativeFields.ItemValue) (key : Key) (owned : ArgumentSlice) (before : World σ) :
    ((context base owner usizeBits children debug).primitives source address native).simplify key owned before =
      Dispatch.simplifyWithInputs (NativeReads.reads owner before.memory.memory) children usizeBits
        key.instruction key.arguments debug (fun slice index _ => ShiftInput.operand (view slice) index)
        owned.address (NativeReads.query owner) before := by
  unfold context
  try unfold operand
  with_reducible rfl

/-- Snapshot equivalence is derived from the shared body, independently of
proper-child simulation, graph correspondence or child success. -/
theorem dispatcher_snapshot (base : PairInput.Context σ) (owner usizeBits : Nat) (children : Constructors σ)
    (debug : AssemblyItem.Fields.Values) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (native : AssemblyClone.NativeFields.ItemValue) (key : Key) (owned : ArgumentSlice) (before : World σ) :
    ((context base owner usizeBits children debug).primitives source address native).simplify key owned before =
      (Dispatch.simplifyWithInputs (NativeReads.reads owner before.memory.memory) children usizeBits
        key.instruction key.arguments debug operand owned.address) before :=
  (Recursive.QueryTiming.simplify before (NativeReads.reads owner before.memory.memory)
    (NativeReads.query owner) (fun _ => rfl) children operand usizeBits key.instruction key.arguments debug owned.address).1

/-- One unfolding uses the already connected literal, constant/materializer
and caller-owned view entries. It adds no alternate caller or simplifier body. -/
def step (base : PairInput.Context σ) (owner usizeBits : Nat) (children : Constructors σ) : Constructors σ where
  constant := fun value debug => (ViewInput.constructors (context base owner usizeBits children debug)).constant value debug
  operation := fun opcode values debug => (ViewInput.constructors (context base owner usizeBits children debug)).operation opcode values debug
  materialize := fun id value debug => (ViewInput.constructors (context base owner usizeBits children debug)).materialize id value debug
  borrowedOperation := fun address opcode values debug =>
    (ViewInput.constructors (context base owner usizeBits children debug)).borrowedOperation address opcode values debug
  localOperation := fun opcode source selected repeated first debug =>
    (ViewInput.constructors (context base owner usizeBits children debug)).localOperation opcode source selected repeated first debug

/-- Exhaustion observes no constructor body and is not ordinary native OOM.
The enclosing existing caller retains its reached locals on this rejection. -/
def exhausted : Constructors σ where
  constant := fun _ _ before => (.error (.language .unsupported), before)
  operation := fun _ _ _ before => (.error (.language .unsupported), before)
  materialize := fun _ _ _ before => (.error (.language .unsupported), before)
  borrowedOperation := fun _ _ _ _ before => (.error (.language .unsupported), before)
  localOperation := fun _ _ _ _ _ _ before => (.error (.language .unsupported), before)

/-- Finite observations of the complete constructor recursion. All depths are
available; choosing a bound supplies no preservation or termination theorem.
Native query/guard and call-site input correspondence remain obligations of
the particular execution, including the named-local and indexed-read routes. -/
def unfold (base : PairInput.Context σ) (owner usizeBits : Nat) : Nat → Constructors σ
  | 0 => exhausted
  | depth + 1 => step base owner usizeBits (unfold base owner usizeBits depth)

attribute [local irreducible] Arguments.operation ConstructorItem.constant ConstructorItem.materialize

theorem operation_succ (base : PairInput.Context σ) (owner usizeBits depth : Nat) (opcode : Opcode)
    (values : List NodeId) (debug : AssemblyItem.Fields.Values) :
    (unfold base owner usizeBits (depth + 1)).operation opcode values debug =
      Arguments.operation base.external base.budget base.allocator
        (context base owner usizeBits (unfold base owner usizeBits depth) debug).primitives base.queries opcode values debug := by
  rfl

theorem borrowed_succ (base : PairInput.Context σ) (owner usizeBits depth : Nat) (slice : ArgumentSlice)
    (opcode : Opcode) (debug : AssemblyItem.Fields.Values) :
    (unfold base owner usizeBits (depth + 1)).borrowedOperation slice.address opcode slice.items debug =
      ViewInput.operation (context base owner usizeBits (unfold base owner usizeBits depth) debug) (view slice) opcode slice.items debug := by
  exact ViewInput.borrowed_forwards _ _ _ _

/-- The recursive entry forwards the admitted named local to native copying,
then to the complete lower constructor through its own recursive context. -/
theorem local_succ (base : PairInput.Context σ) (owner usizeBits depth : Nat) (source : ArgumentSlice)
    (left right : NodeId) (items : source.items = [left, right]) (opcode : Opcode) (selected : Nat)
    (repeated : NodeId) (first : Bool) (debug : AssemblyItem.Fields.Values) :
    (unfold base owner usizeBits (depth + 1)).localOperation opcode source selected repeated first debug =
      ViewInput.localOperation (context base owner usizeBits (unfold base owner usizeBits depth) debug)
        opcode (view source) left right repeated selected first debug :=
  ViewInput.local_forwarded _ _ _ _ items _ _ _ _ _

theorem constant_succ (base : PairInput.Context σ) (owner usizeBits depth : Nat) (value : Contract.Yul.Word)
    (debug : AssemblyItem.Fields.Values) (before : World σ) :
    (unfold base owner usizeBits (depth + 1)).constant value debug before =
      (let result := ConstructorItem.constant base.external base.budget base.allocator
         ((context base owner usizeBits (unfold base owner usizeBits depth) debug).primitives ⟨0, 0, 0⟩)
         base.queries value debug before
       (result.1, result.2.world)) := by
  rfl

theorem materialize_succ (base : PairInput.Context σ) (owner usizeBits depth : Nat) (id : NodeId)
    (value : Contract.Yul.Word) (debug : AssemblyItem.Fields.Values) :
    (unfold base owner usizeBits (depth + 1)).materialize id value debug =
      (unfold base owner usizeBits (depth + 1)).constant value debug := by
  exact PairInput.materialize_forwarded _ _ _ _

theorem exhausted_rejected (before : World σ) (opcode : Opcode) (values : List NodeId)
    (debug : AssemblyItem.Fields.Values) :
    exhausted.operation opcode values debug before = (.error (.language .unsupported), before) ∧
    ordinary (exhausted.operation opcode values debug before).1 = false := ⟨rfl, rfl⟩

theorem zero_entries (base : PairInput.Context σ) (owner usizeBits : Nat) (before : World σ)
    (value : Contract.Yul.Word) (id : NodeId) (address : Nat) (opcode : Opcode) (values : List NodeId)
    (debug : AssemblyItem.Fields.Values) :
    (unfold base owner usizeBits 0).constant value debug before = (.error (.language .unsupported), before) ∧
    (unfold base owner usizeBits 0).operation opcode values debug before = (.error (.language .unsupported), before) ∧
    (unfold base owner usizeBits 0).materialize id value debug before = (.error (.language .unsupported), before) ∧
    (unfold base owner usizeBits 0).borrowedOperation address opcode values debug before = (.error (.language .unsupported), before) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem zero_local (base : PairInput.Context σ) (owner usizeBits : Nat) (before : World σ)
    (opcode : Opcode) (source : ArgumentSlice) (selected : Nat) (repeated : NodeId)
    (first : Bool) (debug : AssemblyItem.Fields.Values) :
    (unfold base owner usizeBits 0).localOperation opcode source selected repeated first debug before =
      (.error (.language .unsupported), before) := rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
