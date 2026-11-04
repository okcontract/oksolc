/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.NestedConstructionProofs

namespace Compiler.Extraction.Associative
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Contract.Yul

/-- The independent algebraic restriction of reassociation. -/
def Supported (op : Folding.Op) : Prop :=
  op = .add ∨ op = .mul ∨ op = .and ∨ op = .or ∨ op = .xor

theorem supported_arity (op : Folding.Op) (supported : Supported op) : op.arity = 2 := by
  rcases supported with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem commutative (op : Folding.Op) (supported : Supported op) (a b : Word) :
    op.value a b 0 = op.value b a 0 := by
  rcases supported with rfl | rfl | rfl | rfl | rfl
  · exact BitVec.add_comm a b
  · exact BitVec.mul_comm a b
  · exact BitVec.and_comm a b
  · exact BitVec.or_comm a b
  · exact BitVec.xor_comm a b

theorem associative (op : Folding.Op) (supported : Supported op) (a b c : Word) :
    op.value (op.value a b 0) c 0 = op.value a (op.value b c 0) 0 := by
  rcases supported with rfl | rfl | rfl | rfl | rfl
  · exact BitVec.add_assoc a b c
  · exact BitVec.mul_assoc a b c
  · exact BitVec.and_assoc a b c
  · exact BitVec.or_assoc a b c
  · exact BitVec.xor_assoc a b c

structure Constructors (Debug : Type) (m : Type → Type := Action) where
  operation : OperationBuilder Debug m
  constant : Word → Debug → m NodeId
  materialize : NodeId → Word → Debug → m NodeId
  /-- Native rules also forward complete graph-owned arrays. Their storage
  identity is retained separately from temporary address-taken operands. Logical
  fixtures can erase this distinction; physical callers must consume it. -/
  borrowedOperation : Nat → OperationBuilder Debug m := fun _ => operation
  /-- The named-local route carries the graph view and exact overwrite choice.
  Native constructors perform the source copy before entering the callee. -/
  localOperation : LocalOperationBuilder Debug m := localBuilder operation

structure ConstructorSound (other : Meaning) (constructors : Constructors Debug) : Prop where
  operation : Constructs other constructors.operation
  constant : ∀ value debug before, Invariant (Folding.wordMeaning other) before →
    Safe (Folding.wordMeaning other) (constructors.constant value debug) before
      (fun id after => after.read id = some value)
  materialize : ∀ original value debug before, Invariant (Folding.wordMeaning other) before →
    Safe (Folding.wordMeaning other) (constructors.materialize original value debug) before
      (fun id after => after.read id = some value)
  borrowedOperation : ∀ address, Constructs other (constructors.borrowedOperation address)
  localOperation : LocalConstructs other constructors.localOperation

/-- Only the Push atom law is needed in addition to the independent word model.
It has a concrete model, e.g. Interner.constructorMeaning. -/
def Pushes (other : Meaning) : Prop := ∀ value, other.atom 2 value 0 [] = some value

def internerConstant (p : Primitives) : Word → Debug → Action NodeId := fun value _ =>
  findCode.run p (constructorCode.constantRequest value)

theorem interner_constant_safe (other : Meaning) (pushes : Pushes other) (p : Primitives)
    (contracts : Contracts (Folding.wordMeaning other) p) (value : Word) (debug : Debug)
    (before : Heap) (valid : Invariant (Folding.wordMeaning other) before) :
    Safe (Folding.wordMeaning other) (internerConstant p value debug) before
      (fun id after => after.read id = some value) := by
  apply find_safe _ p contracts _ before value valid
  simpa [constructorCode, ConstructorCode.constantRequest, Scalar.run, Item.eval,
    readArguments, Folding.wordMeaning] using pushes value

theorem constructor_meaning_pushes (other : Meaning) : Pushes (constructorMeaning other) := by
  intro value; rfl

end Compiler.Extraction.Associative
