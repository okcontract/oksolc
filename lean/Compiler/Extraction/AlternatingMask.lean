/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.AssociativeProofs

namespace Compiler.Extraction.AlternatingMask
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.Extraction.Interner Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
set_option linter.unusedSimpArgs false

structure Choice where
  constantFirst : Bool
  innerSecond : Bool
  outerSecond : Bool
  deriving DecidableEq, Repr

def pick (second : Bool) (left right : α) : α := if second then right else left

/-- Keep the original queried slices and selected indices until their actual
initializer reads. Logical IDs annotate those reads; native execution must load
the retained allocations, including after earlier constructors have returned. -/
structure Capture where
  expression : NodeId
  otherExpression : NodeId
  outerMaskId : NodeId
  innerMask : Word
  outerMask : Word
  inner : ArgumentSlice
  alternatives : ArgumentSlice
  expressionIndex : Nat
  otherIndex : Nat
  deriving DecidableEq

def inputValue (choice : Choice) (x innerMask y outerMask : Word) : Word :=
  let inner := if choice.constantFirst then innerMask &&& x else x &&& innerMask
  let alternatives := if choice.innerSecond then y ||| inner else inner ||| y
  if choice.outerSecond then outerMask &&& alternatives else alternatives &&& outerMask

def outputValue (x innerMask y outerMask : Word) : Word :=
  (x &&& (innerMask &&& outerMask)) ||| (y &&& outerMask)

private theorem and_left_comm (a b c : Word) : a &&& (b &&& c) = b &&& (a &&& c) := by
  rw [← BitVec.and_assoc, BitVec.and_comm a b, BitVec.and_assoc]

theorem distribution (choice : Choice) (x innerMask y outerMask : Word) :
    inputValue choice x innerMask y outerMask = outputValue x innerMask y outerMask := by
  rcases choice with ⟨constantFirst, innerSecond, outerSecond⟩
  cases constantFirst <;> cases innerSecond <;> cases outerSecond <;>
    simp [inputValue, outputValue, BitVec.and_or_distrib_right, BitVec.and_or_distrib_left,
      BitVec.and_assoc, BitVec.and_comm, and_left_comm, BitVec.or_comm]

end Compiler.Extraction.AlternatingMask
