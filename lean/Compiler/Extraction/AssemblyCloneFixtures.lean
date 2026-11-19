/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.AssemblyClone

namespace Compiler.Extraction.AssemblyClone.Fixtures
open Compiler.Algebraic

inductive Error where
  | outOfMemory
  deriving DecidableEq, Repr

/-- A test allocator with append-only live slots. Matching frees use its LIFO
contract. This is an executable witness, not the native allocator model. -/
abbrev Heap := List (List (BitVec 8))

def duplicate (succeeds : Bool) (source : Bytes) : Effect Heap Error Bytes := fun before =>
  if source.contents.isEmpty then (.ok source, before)
  else if succeeds then (.ok ⟨before.length, source.contents, 0⟩, before ++ [source.contents])
  else (.error .outOfMemory, before)

def free (bytes : Bytes) (heap : Heap) : Heap :=
  if bytes.contents.isEmpty then heap else heap.take bytes.address

def Frame (before after : Heap) : Prop := ∀ index, index < before.length → after[index]? = before[index]?

def Owns (source copied : Bytes) (before after : Heap) : Prop :=
  if source.contents.isEmpty then after = before
  else copied.address = before.length ∧ after = before ++ [source.contents]

def original : Value (List Nat) := {
  item := ⟨13, none, 42⟩, metadata := [11, 22, 33],
  verbatim := some ⟨2, 1, ⟨0, [1, 2, 3], 0⟩⟩
}
def initial : Heap := [[1, 2, 3], [99]]
def copied : Value (List Nat) := { original with verbatim := some ⟨2, 1, ⟨2, [1, 2, 3], 0⟩⟩ }
def allocated : Heap := [[1, 2, 3], [99], [1, 2, 3]]
def plain : Value (List Nat) := { original with item := ⟨2, none, 7⟩, verbatim := none }
def empty : Value (List Nat) := { original with verbatim := some ⟨2, 1, ⟨0, [], 0⟩⟩ }

end Compiler.Extraction.AssemblyClone.Fixtures
