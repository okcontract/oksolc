/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.StorageOperations

/-! Typed allocation identities for the expression graph. An identity denotes
an allocation lifetime, not a raw numerical pointer. Item and slice payloads
reuse the storage projection. Allocator pairing, allocation failure, relocation,
invalid reads and empty slices are explicit. Byte layout, alignment, allocator
implementations and the injection into machine addresses remain primitive
refinement obligations; this is not a semantics for arbitrary Zig pointers. -/
namespace Compiler.Extraction.Memory
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage

inductive Block where
  | item (value : Item)
  | arguments (values : List NodeId)
  | representatives (cells : List Cell)
  /-- Owned verbatim extent. Destruction does not inspect byte contents. -/
  | bytes (length : Nat)

structure Allocation where
  allocator : Nat
  block : Block

abbrev Heap := Nat → Option Allocation

inductive Fault where
  | outOfMemory | notFresh | unallocated | wrongAllocator | wrongType | bounds
  deriving DecidableEq, Repr

def write (heap : Heap) (address : Nat) (value : Option Allocation) : Heap :=
  fun query => if query = address then value else heap query

def allocate (heap : Heap) (allocator address : Nat) (block : Block) (succeeds : Bool) : Except Fault Heap :=
  if !succeeds then .error .outOfMemory else
  match heap address with
  | none => .ok (write heap address (some ⟨allocator, block⟩))
  | some _ => .error .notFresh

def release (heap : Heap) (allocator address : Nat) : Except Fault Heap :=
  match heap address with
  | none => .error .unallocated
  | some allocation =>
    if allocation.allocator = allocator then .ok (write heap address none)
    else .error .wrongAllocator

/-- Zero-sized allocation/free in Zig does not access backing memory. Its
sentinel pointer need not identify a live allocation. -/
def releaseSlice (heap : Heap) (allocator : Nat) (slice : ArgumentSlice) : Except Fault Heap :=
  if slice.items.isEmpty then .ok heap else release heap allocator slice.address

def readArgument (heap : Heap) (slice : ArgumentSlice) (index : Nat) : Except Fault NodeId :=
  if index < slice.items.length then
    match heap slice.address with
    | none => .error .unallocated
    | some allocation => match allocation.block with
      | .arguments values => match values[index]? with
        | none => .error .bounds
        | some value => .ok value
      | _ => .error .wrongType
  else .error .bounds

def readRepresentative (heap : Heap) (address index : Nat) : Except Fault Cell :=
  match heap address with
  | none => .error .unallocated
  | some allocation => match allocation.block with
    | .representatives cells => match cells[index]? with
      | none => .error .bounds
      | some cell => .ok cell
    | _ => .error .wrongType

def SliceValid (allocator : Nat) (heap : Heap) (slice : ArgumentSlice) : Prop :=
  slice.items = [] ∨ heap slice.address = some ⟨allocator, .arguments slice.items⟩

def Resident (allocator : Nat) (heap : Heap) (cell : Cell) : Prop :=
  heap cell.itemAddress = some ⟨allocator, .item cell.item⟩ ∧
    SliceValid allocator heap cell.argumentSlice

def GraphResident (allocator : Nat) (heap : Heap) (cells : List Cell) : Prop :=
  ∀ cell ∈ cells, Resident allocator heap cell

def Vector (allocator : Nat) (heap : Heap) (address : Nat) (cells : List Cell) : Prop :=
  heap address = some ⟨allocator, .representatives cells⟩

/-- Models the relevant ArrayList growth outcomes: in-place success, fresh
allocation/copy/free, or allocation failure before touching the old buffer.
The copied vector contains descriptors; it does not move their pointees. -/
def moveVector (heap : Heap) (allocator oldAddress newAddress : Nat) (succeeds : Bool) : Except Fault Heap :=
  match heap oldAddress with
  | none => .error .unallocated
  | some allocation =>
    if allocation.allocator = allocator then
      match allocation.block with
      | .representatives cells =>
        if !succeeds then .error .outOfMemory else
        if newAddress = oldAddress then .ok heap else do
          let allocated ← allocate heap allocator newAddress (.representatives cells) true
          release allocated allocator oldAddress
      | _ => .error .wrongType
    else .error .wrongAllocator

end Compiler.Extraction.Memory
