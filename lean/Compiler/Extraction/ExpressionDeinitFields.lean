/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionFields
import Compiler.Extraction.NormalizationMemoryLifetime

namespace Compiler.Extraction.ExpressionDeinit.Native.Fields
open Compiler.ZigAir.Memory (Address)
open Compiler.Extraction.Memory.Arguments.Normalization

inductive Fault where
  | memory (reason : Compiler.ZigAir.Memory.Fault)
  | registry (reason : Memory.Fault)
  deriving DecidableEq, Repr

def item (memory : Compiler.ZigAir.Memory.State) (descriptor : Address) : Except Fault Address := do
  let value ← (Expression.readField memory false descriptor Expression.itemOffset).mapError Fault.memory
  let .pointer type address := value | .error (.memory .malformed)
  if type ≠ Expression.itemType then .error (.memory .malformed) else .ok address

/-- Free does not read argument elements. Recover the existing logical slice
only after checking the actual native offset and complete registered extent.
An empty free ignores the pointer's identity/offset and needs no registry entry. -/
def resolveArguments (heap : Memory.Heap) (address : Address) (length : Nat) : Except Memory.Fault Storage.ArgumentSlice := do
  if length = 0 then return ⟨address.allocation, []⟩
  if address.offset ≠ 0 then .error .bounds else
  let some allocation := heap address.allocation | .error .unallocated
  let .arguments values := allocation.block | .error .wrongType
  if length ≠ values.length then .error .bounds else .ok ⟨address.allocation, values⟩

def arguments (before : Session σ) (descriptor : Address) : Except Fault Storage.ArgumentSlice := do
  let value ← (Expression.readField before.memory false descriptor Expression.argumentsOffset).mapError Fault.memory
  let .slice type address length := value | .error (.memory .malformed)
  if type ≠ Expression.argumentsType then .error (.memory .malformed) else
  (resolveArguments before.heap address length).mapError Fault.registry

theorem resolve_empty (heap : Memory.Heap) (address : Address) :
    resolveArguments heap address 0 = .ok ⟨address.allocation, []⟩ := rfl

theorem resolve_interior (heap : Memory.Heap) (address : Address) (length : Nat)
    (nonempty : length ≠ 0) (interior : address.offset ≠ 0) :
    resolveArguments heap address length = .error .bounds := by
  simp only [resolveArguments, nonempty, ↓reduceIte, pure, Except.pure, bind, Except.bind]
  exact if_pos interior

theorem resolve_extent (heap : Memory.Heap) (address : Nat) (length allocator : Nat) (values : List Compiler.Algebraic.NodeId)
    (nonempty : length ≠ 0) (stored : heap address = some ⟨allocator, .arguments values⟩) (different : length ≠ values.length) :
    resolveArguments heap ⟨address, 0⟩ length = .error .bounds := by
  simp only [resolveArguments, nonempty, stored, ↓reduceIte, ne_self_iff_false, bind, Except.bind]
  exact if_pos different

theorem item_read (memory : Compiler.ZigAir.Memory.State) (descriptor address : Address)
    (read : Expression.readField memory false descriptor Expression.itemOffset = .ok (.pointer Expression.itemType address)) :
    item memory descriptor = .ok address := by
  simp only [item, read, Except.mapError, bind, Except.bind, ne_self_iff_false, ↓reduceIte]

theorem item_frame (before after : Compiler.ZigAir.Memory.State) (descriptor : Address)
    (same : after.heap.lookup descriptor.allocation = before.heap.lookup descriptor.allocation) :
    item after descriptor = item before descriptor := by
  simp only [item, Expression.readField_frame before after false descriptor Expression.itemOffset same]

theorem resolve_owned (heap : Memory.Heap) (allocator : Nat) (slice : Storage.ArgumentSlice)
    (live : Memory.SliceValid allocator heap slice) :
    resolveArguments heap ⟨slice.address, 0⟩ slice.items.length = .ok slice := by
  by_cases empty : slice.items = []
  · cases slice; simp_all [resolveArguments, pure, Except.pure]
  · simp [resolveArguments, List.length_eq_zero_iff, empty, live.resolve_left empty]

theorem arguments_read (before : Session σ) (descriptor : Address) (allocator : Nat) (slice : Storage.ArgumentSlice)
    (read : Expression.readField before.memory false descriptor Expression.argumentsOffset =
      .ok (.slice Expression.argumentsType ⟨slice.address, 0⟩ slice.items.length))
    (live : Memory.SliceValid allocator before.heap slice) :
    arguments before descriptor = .ok slice := by
  simp only [arguments, read, Except.mapError, bind, Except.bind, ne_self_iff_false, ↓reduceIte,
    resolve_owned before.heap allocator slice live]

end Compiler.Extraction.ExpressionDeinit.Native.Fields
