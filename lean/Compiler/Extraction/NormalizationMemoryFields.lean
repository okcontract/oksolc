/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationMemory

namespace Compiler.Extraction.Memory.Arguments
open Compiler.Algebraic Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray

/-- Successful reservation retains the requested descriptor. This says nothing
about initialized payload bytes, ownership, or validity of the reached memory. -/
theorem Allocation.reserve_items (heap : Heap) (state : Compiler.ZigAir.Memory.State) (allocator : Nat)
    (items : List NodeId) (request : Compiler.ZigAir.Memory.WordAllocation.Allocator σ) (effects : σ)
    (slice : ArgumentSlice)
    (returned : (Allocation.reserve heap state allocator items request effects).1.1 = .ok (some slice)) :
    slice.items = items := by
  unfold Allocation.reserve at returned
  cases ran : Compiler.ZigAir.Memory.WordAllocation.reserve state items.length request effects with
  | mk pair reached =>
    rcases pair with ⟨result, after⟩
    simp only [ran] at returned
    cases result with
    | error fault => cases returned
    | ok target =>
      cases target with
      | none => cases returned
      | some target =>
        dsimp only at returned
        split at returned
        · cases returned; rfl
        · cases registered : Memory.allocate heap allocator target.allocation (.arguments items) true with
          | error fault => simp only [registered] at returned; cases returned
          | ok registered => simp only [registered] at returned; cases returned; rfl

theorem Duplication.run_items (heap : Heap) (state : Compiler.ZigAir.Memory.State) (allocator : Nat)
    (source : View) (items : List NodeId) (request : Compiler.ZigAir.Memory.WordAllocation.Allocator σ)
    (effects : σ) (slice : ArgumentSlice)
    (returned : (Duplication.run heap state allocator source items request effects).1.1 = .ok (some slice)) :
    slice.items = items := by
  unfold Duplication.run at returned
  split at returned
  · cases returned
  · cases ran : Allocation.reserve heap state allocator items request effects with
    | mk result reached =>
      rcases result with ⟨result, registered, allocated⟩
      simp only [ran] at returned
      cases result with
      | error fault => cases returned
      | ok destination =>
        cases destination with
        | none => cases returned
        | some destination =>
          have fields := Allocation.reserve_items heap state allocator items request effects destination (by rw [ran])
          cases copied : Compiler.ZigAir.Memory.WordCopy.copy allocated source (view destination) with
          | mk result after =>
            simp only [copied] at returned
            cases result with
            | error fault => cases returned
            | ok done => cases done; cases returned; exact fields

namespace Normalization

/-- Borrowed take obtains its descriptor from the actual reserve/copy outcome.
Typed copy, ownership and source representation remain separate contracts. -/
theorem takeOwned_borrowed_items (code : Compiler.Extraction.Cache.NormalizationOwnership.Code) (external : External σ)
    (allocator : Nat) (handle : Handle) (before : Session σ) (slice : ArgumentSlice) (remaining : Handle)
    (borrowed : handle.owned = none)
    (returned : (takeOwned code external allocator handle before).1 = .ok (slice, remaining)) :
    slice.items = handle.values := by
  simp only [takeOwned, borrowed] at returned
  cases ran : Duplication.run before.heap before.memory allocator handle.items handle.values
      (external.allocate .duplicate before) before.effects with
  | mk result reached =>
    rcases result with ⟨result, heap, memory⟩
    simp only [ran] at returned
    cases result with
    | error fault => cases returned
    | ok destination =>
      cases destination with
      | none => cases returned
      | some destination =>
        have fields := Duplication.run_items before.heap before.memory allocator handle.items handle.values
          (external.allocate .duplicate before) before.effects destination (by rw [ran])
        cases returned
        exact fields

end Normalization
end Compiler.Extraction.Memory.Arguments
