/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeParentRelease

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Native transfer appends the existing private owner and leaves keys unchanged.
Storage may move; the frame retains the original native and registry entries
outside that storage. Empty backing sentinels remain unrestricted. -/
structure TransferredFrame (safety : Bool) (allocator owner : Nat)
    (oldData : Compiler.ZigAir.Memory.Address) (oldCapacity : Nat) (rows : List Storage.Cell)
    (owned : ArgumentSlice) (row : Storage.Cell)
    (before after : World (Publication.Effects σ)) : Prop where
  native : ∃ data capacity, NativeGraph.Facts safety allocator owner data capacity after (rows ++ [row])
  keys : after.memory.effects.keys = before.memory.effects.keys
  arguments : row.argumentsAddress = owned.address
  memory : ∀ id cell, before.memory.memory.heap.lookup id = some cell → id ≠ owner →
    (oldCapacity ≠ 0 → id ≠ oldData.allocation) → after.memory.memory.heap.lookup id = some cell
  registry : ∀ id block, before.memory.heap id = some block →
    (oldCapacity ≠ 0 → id ≠ oldData.allocation) → after.memory.heap id = some block

/-- Completion of the actual native transfer, including reached storage for
parent framing. This predicate is a conclusion, never a source observation. -/
def TransferredReturn (safety : Bool) (allocator owner : Nat) (rows : List Storage.Cell)
    (owned : ArgumentSlice) (before : World (Publication.Effects σ))
    (actual : Except Fault NodeId × World (Publication.Effects σ)) : Prop :=
  actual.1 = .ok (Storage.idFor (before.graph.representatives.getD [])) ∧
    ∃ added data capacity row,
      NativeGraph.Facts safety allocator owner data capacity before (rows ++ added) ∧
      TransferredFrame safety allocator owner data capacity (rows ++ added) owned row before actual.2

/-- Transfer shares storage framing with cleanup and rollback. The child's
original normalization freshness separates the new row from each live parent;
no fresh duplicate or publication is assumed. -/
theorem TransferredFrame.parent
    {safety : Bool} {allocator owner oldCapacity : Nat} {oldData : Compiler.ZigAir.Memory.Address}
    {rows parentRows : List Storage.Cell} {source : View} {values : List NodeId}
    {normalized : ArgumentSlice} {address : Compiler.ZigAir.Memory.Address}
    {native : AssemblyClone.NativeFields.ItemValue} {outer : World (Publication.Effects σ) → Prop}
    {original before after : World (Publication.Effects σ)}
    {childSource : View} {request : Interner.Request} {childValues : List NodeId}
    {taken : State (Publication.Effects σ)} {owned : ArgumentSlice} {lookup : Handle} {row : Storage.Cell}
    (origin : Caller.Origin allocator childSource request childValues original taken owned lookup)
    (initial : CallFrame safety allocator owner parentRows source values normalized address native outer original)
    (reached : CallFrame safety allocator owner parentRows source values normalized address native outer before)
    (facts : NativeGraph.Facts safety allocator owner oldData oldCapacity before rows)
    (post : TransferredFrame safety allocator owner oldData oldCapacity rows owned row before after)
    (outerKept : outer after) :
    CallFrame safety allocator owner parentRows source values normalized address native outer after := by
  exact CallFrame.storage_frame_rows origin initial reached facts [row]
    (by intro logical member _; exact List.mem_singleton.mp member ▸ post.arguments)
    post.native post.keys (fun id cell found apart storage _ => post.memory id cell found apart storage)
    (fun id block found _ storage _ => post.registry id block found storage) outerKept

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
