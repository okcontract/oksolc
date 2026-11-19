/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InsertionSortProofs
import Compiler.Extraction.ScopedRecursiveSemantics

namespace Compiler.Extraction.InsertionSort
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul

/-- Retain the caller's explicit allocation/release outcomes and replace only
the former sort oracle with the extracted, terminating insertion program. -/
def resources (r : Scoped.Resources) : Scoped.Resources := { r with sort := sortIds }

theorem normalize_word (other : Meaning) (item : Item) (before after : List NodeId)
    (read : Read) (sequence : BitVec 32)
    (normalized : normalizeCode.run sortIds item before = some after) :
    item.eval (Folding.wordMeaning other) read after sequence =
      item.eval (Folding.wordMeaning other) read before sequence :=
  Cache.normalize_word other sortIds sortIds_perm item before after read sequence normalized

/-- No sort-permutation or recursive-correctness premise. Native execution and
the graph insertion/publication contracts remain separate obligations. -/
theorem unfold_safe (env : AddressMask.Environment) (other : Meaning) (pushes : Pushes other)
    (r : Scoped.Resources) (p : Primitives)
    (primitive : Scoped.GraphContracts (Dispatch.wordDispatchMeaning env other) p)
    (usizeBits depth : Nat) :
    Recursive.FindSound (Dispatch.wordDispatchMeaning env other)
      (ScopedRecursive.unfold (resources r) p representativeReads usizeBits depth) :=
  ScopedRecursive.unfold_representatives_safe env other pushes (resources r) sortIds_perm
    p primitive usizeBits depth

/-- Word semantics, graph extension and local ownership for the same recursive
execution, now with an executable sort and its proved permutation law. -/
theorem detailed_verified (env : AddressMask.Environment) (other : Meaning) (pushes : Pushes other)
    (r : Scoped.Resources) (p : Primitives)
    (primitive : Scoped.GraphContracts (Dispatch.wordDispatchMeaning env other) p)
    (frames : Recursive.PrimitiveFrames p) (usizeBits depth : Nat) (request : Request) (before : Heap) (value : Word)
    (valid : Invariant (Dispatch.wordDispatchMeaning env other) before)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.read
      request.arguments request.sequence = some value) :
    let (result, after) := ScopedRecursive.detailed (resources r) p
      representativeReads usizeBits depth request before
    Invariant (Dispatch.wordDispatchMeaning env other) after.heap ∧ Stable before after.heap ∧
      Extends before after.heap ∧ Scoped.Closed after.scope ∧
      match result with | .error _ => True | .ok id => after.heap.read id = some value :=
  ScopedRecursive.detailed_verified env other pushes (resources r) sortIds_perm p primitive
    frames usizeBits depth request before value valid evaluated

end Compiler.Extraction.InsertionSort
