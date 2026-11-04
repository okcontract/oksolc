/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ArgumentMemory
import Compiler.ZigAir.MemoryWordAllocation

namespace Compiler.Extraction.Memory.Arguments.Allocation
open Compiler.Algebraic Compiler.Extraction.Storage

inductive Fault where
  | memory (fault : Compiler.ZigAir.Memory.Fault)
  | registry (fault : Memory.Fault)
  deriving DecidableEq, Repr

/-- Reserve persistent storage and register its allocator and extent. The
payload is provisional and must remain unobserved until copy initializes it.
Ordinary allocation failure is `ok none`. A registry collision retains the
already accepted typed allocation and reached private effects; no cleanup or
rollback is invented. Allocator brands are logical identities, not native
`Allocator.ptr` values (that field may be undefined for stateless allocators).
This is a checked external contract, not captured allocator AIR. -/
def reserve (heap : Heap) (state : Compiler.ZigAir.Memory.State) (allocator : Nat)
    (items : List NodeId) (request : Compiler.ZigAir.Memory.WordAllocation.Allocator σ) (effects : σ) :
    (Except Fault (Option ArgumentSlice) × Heap × Compiler.ZigAir.Memory.State) × σ :=
  let ((result, after), reached) := Compiler.ZigAir.Memory.WordAllocation.reserve state items.length request effects
  match result with
  | .error fault => ((.error (.memory fault), heap, after), reached)
  | .ok none => ((.ok none, heap, after), reached)
  | .ok (some target) =>
    if items.isEmpty then ((.ok (some ⟨target.allocation, items⟩), heap, after), reached) else
    match Memory.allocate heap allocator target.allocation (.arguments items) true with
    | .error fault => ((.error (.registry fault), heap, after), reached)
    | .ok registered => ((.ok (some ⟨target.allocation, items⟩), registered, after), reached)

end Compiler.Extraction.Memory.Arguments.Allocation
