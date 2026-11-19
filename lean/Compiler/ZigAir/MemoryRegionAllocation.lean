/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryAllocationShape

namespace Compiler.ZigAir.Memory.RegionAllocation

/-- An external allocator receives the complete byte request and alignment.
None is ordinary OOM; private effects are retained on every response. -/
abbrev Allocator (σ : Type) := Nat → Nat → σ → Option Nat × σ

def cell (type : Ty) (base : Nat) : Allocation := ⟨base, type, [], true, false⟩

/-- Introduce one persistent lifetime for the returned region. Reusing a freed
address never reuses its lifetime or lowers the address high-water mark. -/
def extend (state : State) (type : Ty) (bytes base : Nat) : State :=
  ⟨(state.nextId, cell type base) :: state.heap, state.nextId + 1,
    max state.nextAddress (base + bytes)⟩

structure Fits (state : State) (layout : Layout) (base : Nat) : Prop where
  positive : 0 < base
  aligned : base % layout.alignment = 0
  bounded : base + layout.bytes ≤ addressLimit
  separate : ∀ entry ∈ state.heap, ∀ old, entry.2.type.layout = some old →
    base + layout.bytes ≤ entry.2.base ∨ entry.2.base + old.bytes ≤ base

/-- Validate the complete immutable type and returned region before publication.
Empty requests create no allocation. A byte-count overflow is ordinary OOM;
unsupported metadata or a corrupt returned region is a verification rejection.
The rejection retains the external response's actual private effects. -/
def reserve (state : State) (type : Ty) (allocate : Allocator σ) (effects : σ) :
    (Except Fault (Option Address) × State) × σ :=
  match type.layout with
  | none => ((.error .unsupported, state), effects)
  | some layout =>
    if layout.bytes = 0 then ((.ok (some ⟨state.nextId, 0⟩), state), effects) else
    if !state.valid then ((.error .malformed, state), effects) else
    if layout.bytes ≥ addressLimit then ((.ok none, state), effects) else
    let (response, reached) := allocate layout.bytes layout.alignment effects
    match response with
    | none => ((.ok none, state), reached)
    | some base =>
      let after := extend state type layout.bytes base
      if after.valid then ((.ok (some ⟨state.nextId, 0⟩), after), reached)
      else ((.error .memoryValidity, state), reached)

end Compiler.ZigAir.Memory.RegionAllocation
