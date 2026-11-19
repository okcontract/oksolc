/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryWordArray
import Compiler.ZigAir.MemoryRegionAllocation

/-! Checked external allocation contract for persistent u32 storage. The
external operation chooses an abstract region or ordinary allocation failure,
and retains its private effects. Native allocator framing, pointer injection
and the correspondence of those effects remain external refinement obligations.
This does not invoke or relabel the AIR stack-allocation primitive. -/
namespace Compiler.ZigAir.Memory.WordAllocation
open WordArray

abbrev Allocator (σ : Type) := Nat → σ → Option Nat × σ

def cell (length base : Nat) : Allocation := RegionAllocation.cell (.array length word) base

/-- The address counter remains a high-water mark; a region below it can be
reused once its prior lifetime has ended. Lifetime IDs are never reused. -/
def extend (state : State) (length base : Nat) : State :=
  RegionAllocation.extend state (.array length word) (length * 4) base

/-- The external request is for nonzero byte length with alignment four.
None denotes ordinary OOM. Invalid responses are semantic verification faults,
not OOM; their reached private effects are retained, but no unchecked typed
allocation is published. This makes no native rollback claim after a violated
allocator contract. Empty sentinels have no live allocation or registry entry. -/
def reserve (state : State) (length : Nat) (allocate : Allocator σ) (effects : σ) :
    (Except Fault (Option View) × State) × σ :=
  if length = 0 then ((.ok (some ⟨state.nextId, 0, 0⟩), state), effects) else
  if length ≥ addressLimit then ((.error .malformed, state), effects) else
  let ((result, after), reached) := RegionAllocation.reserve state (.array length word)
    (fun bytes _ => allocate bytes) effects
  ((result.map (Option.map fun address => ⟨address.allocation, address.offset, length⟩), after), reached)

/-- Layout and disjointness obligations on an external nonempty region. These
are concrete preconditions, not an assumption that reserve already succeeded. -/
abbrev Fits (state : State) (length base : Nat) : Prop :=
  RegionAllocation.Fits state ⟨length * 4, 4⟩ base

end Compiler.ZigAir.Memory.WordAllocation
