/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryWordSwapRegions
import Compiler.ZigAir.MemoryShapeTests
import Compiler.ZigAir.MemoryWordSwapConfinementTests

namespace Compiler.ZigAir.MemoryWordSwap.Tests
open Memory MemoryAir Control.Machine
open Memory.ByteExchange.Tests (caller view items writable represented)

theorem all_prefix_shapes (fuel : Nat) (event : Observation Ty Prim Value State)
    (present : event ∈ (bodyObserved fuel caller).1) : caller.heap.RetainsShape event.state.heap :=
  captured_retains_shape caller view 0 1 fuel WordByteView.Tests.valid_caller event present

theorem exhausted_prefix_shapes (fuel : Nat) (event : Observation Ty Prim Value State)
    (present : event ∈ (bodyObserved fuel exhausted).1) : exhausted.heap.RetainsShape event.state.heap :=
  captured_retains_shape exhausted view 0 1 fuel exhausted_valid event present

theorem all_prefix_writable (fuel : Nat) (event : Observation Ty Prim Value State)
    (present : event ∈ (bodyObserved fuel caller).1) : WordArray.Writable event.state view :=
  Heap.RetainsShape.writable caller event.state view (all_prefix_shapes fuel event present) writable

theorem fixed_argument_regions :
    ∃ cell, caller.heap.lookup view.allocation = some cell ∧
      0 < cell.base + (view.address 0).offset ∧
      cell.base + (view.address 0).offset + 4 ≤ addressLimit ∧
      0 < cell.base + (view.address 1).offset ∧
      cell.base + (view.address 1).offset + 4 ≤ addressLimit ∧
      (cell.base + (view.address 0).offset + 4 ≤ cell.base + (view.address 1).offset ∨
       cell.base + (view.address 1).offset + 4 ≤ cell.base + (view.address 0).offset) ∧
      ∀ fuel event, event ∈ (bodyObserved fuel caller).1 →
        ∃ updated, event.state.heap.lookup view.allocation = some updated ∧ cell.SameShape updated :=
  captured_regions caller view 0 1 WordByteView.Tests.valid_caller writable (by decide) (by decide) (by decide)

theorem actual_byte_regions (fuel : Nat) (event : Observation Ty Prim Value State) (order : WordBytes.Order) (pointer : Ref)
    (present : event ∈ (bodyObserved fuel caller).1)
    (kind : event.site.2.2 = .wordByteLoad order pointer ∨ ∃ value, event.site.2.2 = .wordByteStore order pointer value) :
    ∃ original current address word,
      caller.heap.lookup view.allocation = some original ∧
      event.state.heap.lookup address.allocation = some current ∧ original.SameShape current ∧
      pointer.eval event.env = .ok (ByteAccess.pointer true false address) ∧
      ((pointer = .local 18 ∧ word = 0) ∨ (pointer = .local 19 ∧ word = 1)) ∧
      ByteAccess.wordAddress address = view.address word ∧
      current.base + (ByteAccess.wordAddress address).offset = original.base + (view.address word).offset ∧
      original.base + (view.address word).offset ≤ current.base + address.offset ∧
      current.base + address.offset < original.base + (view.address word).offset + 4 :=
  captured_byte_regions caller view items 0 1 WordByteView.Tests.valid_caller writable represented
    (by decide) (by decide) (by decide) fuel event order pointer present kind

end Compiler.ZigAir.MemoryWordSwap.Tests
