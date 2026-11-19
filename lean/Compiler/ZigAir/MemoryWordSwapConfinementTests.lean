/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryWordSwapConfinement
import Compiler.ZigAir.MemoryWordSwapObservationTests
import Compiler.ZigAir.MachineGuardedTests

namespace Compiler.ZigAir.MemoryWordSwap.Tests
open Memory MemoryAir Control.Machine
open Memory.ByteExchange.Tests (caller view items writable represented)

theorem all_caller_prefixes (fuel : Nat) (event : Observation Ty Prim Value State)
    (present : event ∈ (bodyObserved fuel caller).1) :
    Footprint view 0 1 ⟨caller.nextId, 0⟩ event ∧ event.state.valid = true :=
  (captured_confinement caller view items 0 1 WordByteView.Tests.valid_caller writable represented
    (by decide) (by decide) (by decide)).2 fuel event present

theorem all_exhausted_prefixes (fuel : Nat) (event : Observation Ty Prim Value State)
    (present : event ∈ (bodyObserved fuel exhausted).1) :
    Footprint view 0 1 ⟨exhausted.nextId, 0⟩ event ∧ event.state.valid = true :=
  (captured_confinement exhausted view items 0 1 exhausted_valid
    (WordArray.writable_heap_eq caller exhausted view rfl writable)
    (WordArray.represents_heap_eq caller exhausted view items rfl represented)
    (by decide) (by decide) (by decide)).2 fuel event present

theorem all_byte_prefixes (fuel : Nat) (event : Observation Ty Prim Value State) (order : WordBytes.Order) (pointer : Ref)
    (present : event ∈ (bodyObserved fuel caller).1)
    (kind : event.site.2.2 = .wordByteLoad order pointer ∨ ∃ value, event.site.2.2 = .wordByteStore order pointer value) :
    ByteBorrow view 0 1 event.env pointer :=
  Footprint.byte_access view 0 1 ⟨caller.nextId, 0⟩ event order pointer kind (all_caller_prefixes fuel event present).1

theorem next_word_not_borrowed : ¬ ByteBorrow view 0 1
    (Control.Env.set (fun _ => none) 18 (ByteAccess.pointer true false ⟨0, 4⟩)) (.local 18) := by
  intro borrowed
  obtain ⟨index, first | second⟩ := borrowed
  · have same := first.2
    change Except.ok (ByteAccess.pointer true false ⟨0, 4⟩) =
      Except.ok (ByteAccess.pointer true false (ByteAccess.atByte (view.address 0) index)) at same
    have offsets : 4 = index.val := by simpa [ByteAccess.pointer, ByteAccess.atByte, WordArray.View.address, view] using same
    have := index.isLt
    omega
  · cases second.1

end Compiler.ZigAir.MemoryWordSwap.Tests
