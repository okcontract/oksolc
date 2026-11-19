/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPublicationMemoryBoundary
import Compiler.Extraction.OwnedKeysPhysicalTests

namespace Compiler.Extraction.OwnedKeys.Physical.MemoryBoundaryTests
open Tests

/-- Match the field selected by `ExpressionMap.readSize` to both captured native
owner layouts. The executable gate checks these extents and offsets again. -/
theorem captured_count_layout :
    ((RepresentativeArray.Owner.layout true).bytes,
      RepresentativeArray.Owner.expressionsOffset true + ExpressionMap.sizeOffset true,
      (RepresentativeArray.Owner.layout false).bytes,
      RepresentativeArray.Owner.expressionsOffset false + ExpressionMap.sizeOffset false) =
      (72, 64, 56, 48) := rfl

/-- The empty-argument restriction matters: an existing nonempty key releases
its old typed allocation. Reuse the established replacement execution. -/
theorem nonempty_changes_memory : (observed).2.memory.memory ≠ before.memory.memory := by
  intro same
  have dead := replacement.2.2.2.1
  rw [same] at dead
  cases dead

/-- Memory framing does not erase private allocator effects. -/
theorem empty_changes_effects :
    (run (probe false) external 7 emptyKey ⟨2, 5⟩ empty).2.memory.effects ≠ empty.memory.effects := by
  rw [empty_sentinel]
  decide

end Compiler.Extraction.OwnedKeys.Physical.MemoryBoundaryTests
