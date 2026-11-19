/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.ScopedRecursiveFrames
import Compiler.Extraction.InternerScopeTests

namespace Compiler.Extraction.Interner.Scoped.FrameTests
open Compiler.Algebraic Compiler.Extraction.Cache

theorem all_depths (failAt depth : Nat) :
    Extends Recursive.FrameTests.initial (Tests.recursive failAt depth).2.heap ∧
      Closed (Tests.recursive failAt depth).2.scope :=
  ScopedRecursive.detailed_preserves _ _ (InsertEffectTests.primitive_frames failAt) _ _ _ _ _

theorem old_operation_retained (failAt depth : Nat) :
    (representativeReads (Tests.recursive failAt depth).2.heap).operation 0 0x33 =
      (representativeReads Recursive.FrameTests.initial).operation 0 0x33 :=
  Extends.operation _ _ (all_depths failAt depth).1 Recursive.FrameTests.cells rfl 0 (by decide) 0x33

theorem old_constant_retained (failAt depth : Nat) :
    (representativeReads (Tests.recursive failAt depth).2.heap).constant 1 =
      (representativeReads Recursive.FrameTests.initial).constant 1 :=
  Extends.constant _ _ (all_depths failAt depth).1 Recursive.FrameTests.cells rfl 1 (by decide)

theorem parent_failure_child_read :
    (representativeReads Tests.parentFailure.2.heap).constant 3 = .ok (some 42) := rfl

theorem forced_failure_frames : Extends Recursive.FrameTests.initial Tests.forceFailure.2.heap :=
  force_frames (Tests.resources 1) _ (InsertEffectTests.primitive_frames 1).publish
    (fun _ _ => .ok ()) 1 Tests.nondeterministic.item Tests.nondeterministic.arguments Recursive.FrameTests.initial

/-- Deliberately violates the insertion frame contract while leaving word reads
unchanged. Local ownership safety cannot hide the lost representative graph. -/
def dropping : Primitives := {
  InsertEffectTests.primitives 99 with
  deterministic := fun _ => .ok false
  insert := fun _ _ before => (.error .outOfMemory, { before with representatives := none })
}
def dropped := findDetailed (Tests.resources 99) dropping Tests.nondeterministic Recursive.FrameTests.initial

theorem dropped_scope_closed : Closed dropped.2.scope := find_closed _ _ _ _

theorem dropped_reads_unchanged : dropped.2.heap.read = Recursive.FrameTests.initial.read := rfl

theorem missing_frame_rejected : ¬Extends Recursive.FrameTests.initial dropped.2.heap := by
  intro framed
  obtain ⟨suffix, impossible⟩ := framed Recursive.FrameTests.cells rfl
  cases impossible

theorem dropping_primitive_rejected : ¬Recursive.PrimitiveFrames dropping := by
  intro primitive
  have framed := primitive.insert Tests.tempKey false Recursive.FrameTests.initial
  obtain ⟨suffix, impossible⟩ := framed Recursive.FrameTests.cells rfl
  cases impossible

end Compiler.Extraction.Interner.Scoped.FrameTests
