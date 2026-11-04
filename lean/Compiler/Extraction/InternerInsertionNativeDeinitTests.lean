/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionNative
import Compiler.Extraction.AssemblyItemDeinitNativeTests
import Compiler.Extraction.InternerInsertionTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CleanupTests
open Compiler.Extraction.Storage
open AssemblyItemDeinit.Native.Tests (input itemCell withItem)

def frame (session : Session Nat) : Frame Nat :=
  ⟨⟨⟨⟨⟨session.heap, session.memory, ⟨fun _ => some ⟨5, 6⟩, session.effects⟩⟩, false⟩,
    some { input with verbatim := none }⟩, some 4⟩, none⟩
def before := frame AssemblyItemDeinit.Native.Tests.before
def observed := releaseValue (Insertion.Tests.ops) 7 before

/-- Deliberately stale logical clone metadata cannot suppress the actual native
payload free. The subsequent object destroy has not run yet. -/
theorem native_payload_wins : observed.1 = .ok () ∧
    (memory observed.2).heap 3 = none ∧ (memory observed.2).memory.heap.lookup 3 = none ∧
    (memory observed.2).memory.heap.lookup 4 = some { itemCell with cells := [] } ∧
    (memory observed.2).effects.allocator = 12 ∧
    (memory observed.2).effects.keys Insertion.Tests.key = some ⟨5, 6⟩ ∧
    observed.2.item.object = some 4 ∧ observed.2.item.clone.value.isNone = true ∧
    observed.2.item.clone.execution.invalidated = false :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def readonly := releaseValue (Insertion.Tests.ops) 7 (frame (withItem { itemCell with writable := false }))
theorem rejection_keeps_reached : readonly.1 = .error (.cleanup (.memory .readOnly)) ∧
    (memory readonly.2).memory.heap.lookup 3 = none ∧ (memory readonly.2).effects.allocator = 12 ∧
    readonly.2.item.object = some 4 ∧ readonly.2.item.clone.value.isSome = true ∧
    readonly.2.item.clone.execution.invalidated = false :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem missing_object : (releaseValue (Insertion.Tests.ops) 7 { before with item := { before.item with object := none } }).1 =
    .error (.base (.creation .missingObject)) ∧
    (memory (releaseValue (Insertion.Tests.ops) 7 { before with item := { before.item with object := none } }).2).effects.allocator = 1 :=
  ⟨by decide +kernel, by decide +kernel⟩

theorem source_callback :
    ((callbacks (Insertion.Tests.ops) (fun _ _ _ effects => (none, effects)) false 7 999
      Insertion.Tests.source ⟨999, 0⟩ input Insertion.Tests.key Insertion.Tests.normalized [] 0
      (fun _ _ => Insertion.Tests.heap)).release .value {} before).1 = .ok () ∧
    (memory ((callbacks (Insertion.Tests.ops) (fun _ _ _ effects => (none, effects)) false 7 999
      Insertion.Tests.source ⟨999, 0⟩ input Insertion.Tests.key Insertion.Tests.normalized [] 0
      (fun _ _ => Insertion.Tests.heap)).release .value {} before).2).effects.allocator = 12 :=
  ⟨by decide +kernel, by decide +kernel⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CleanupTests
