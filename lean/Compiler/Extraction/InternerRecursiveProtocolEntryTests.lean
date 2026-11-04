/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursiveProtocolEntry
import Compiler.Extraction.InternerConstructorProtocolInduction
import Compiler.Extraction.InternerConstructorProtocolEntryTests
import Compiler.Extraction.InternerConstructorProtocolTraceTests
import Compiler.Extraction.InternerNativeConstructors

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ProtocolTrace.EntryTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray Caller.ProtocolTrace ConstructorItem.ProtocolTrace

/-- Reuse the existing capacity override and borrowed input. This checks the
wrapper control, not a native representation of a graph with 2^32-1 rows. -/
def base := { ConstructorItem.ProtocolTrace.Tests.cacheContext with queries := EntryFailureTests.fullQueries }
def before := Publication.OriginTests.before .scratch
def source : ArgumentSlice := ⟨0, [3, 1]⟩
def model := { Caller.CacheStream.Tests.model with atCapacity := fun _ => true }
def family (depth : Nat) := unfold (CallerTraceTests.ops false) (fun _ _ _ effects => (none, effects)) false 3
  Insertion.Tests.model base none 64 (depth + 1)

theorem valid : Valid before.memory := (Publication.OriginTests.initial_good .scratch).1
theorem good : Good (view source) source.items before := Publication.OriginTests.initial_good .scratch

/-- The same capacity outcome is ordinary on every wrapper, so the projection
regression is not discharged by a rejected preparation. The unused local slot
is out of range here and must remain unused. -/
theorem capacity_observed :
    ((family 1).operation 1 [3, 1] AssemblyItem.Initializers.Tests.debug before []).1 = .error (.language .capacity) ∧
    ((family 1).borrowedOperation source.address 1 source.items AssemblyItem.Initializers.Tests.debug before []).1 = .error (.language .capacity) ∧
    ((family 1).constant 0 AssemblyItem.Initializers.Tests.debug before []).1 = .error (.language .capacity) ∧
    ((family 1).materialize 99 0 AssemblyItem.Initializers.Tests.debug before []).1 = .error (.language .capacity) ∧
    ((family 1).localOperation 1 source 2 99 false AssemblyItem.Initializers.Tests.debug before []).1 = .error (.language .capacity) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> insertion_kernel_rfl

/-- One existing capacity input exercises every actual finite entry. All five
proofs consume the general entry composition; no child or miss callback runs. -/
theorem capacity_entries (depth selected : Nat) (leading trailing : List ProtocolEvent)
    (other : Meaning) (read : Read) (sequence : BitVec 32) :
    EntryProjected model (Interner.constructorCode.operationRequest 1 [3, 1]) before.graph leading trailing
      ((family depth).operation 1 [3, 1] AssemblyItem.Initializers.Tests.debug before leading) ∧
    EntryProjected model (Interner.constructorCode.operationRequest 1 source.items) before.graph leading trailing
      ((family depth).borrowedOperation source.address 1 source.items AssemblyItem.Initializers.Tests.debug before leading) ∧
    EntryProjected model (Interner.constructorCode.constantRequest 0) before.graph leading trailing
      ((family depth).constant 0 AssemblyItem.Initializers.Tests.debug before leading) ∧
    EntryProjected model (Interner.constructorCode.constantRequest 0) before.graph leading trailing
      ((family depth).materialize 99 0 AssemblyItem.Initializers.Tests.debug before leading) ∧
    EntryProjected model (Interner.constructorCode.operationRequest 1 source.items) before.graph leading trailing
      ((family depth).localOperation 1 source selected 99 false AssemblyItem.Initializers.Tests.debug before leading) := by
  have admitted := Publication.external_admitted _ (Normalization.Tests.external_admitted (fun _ => false))
  have typed := AssemblyItem.Initializers.Tests.debug_valid
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact operation_entry_projected (CallerTraceTests.ops false) (fun _ _ _ effects => (none, effects)) false 3
      Insertion.Tests.model base none 64 depth model _ before leading trailing other read sequence admitted typed rfl
      1 [3, 1] valid rfl (by intro target prepared ran constructed address memory made impossible; cases impossible)
  · exact borrowed_entry_projected (CallerTraceTests.ops false) (fun _ _ _ effects => (none, effects)) false 3
      Insertion.Tests.model base none 64 depth model _ before leading trailing other read sequence admitted typed rfl
      1 source good rfl (by intro constructed address memory made impossible; cases impossible)
  · exact constant_entry_projected (CallerTraceTests.ops false) (fun _ _ _ effects => (none, effects)) false 3
      Insertion.Tests.model base none 64 depth model _ before leading trailing other read sequence admitted typed rfl
      0 valid rfl (by intro constructed address memory made impossible; cases impossible)
  · exact materialize_entry_projected (CallerTraceTests.ops false) (fun _ _ _ effects => (none, effects)) false 3
      Insertion.Tests.model base none 64 depth model _ before leading trailing other read sequence admitted typed rfl
      99 0 valid rfl (by intro constructed address memory made impossible; cases impossible)
  · exact local_entry_projected (CallerTraceTests.ops false) (fun _ _ _ effects => (none, effects)) false 3
      Insertion.Tests.model base none 64 depth model _ before leading trailing other read sequence admitted typed rfl
      1 source selected 99 false good (by intro impossible; cases impossible) rfl
      (by intro target prepared ran constructed address memory made impossible; cases impossible)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ProtocolTrace.EntryTests
