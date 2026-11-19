/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorProtocolCompleteTests
import Compiler.Extraction.InternerConstructorItemTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace.EntryTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray Caller.ProtocolTrace

/-- Reuse both original preparation failures: malformed debug data retains
the allocated local, while stack exhaustion retains the initial world. Neither
failure is ordinary compiler OOM, and both retain arbitrary recorder history. -/
theorem preparation_rejections (context : PairInput.Context Nat)
    (ports : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → GraphObservations Nat)
    (leading : List ProtocolEvent) :
    (item context ports ⟨99, 8, 0⟩ (ConstructorItem.Tests.request true) AssemblyItem.Initializers.Tests.invalidDebug
        ConstructorItem.Tests.blank leading =
      (.error (.memory (.preparation (.memory .malformed))), start ConstructorItem.Tests.allocatedBlank leading) ∧
      ordinary (item context ports ⟨99, 8, 0⟩ (ConstructorItem.Tests.request true) AssemblyItem.Initializers.Tests.invalidDebug
        ConstructorItem.Tests.blank leading).1 = false) ∧
    (item context ports ⟨99, 8, 0⟩ (ConstructorItem.Tests.request true) ConstructorItem.Tests.debug
        ConstructorItem.Tests.exhausted leading =
      (.error (.memory (.preparation (.memory .outOfMemory))), start ConstructorItem.Tests.exhausted leading) ∧
      ordinary (item context ports ⟨99, 8, 0⟩ (ConstructorItem.Tests.request true) ConstructorItem.Tests.debug
        ConstructorItem.Tests.exhausted leading).1 = false) :=
  ⟨item_rejected context ports _ _ _ _ _ _ leading ConstructorItem.Tests.preparation_rejections.1,
   item_rejected context ports _ _ _ _ _ _ leading ConstructorItem.Tests.preparation_rejections.2⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace.EntryTests
