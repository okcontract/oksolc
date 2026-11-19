/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstantFoldReturnTests
import Compiler.Extraction.InternerNativeConstantDispatch

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ConstantFoldTests
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul

/-- The first production stage forwards the folded native word to the actual
constant child and returns its reached result before any later rule. -/
theorem iszero_result (reads : Nested.Reads)
    (constructors : Associative.Constructors AssemblyItem.Fields.Values (GraphAction (Publication.Effects Nat)))
    (value : Word) (metadata : AssemblyItem.Fields.Values) (before after : World (Publication.Effects Nat))
    (result : Except Fault NodeId) (constant : reads.constant 4 = .ok (some value))
    (called : constructors.constant (Unary.iszero.eval value) metadata before = (result, after))
    (input : Nested.OperandRead (GraphAction (Publication.Effects Nat)) := Nested.logicalOperand)
    (address : Nat := 0) :
    (Dispatch.simplifyWithInputs reads constructors 64 21 [4] metadata input address) before = (result.map some, after) := by
  have collected : Dispatch.collectConstants reads [4] = .ok (some [value]) := by
    unfold Dispatch.collectConstants
    rw [constant]
    rfl
  have folded : Folding.run Folding.helpers Folding.clauses 21 [value] = .ok (some (Unary.iszero.eval value)) := by
    simpa only [Folding.Op.opcode, Folding.Op.eval, Folding.Op.arity, Folding.Op.value] using
      Folding.folding_correct .iszero [value]
  simpa only [called] using NativeRecursion.constant_dispatch_result reads constructors 64 21 [4] metadata
    before [value] (Unary.iszero.eval value) (by decide) (by decide) collected folded input address

theorem iszero_failure (reads : Nested.Reads)
    (constructors : Associative.Constructors AssemblyItem.Fields.Values (GraphAction (Publication.Effects Nat)))
    (value : Word) (metadata : AssemblyItem.Fields.Values) (before after : World (Publication.Effects Nat)) {fault : Fault}
    (constant : reads.constant 4 = .ok (some value))
    (called : constructors.constant (Unary.iszero.eval value) metadata before = (.error fault, after))
    (input : Nested.OperandRead (GraphAction (Publication.Effects Nat)) := Nested.logicalOperand)
    (address : Nat := 0) :
    (Dispatch.simplifyWithInputs reads constructors 64 21 [4] metadata input address) before = (.error fault, after) := by
  exact iszero_result reads constructors value metadata before after (.error fault) constant called input address

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ConstantFoldTests
