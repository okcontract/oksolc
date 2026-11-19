/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstantNegationReturnTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ConstantNegationTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul

theorem negate_failure (reads : Nested.Reads)
    (constructors : Associative.Constructors AssemblyItem.Fields.Values (GraphAction (Publication.Effects Nat)))
    (value : Word) (metadata : AssemblyItem.Fields.Values) (before after : World (Publication.Effects Nat))
    {fault : Fault} (nonzero : value ≠ 0)
    (left : reads.constant 0 = .ok none) (right : reads.constant 4 = .ok (some value))
    (equality : reads.overrideEquality = none)
    (called : constructors.constant (0 - value) metadata before = (.error fault, after))
    (input : Nested.OperandRead (GraphAction (Publication.Effects Nat)) := Nested.logicalOperand)
    (address : Nat := 0) :
    (Dispatch.simplifyWithInputs reads constructors 64 3 [0, 4] metadata input address) before = (.error fault, after) := by
  have collected : Dispatch.collectConstants reads [0, 4] = .ok none := by
    unfold Dispatch.collectConstants; rw [left]; rfl
  have selected : zigSelect 3 .constants ⟨none, some value, false⟩ = none := by
    change zigSelectFrom productionRules (productionOpcode .sub) .constants _ = none
    rw [zigSelectFrom_eq]
    simp [select, productionRules, Guard.stage, Guard.matches]
    exact nonzero
  have first : (Dispatch.constantStage reads constructors 3 [0, 4] metadata) before = (.ok none, before) := by
    simp only [Dispatch.constantStage, collected]; rfl
  have second : (Dispatch.binaryStageWithInputs reads constructors 64 3 0 4 metadata Dispatch.defaultOptions input) before =
      (.error fault, after) := by
    simp only [Dispatch.binaryStageWithInputs, left, right, Nested.readAction, selected, Nested.sameExpression, equality,
      Dispatch.opSDIV, Dispatch.opAND, Dispatch.opBYTE, Dispatch.opXOR, Dispatch.opOR, Dispatch.opSIGNEXTEND,
      Dispatch.opMOD, Dispatch.opSHL, Dispatch.opSHR, Dispatch.opSUB,
      BitVec.reduceBEq, Bool.false_eq_true, Bool.false_or, ↓reduceIte, bind, Effect.bind, pure, Effect.pure]
    change (do let id ← constructors.constant (0 - value) metadata
               let result ← ConstructorPair.scalars constructors Dispatch.opADD 0 id metadata
               pure (some result) : GraphAction (Publication.Effects Nat) (Option NodeId)) before = _
    exact Effect.bind_failure _ _ _ _ _ called
  unfold Dispatch.simplifyWithInputs Dispatch.simplifyOptionsWithInputs
  simp only [Dispatch.orNext, bind, Effect.bind, first]
  exact (Effect.bind_failure _ _ _ _ _ second).trans rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ConstantNegationTests
