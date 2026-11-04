/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.ShiftMasksProgram
import Compiler.Extraction.AssociativeProofs

namespace Compiler.Extraction.ShiftMasks
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.Extraction.Interner Compiler.Extraction.Nested Contract.Yul
set_option linter.unusedSimpArgs false

private theorem pure_bind_action (value : α) (next : α → Action β) :
    ((pure value : Action α) >>= next) = next value := rfl

theorem shl_opcode : shlOpcode = Folding.Op.shl.opcode := rfl
theorem shr_opcode : shrOpcode = Folding.Op.shr.opcode := rfl

theorem coverage_correct (amount : Word) (bound : amount.toNat ≤ 256) :
    shiftedCoverage amount = .ok (Folding.Op.shr.value amount (BitVec.allOnes 256) 0) := by
  by_cases boundary : amount.toNat = 256
  · simp [shiftedCoverage, Folding.Op.value, Binary.eval, boundary]
  · have small : amount.toNat < 256 := by omega
    simp [shiftedCoverage, Folding.Op.value, Binary.eval, boundary, small]

theorem coverage_fault (amount : Word) (large : 256 < amount.toNat) :
    shiftedCoverage amount = .error .safetyFault := by
  have different : amount.toNat ≠ 256 := by omega
  have outside : ¬amount.toNat < 256 := by omega
  simp [shiftedCoverage, different, outside]

theorem shift_product_safe (other : Meaning) (reads : Reads) (build : OperationBuilder Debug)
    (constructs : Constructs other build) (before : Heap) (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (valueId shiftedId : NodeId) (value shiftedValue : Word) (debug : Debug)
    (valueRead : before.read valueId = some value) (shiftedRead : before.read shiftedId = some shiftedValue) :
    Safe (Folding.wordMeaning other) (powerOfTwoShiftProduct reads build valueId shiftedId debug) before
      (fun result after => ∀ id, result = some id → after.read id = some (value * shiftedValue)) := by
  unfold powerOfTwoShiftProduct
  apply read_action_bind_safe _ before _ _ _ valid
  intro option lookup
  cases option with
  | none => exact Safe.pure _ before none _ valid (by simp)
  | some slice =>
    dsimp only
    split
    next amountId baseId items =>
      apply read_action_bind_safe _ before _ _ _ valid
      intro constant found
      by_cases one : constant = some (1 : Word)
      · subst constant
        simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨amount, base, amountRead, baseRead, shiftedFact⟩ := binary_values other before.read reads sound .shl
          rfl shiftedId amountId baseId slice lookup items
        have literal := sound.constant baseId 1 found
        have baseOne : base = 1 := Option.some.inj (baseRead.symm.trans literal)
        subst base
        have same : shiftedValue = Folding.Op.shl.value amount 1 0 := Option.some.inj (shiftedRead.symm.trans shiftedFact)
        rw [same, power_shift_value]
        apply Safe.bind _ before _ _ (fun id after => after.read id = some (Folding.Op.shl.value amount value 0)) _
          (constructs .shl [amountId, valueId] [amount, value] _ debug before valid
            (by simp [readArguments, amountRead, valueRead]) rfl)
        intro result after validAfter _ actual
        exact Safe.pure _ after (some result) _ validAfter (by intro id equal; cases equal; exact actual)
      · have different : (constant != some (1 : Word)) = true := by simpa using one
        simp only [different, ↓reduceIte]
        exact Safe.pure _ before none _ valid (by simp)
    next => exact Safe.pure _ before none _ valid (by simp)

theorem remove_mask_safe (other : Meaning) (reads : Reads) (constructors : Associative.Constructors Debug)
    (constructs : ∀ address, Constructs other (constructors.borrowedOperation address))
    (before : Heap) (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (maskId shiftedId : NodeId) (maskValue shiftedValue : Word) (debug : Debug)
    (maskRead : before.read maskId = some maskValue) (shiftedRead : before.read shiftedId = some shiftedValue) :
    Safe (Folding.wordMeaning other) (removeCoveredShiftMask reads constructors maskId shiftedId debug) before
      (fun result after => ∀ id, result = some id → after.read id = some (maskValue &&& shiftedValue)) := by
  unfold removeCoveredShiftMask
  apply read_action_bind_safe _ before _ _ _ valid
  intro maskOption maskFound
  cases maskOption with
  | none => exact Safe.pure _ before none _ valid (by simp)
  | some mask =>
    have literal := sound.constant maskId mask maskFound
    have same : mask = maskValue := Option.some.inj (literal.symm.trans maskRead)
    subst mask
    apply read_action_bind_safe _ before _ _ _ valid
    intro option lookup
    cases option with
    | none => exact Safe.pure _ before none _ valid (by simp)
    | some slice =>
      dsimp only
      split
      next amountId valueId items =>
        apply read_action_bind_safe _ before _ _ _ valid
        intro amountOption amountFound
        cases amountOption with
        | none => exact Safe.pure _ before none _ valid (by simp)
        | some amount =>
          dsimp only
          split
          next large => exact Safe.pure _ before none _ valid (by simp)
          next small =>
            have bound : amount.toNat ≤ 256 := by omega
            simp only [coverage_correct amount bound, readAction, pure_bind_action]
            split
            next covered =>
              obtain ⟨actualAmount, value, amountRead, valueRead, shiftedFact⟩ := binary_values other before.read reads sound .shr
                rfl shiftedId amountId valueId slice lookup items
              have literal := sound.constant amountId amount amountFound
              have same : actualAmount = amount := Option.some.inj (amountRead.symm.trans literal)
              subst actualAmount
              have same : shiftedValue = Folding.Op.shr.value amount value 0 := Option.some.inj (shiftedRead.symm.trans shiftedFact)
              have covers : maskValue &&& Folding.Op.shr.value amount (BitVec.allOnes 256) 0 =
                  Folding.Op.shr.value amount (BitVec.allOnes 256) 0 := by simpa using covered
              rw [same, covered_mask_value amount value maskValue covers]
              apply Safe.bind _ before _ _ (fun id after => after.read id = some (Folding.Op.shr.value amount value 0)) _
                (constructs slice.address .shr slice.items [amount, value] _ debug before valid
                  (by simp [items, readArguments, amountRead, valueRead]) rfl)
              intro result after validAfter _ actual
              exact Safe.pure _ after (some result) _ validAfter (by intro id equal; cases equal; exact actual)
            next => exact Safe.pure _ before none _ valid (by simp)
      next => exact Safe.pure _ before none _ valid (by simp)

theorem interner_helpers_safe (other : Meaning) (p : Primitives)
    (contracts : Contracts (Folding.wordMeaning other) p) (reads : Reads) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before) (sound : Sound (Folding.wordMeaning other) before.read reads)
    (valueId shiftedId : NodeId) (value shiftedValue : Word) (debug : Debug)
    (valueRead : before.read valueId = some value) (shiftedRead : before.read shiftedId = some shiftedValue) :
    Safe (Folding.wordMeaning other)
      (powerOfTwoShiftProduct reads (internerBuilder p) valueId shiftedId debug) before
      (fun result after => ∀ id, result = some id → after.read id = some (value * shiftedValue)) ∧
    Safe (Folding.wordMeaning other)
      (removeCoveredShiftMask reads (Associative.implementedConstructors p) valueId shiftedId debug) before
      (fun result after => ∀ id, result = some id → after.read id = some (value &&& shiftedValue)) :=
  ⟨shift_product_safe other reads (internerBuilder p) (interner_constructs other p contracts)
      before valid sound valueId shiftedId value shiftedValue debug valueRead shiftedRead,
    remove_mask_safe other reads _ (fun _ => interner_constructs other p contracts)
      before valid sound valueId shiftedId value shiftedValue debug valueRead shiftedRead⟩

end Compiler.Extraction.ShiftMasks
