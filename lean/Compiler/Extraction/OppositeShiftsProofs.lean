/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.OppositeShiftsProgram

namespace Compiler.Extraction.OppositeShifts
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.Extraction.Interner Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
set_option linter.unusedSimpArgs false

theorem and_opcode : andOpcode = Folding.Op.and.opcode := rfl
theorem opposite_opcode (direction : Direction) :
    oppositeOpcode direction.op.opcode = direction.opposite.op.opcode := by cases direction <;> rfl

theorem native_mask_correct (direction : Direction) (outer inner : Word)
    (outerBound : outer.toNat < 256) (innerBound : inner.toNat < 256) :
    nativeMask direction.op.opcode outer inner =
      .ok (direction.shift (direction.opposite.shift (BitVec.allOnes 256) inner.toNat) outer.toNat) := by
  cases direction <;> simp [nativeMask, outerBound, innerBound, Direction.op, Folding.Op.opcode,
    shrOpcode, Direction.shift, Direction.opposite]

theorem native_mask_fault (opcode : Opcode) (outer inner : Word)
    (outside : 256 ≤ outer.toNat ∨ 256 ≤ inner.toNat) : nativeMask opcode outer inner = .error .safetyFault := by
  unfold nativeMask
  split
  · split
    · omega
    · rfl
  · rfl

theorem combine_cast_fault (constructors : Constructors Debug) (opcode : Opcode) (outer inner : Word)
    (id : NodeId) (debug : Debug) (before : Heap) (outside : 256 ≤ outer.toNat ∨ 256 ≤ inner.toNat) :
    combineOppositeShifts constructors opcode outer inner id debug before = (.error .safetyFault, before) := by
  unfold combineOppositeShifts
  rw [native_mask_fault opcode outer inner outside]
  rfl

theorem difference_correct (left right : Word) (ordered : right.toNat ≤ left.toNat) :
    checkedDifference left right = .ok (left - right) ∧ (left - right).toNat = left.toNat - right.toNat := by
  constructor
  · simp [checkedDifference, ordered]
  · exact BitVec.toNat_sub_of_not_usubOverflow (by simpa [BitVec.usubOverflow] using ordered)

theorem difference_fault (left right : Word) (underflow : left.toNat < right.toNat) :
    checkedDifference left right = .error .safetyFault := by
  simp [checkedDifference, show ¬right.toNat ≤ left.toNat by omega]

theorem evm_shift (direction : Direction) (amount value : Word) (bound : amount.toNat < 256) :
    direction.op.value amount value 0 = direction.shift value amount.toNat := by
  cases direction <;> simp [Direction.op, Folding.Op.value, Binary.eval, Direction.shift, bound]

private theorem build_shift_safe (other : Meaning) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (direction : Direction) (amount : Word)
    (amountBound : amount.toNat < 256) (before : Heap) (valid : Invariant (Folding.wordMeaning other) before)
    (id : NodeId) (value : Word) (actual : before.read id = some value) (debug : Debug) :
    Safe (Folding.wordMeaning other)
      (constructors.constant amount debug >>= fun amountId => constructors.operation direction.op.opcode [amountId, id] debug)
      before (fun result after => after.read result = some (direction.shift value amount.toNat)) := by
  apply Safe.bind _ before _ _ (fun id after => after.read id = some amount) _
    (correct.constant amount debug before valid)
  intro amountId middle validMiddle stable amountRead
  rw [← evm_shift direction amount value amountBound]
  exact correct.operation direction.op [amountId, id] [amount, value] _ debug middle validMiddle
    (by simp [readArguments, amountRead, stable _ _ actual])
    (by cases direction <;> rfl)

theorem net_safe (other : Meaning) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (direction : Direction) (outer inner : Word)
    (outerBound : outer.toNat < 256) (innerBound : inner.toNat < 256)
    (before : Heap) (valid : Invariant (Folding.wordMeaning other) before)
    (id : NodeId) (value : Word) (actual : before.read id = some value) (debug : Debug) :
    Safe (Folding.wordMeaning other) (buildNet constructors direction.op.opcode outer inner id debug) before
      (fun result after => after.read result = some (netShift direction outer.toNat inner.toNat value)) := by
  unfold buildNet netShift
  by_cases innerLarger : outer.toNat < inner.toNat
  · have ordered : outer.toNat ≤ inner.toNat := by omega
    obtain ⟨checked, difference⟩ := difference_correct inner outer ordered
    have bound : (inner - outer).toNat < 256 := by omega
    simp only [innerLarger, ↓reduceIte, checked, readAction, opposite_opcode]
    rw [← difference]
    exact build_shift_safe other constructors correct direction.opposite (inner - outer) bound before valid id value actual debug
  · by_cases outerLarger : inner.toNat < outer.toNat
    · have ordered : inner.toNat ≤ outer.toNat := by omega
      obtain ⟨checked, difference⟩ := difference_correct outer inner ordered
      have bound : (outer - inner).toNat < 256 := by omega
      simp only [innerLarger, outerLarger, ↓reduceIte, checked, readAction]
      rw [← difference]
      exact build_shift_safe other constructors correct direction (outer - inner) bound before valid id value actual debug
    · simp only [innerLarger, outerLarger, ↓reduceIte]
      exact Safe.pure _ before id _ valid actual

theorem combine_safe (other : Meaning) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (direction : Direction) (outer inner : Word)
    (outerBound : outer.toNat < 256) (innerBound : inner.toNat < 256)
    (before : Heap) (valid : Invariant (Folding.wordMeaning other) before)
    (id : NodeId) (value : Word) (actual : before.read id = some value) (debug : Debug) :
    Safe (Folding.wordMeaning other) (combineOppositeShifts constructors direction.op.opcode outer inner id debug) before
      (fun result after => after.read result = some
        (direction.op.value outer (direction.opposite.op.value inner value 0) 0)) := by
  unfold combineOppositeShifts
  simp only [native_mask_correct direction outer inner outerBound innerBound, readAction]
  rw [evm_shift direction outer _ outerBound, evm_shift direction.opposite inner value innerBound,
    masked_net direction outer.toNat inner.toNat value]
  apply Safe.bind _ before _ _
    (fun result after => after.read result = some (netShift direction outer.toNat inner.toNat value)) _
    (net_safe other constructors correct direction outer inner outerBound innerBound before valid id value actual debug)
  intro shifted middle validMiddle _ shiftedRead
  apply Safe.bind _ middle _ _
    (fun result after => after.read result = some
      (direction.shift (direction.opposite.shift (BitVec.allOnes 256) inner.toNat) outer.toNat)) _
    (correct.constant _ debug middle validMiddle)
  intro maskId after validAfter stable maskRead
  exact correct.operation .and [shifted, maskId]
    [netShift direction outer.toNat inner.toNat value,
      direction.shift (direction.opposite.shift (BitVec.allOnes 256) inner.toNat) outer.toNat] _ debug after validAfter
    (by simp [readArguments, stable _ _ shiftedRead, maskRead]) rfl

theorem interner_combine_safe (other : Meaning) (pushes : Pushes other) (p : Primitives)
    (contracts : Contracts (Folding.wordMeaning other) p) (direction : Direction) (outer inner : Word)
    (outerBound : outer.toNat < 256) (innerBound : inner.toNat < 256)
    (before : Heap) (valid : Invariant (Folding.wordMeaning other) before)
    (id : NodeId) (value : Word) (actual : before.read id = some value) (debug : Debug) :
    Safe (Folding.wordMeaning other)
      (combineOppositeShifts (implementedConstructors p) direction.op.opcode outer inner id debug) before
      (fun result after => after.read result = some
        (direction.op.value outer (direction.opposite.op.value inner value 0) 0)) :=
  combine_safe other (implementedConstructors p) (implemented_constructors_sound other pushes p contracts)
    direction outer inner outerBound innerBound before valid id value actual debug

end Compiler.Extraction.OppositeShifts
