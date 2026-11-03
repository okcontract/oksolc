/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.SignExtendMaskProgram

namespace Compiler.Extraction.SignExtendMask
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.Extraction.Interner Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 1024

private theorem pure_ok (value : α) : (pure value : Except Folding.Fault α) = .ok value := rfl
private theorem bind_ok (value : α) (next : α → Except Folding.Fault β) :
    ((.ok value : Except Folding.Fault α) >>= next) = next value := rfl
private theorem bind_error (fault : Folding.Fault) (next : α → Except Folding.Fault β) :
    ((.error fault : Except Folding.Fault α) >>= next) = .error fault := rfl
private theorem pure_bind_action (value : α) (next : α → Action β) :
    ((pure value : Action α) >>= next) = next value := rfl
attribute [local simp] pure_ok bind_ok bind_error

theorem signextend_opcode : signextendOpcode = Folding.Op.signextend.opcode := rfl
theorem and_opcode : andOpcode = Folding.Op.and.opcode := rfl

/-- The dominating byte-index guard discharges every native arithmetic check,
including the u8 shift-count cast and non-wrapping unsigned subtraction. -/
theorem native_low_mask_correct (index : Word) (bound : index.toNat < 31) :
    nativeLowMask index = .ok (lowBits ((index.toNat + 1) * 8)) := by
  have sum : index.toNat + 1 < 2 ^ 256 := by omega
  have product : (index.toNat + 1) * 8 < 2 ^ 256 := by omega
  have cast : (index.toNat + 1) * 8 < 2 ^ 8 := by omega
  have width : (index.toNat + 1) * 8 < 256 := by omega
  have high := Folding.highBit_toNat ((index.toNat + 1) * 8) width
  have positive : 1 ≤ 2 ^ ((index.toNat + 1) * 8) := Nat.two_pow_pos _
  simp only [nativeLowMask, Folding.Zig.checkedAdd, sum, Folding.Zig.checkedMul, product,
    Folding.Zig.narrow, cast, ↓reduceIte, bind_ok, pure_ok, high,
    Folding.Zig.checkedSub, positive, lowBits]

theorem low_mask_read_correct (index : Word) (bound : index.toNat < 31) :
    lowMaskRead index = .ok (lowBits ((index.toNat + 1) * 8)) := by
  simp [lowMaskRead, native_low_mask_correct index bound]

theorem low_mask_read_fault (index : Word) (large : 31 ≤ index.toNat) :
    lowMaskRead index = .error .safetyFault := by
  have cast : ¬ (index.toNat + 1) * 8 < 2 ^ 8 := by omega
  by_cases sum : index.toNat + 1 < 2 ^ 256
  · by_cases product : (index.toNat + 1) * 8 < 2 ^ 256
    · simp [lowMaskRead, nativeLowMask, Folding.Zig.checkedAdd, sum,
        Folding.Zig.checkedMul, product, Folding.Zig.narrow, cast]
    · simp [lowMaskRead, nativeLowMask, Folding.Zig.checkedAdd, sum,
        Folding.Zig.checkedMul, product]
  · simp [lowMaskRead, nativeLowMask, Folding.Zig.checkedAdd, sum]

theorem strip_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (maskId extendedId : NodeId) (maskValue extendedValue : Word) (debug : Debug)
    (maskRead : before.read maskId = some maskValue)
    (extendedRead : before.read extendedId = some extendedValue) :
    Safe (Folding.wordMeaning other)
      (stripRedundantSignExtendMask reads constructors maskId extendedId debug) before
      (fun result after => ∀ id, result = some id → after.read id = some (maskValue &&& extendedValue)) := by
  unfold stripRedundantSignExtendMask
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
      next indexId valueId items =>
        apply read_action_bind_safe _ before _ _ _ valid
        intro indexOption indexFound
        cases indexOption with
        | none => exact Safe.pure _ before none _ valid (by simp)
        | some index =>
          dsimp only
          split
          next large => exact Safe.pure _ before none _ valid (by simp)
          next small =>
            have bound : index.toNat < 31 := by omega
            simp only [low_mask_read_correct index bound, readAction, pure_bind_action]
            split
            next outside => exact Safe.pure _ before none _ valid (by simp)
            next contained =>
              have covers : maskValue &&& lowBits ((index.toNat + 1) * 8) = maskValue := by
                simpa using contained
              obtain ⟨actualIndex, value, indexRead, valueRead, extendedFact⟩ :=
                binary_values other before.read reads sound .signextend rfl
                  extendedId indexId valueId slice lookup items
              have literal := sound.constant indexId index indexFound
              have same : actualIndex = index := Option.some.inj (indexRead.symm.trans literal)
              subst actualIndex
              have same : extendedValue = Folding.Op.signextend.value index value 0 :=
                Option.some.inj (extendedRead.symm.trans extendedFact)
              rw [same, masked_evm_signextend index maskValue value bound covers]
              apply Safe.bind _ before _ _ (fun id after => after.read id = some maskValue) _
                (correct.materialize maskId maskValue debug before valid)
              intro materialized after validAfter stable materializedRead
              have valueAfter := stable valueId value valueRead
              apply Safe.bind _ after _ _ (fun id final => final.read id = some (maskValue &&& value)) _
                (correct.operation .and [materialized, valueId] [maskValue, value] _ debug after validAfter
                  (by simp [readArguments, materializedRead, valueAfter]) rfl)
              intro result final validFinal _ actual
              exact Safe.pure _ final (some result) _ validFinal (by intro id equal; cases equal; exact actual)
      next => exact Safe.pure _ before none _ valid (by simp)

theorem interner_strip_safe (other : Meaning) (pushes : Pushes other) (p : Primitives)
    (contracts : Contracts (Folding.wordMeaning other) p) (reads : Reads) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (maskId extendedId : NodeId) (maskValue extendedValue : Word) (debug : Debug)
    (maskRead : before.read maskId = some maskValue)
    (extendedRead : before.read extendedId = some extendedValue) :
    Safe (Folding.wordMeaning other)
      (stripRedundantSignExtendMask reads (implementedConstructors p) maskId extendedId debug) before
      (fun result after => ∀ id, result = some id → after.read id = some (maskValue &&& extendedValue)) :=
  strip_safe other reads _ (implemented_constructors_sound other pushes p contracts)
    before valid sound maskId extendedId maskValue extendedValue debug maskRead extendedRead

end Compiler.Extraction.SignExtendMask
