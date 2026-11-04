/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchAlgebraicProofs

namespace Compiler.Extraction.Dispatch
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096

theorem word_power_one (exponent : Nat) : Contract.Interaction.WordPower.pow 1 exponent = 1 := by
  apply BitVec.eq_of_toNat_eq
  rw [Contract.Interaction.WordPower.toNat_pow]
  simp

theorem exp_zero_value (exponent : Word) :
    Folding.Op.exp.value 0 exponent 0 = Folding.Op.iszero.value exponent 0 0 := by
  by_cases zero : exponent = 0
  · subst exponent
    simp [Folding.Op.value, Unary.eval, boolWord]
  · have positive : 0 < exponent.toNat := by
      have nonzero : exponent.toNat ≠ 0 := by
        intro equal
        exact zero (BitVec.eq_of_toNat_eq equal)
      omega
    simp only [Folding.Op.value, Unary.eval, zero, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    rw [Contract.Interaction.WordPower.toNat_pow]
    simp [Nat.zero_pow positive, boolWord, zero]
    split
    · rename_i equal
      exact (zero equal).elim
    · rfl

theorem exp_one_value (exponent : Word) : Folding.Op.exp.value 1 exponent 0 = 1 :=
  word_power_one exponent.toNat

theorem exp_two_value (exponent : Word) :
    Folding.Op.exp.value 2 exponent 0 = Folding.Op.shl.value exponent 1 0 := by
  by_cases small : exponent.toNat < 256
  · simp only [Folding.Op.value, Binary.eval, small, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    rw [Contract.Interaction.WordPower.toNat_pow, Folding.highBit_toNat exponent.toNat small]
    change 2 ^ exponent.toNat % 2 ^ 256 = 2 ^ exponent.toNat
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_of_lt (by decide : 1 < 2) small)
  · simp only [Folding.Op.value, Binary.eval, small, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    rw [Contract.Interaction.WordPower.toNat_pow]
    change 2 ^ exponent.toNat % 2 ^ 256 = 0
    exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega))

theorem word_power_minus_one (exponent : Nat) :
    Contract.Interaction.WordPower.pow (BitVec.allOnes 256) exponent =
      if exponent % 2 = 0 then 1 else BitVec.allOnes 256 := by
  by_cases zero : exponent = 0
  · subst exponent
    simp
  · rw [Contract.Interaction.WordPower.pow, dif_neg zero]
    have squared : (BitVec.allOnes 256) * (BitVec.allOnes 256) = (1 : Word) := by rfl
    rw [squared, word_power_one]
    split <;> simp

theorem exp_minus_one_value (exponent : Word) :
    Folding.Op.exp.value (BitVec.allOnes 256) exponent 0 =
      Folding.Op.sub.value (Folding.Op.iszero.value (exponent &&& 1) 0 0) (exponent &&& 1) 0 := by
  have parity : (exponent &&& 1).toNat = exponent.toNat % 2 := by
    exact Nat.and_two_pow_sub_one_eq_mod exponent.toNat 1
  have bit : exponent &&& 1 = if exponent.toNat % 2 = 0 then 0 else 1 := by
    apply BitVec.eq_of_toNat_eq
    rw [parity]
    split
    · assumption
    · have bound := Nat.mod_lt exponent.toNat (by decide : 0 < 2)
      change exponent.toNat % 2 = 1
      omega
  simp only [Folding.Op.value, Binary.eval, Unary.eval]
  rw [word_power_minus_one, bit]
  split <;> rfl

theorem exp_minus_one_safe (other : Meaning) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (operand : NodeId) (exponent : Word) (debug : Debug)
    (actual : before.read operand = some exponent) :
    Safe (Folding.wordMeaning other) (do
      let one ← constructors.constant 1 debug
      let parity ← constructors.operation opAND [operand, one] debug
      let even ← constructors.operation opISZERO [parity] debug
      return some (← constructors.operation opSUB [even, parity] debug)) before
      (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.exp.value (BitVec.allOnes 256) exponent 0)) := by
  rw [exp_minus_one_value]
  apply Safe.bind _ before _ _ _ _ (correct.constant 1 debug before valid)
  intro one afterOne validOne stableOne oneRead
  apply Safe.bind _ afterOne _ _ _ _ (correct.operation .and [operand, one] [exponent, 1] (exponent &&& 1) debug afterOne validOne
    (by simp [readArguments, stableOne operand exponent actual, oneRead]) rfl)
  intro parity afterParity validParity _ parityRead
  apply Safe.bind _ afterParity _ _ _ _ (correct.operation .iszero [parity] [exponent &&& 1] _ debug afterParity validParity
    (by simp [readArguments, parityRead]) rfl)
  intro even afterEven validEven stableEven evenRead
  exact operation_some_safe other constructors correct afterEven validEven .sub [even, parity]
    [Folding.Op.iszero.value (exponent &&& 1) 0 0, exponent &&& 1] _ debug
    (by simp [readArguments, evenRead, stableEven parity (exponent &&& 1) parityRead]) rfl

theorem exp_evm_stage_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (version : Version) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (evmStage reads constructors usizeBits opEXP [left, right] debug version) before
      (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.exp.value a b 0)) := by
  simp only [evmStage, evmStageWithInputs, logicalOperand, shiftInput_some, maxExponent, Effect.bind_pure, opEXP, opBALANCE, opMUL, opDIV,
    Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, BitVec.reduceBEq]
  apply read_action_bind_safe _ before _ _ _ valid
  intro base lookup
  by_cases zero : base = some (0 : Word)
  · subst base
    simp only [beq_self_eq_true, ↓reduceIte]
    have same : a = 0 := Option.some.inj (lhs.symm.trans (sound.constant left 0 lookup))
    rw [same, exp_zero_value]
    exact operation_some_safe other constructors correct before valid .iszero [right] [b] _ debug
      (by simp [readArguments, rhs]) rfl
  · have different : (base == some (0 : Word)) = false := by simpa using zero
    simp only [different, Bool.false_eq_true, ↓reduceIte]
    by_cases one : base = some (1 : Word)
    · subst base
      simp only [beq_self_eq_true, ↓reduceIte]
      have same : a = 1 := Option.some.inj (lhs.symm.trans (sound.constant left 1 lookup))
      rw [same, exp_one_value]
      exact constant_some_safe other constructors correct before valid 1 debug
    · have different : (base == some (1 : Word)) = false := by simpa using one
      simp only [different, Bool.false_eq_true, ↓reduceIte]
      by_cases two : (base == some (2 : Word) && hasBitwiseShifting version) = true
      · simp only [two, ↓reduceIte]
        have pair : base = some (2 : Word) ∧ hasBitwiseShifting version = true := by simpa using two
        have twoBase := pair.1
        have same : a = 2 := Option.some.inj (lhs.symm.trans (sound.constant left 2 (twoBase ▸ lookup)))
        rw [same, exp_two_value]
        apply Safe.bind _ before _ _ _ _ (correct.constant 1 debug before valid)
        intro oneId after validAfter stable oneRead
        exact operation_some_safe other constructors correct after validAfter .shl [right, oneId] [b, 1] _ debug
          (by simp [readArguments, stable right b rhs, oneRead]) rfl
      · simp only [two, ↓reduceIte]
        by_cases minusOne : base = some (BitVec.allOnes 256)
        · subst base
          simp only [beq_self_eq_true, ↓reduceIte]
          have same : a = BitVec.allOnes 256 := Option.some.inj (lhs.symm.trans (sound.constant left _ lookup))
          rw [same]
          change Safe (Folding.wordMeaning other)
            (Effect.bind (maxExponent constructors (fun one debug => constructors.operation opAND [right, one] debug) debug)
              Effect.pure) before _
          rw [Effect.bind_pure]
          exact exp_minus_one_safe other constructors correct before valid right b debug rhs
        · have different : (base == some (BitVec.allOnes 256)) = false := by simpa using minusOne
          simp only [different, Bool.false_eq_true, ↓reduceIte]
          split <;> exact Safe.pure _ before none _ valid (by simp)

theorem binary_exp_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (binaryStage reads constructors usizeBits opEXP left right debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.exp.value a b 0)) := by
  unfold binaryStage binaryStageWithInputs
  simp only [opEXP, opSDIV, opAND, opBYTE, opSLT, opSGT, opXOR, opOR,
    opSIGNEXTEND, opMOD, opSHL, opSHR, opMUL, opDIV, opSUB, Associative.isAssociative,
    Bool.false_eq_true, ↓reduceIte, Bool.false_or, Bool.or_false, Bool.true_or, Bool.or_true,
    List.contains_cons, List.contains_nil, beq_self_eq_true, BitVec.reduceBEq]
  apply read_action_bind_safe _ before _ _ _ valid
  intro lc leftRead
  apply read_action_bind_safe _ before _ _ _ valid
  intro rc rightRead
  have reliable := constant_facts_reliable _ before.read reads sound left right a b lhs rhs lc rc leftRead rightRead
  split
  next replacement selected =>
    apply algebraic_selected_safe other constructors correct before valid _ 0 .constants _ left right a b _ debug lhs rhs reliable replacement selected
    rfl
  next =>
    split
    next equal =>
      have facts := equal_facts_reliable _ before.read reads sound left right a b lhs rhs equal
      split
      next replacement selected =>
        apply algebraic_selected_safe other constructors correct before valid _ 0 .equal _ left right a b _ debug lhs rhs facts replacement selected
        rfl
      next => exact Safe.pure _ before none _ valid (by simp)
    next => exact Safe.pure _ before none _ valid (by simp)

theorem binary_exp_miss (reads : Reads) (constructors : Constructors Debug)
    (left right : NodeId) (debug : Debug) (options : Options) (usizeBits : Nat) :
    MissUnchanged (binaryStage reads constructors usizeBits opEXP left right debug options) := by
  unfold binaryStage binaryStageWithInputs
  simp only [opEXP, opSDIV, opAND, opBYTE, opSLT, opSGT, opXOR, opOR,
    opSIGNEXTEND, opMOD, opSHL, opSHR, opMUL, opDIV, opSUB, Associative.isAssociative,
    Bool.false_eq_true, ↓reduceIte, Bool.false_or, Bool.or_false, Bool.true_or, Bool.or_true,
    List.contains_cons, List.contains_nil, beq_self_eq_true, BitVec.reduceBEq]
  repeat first
    | exact pure_miss_unchanged _
    | exact terminal_miss_unchanged _
    | apply read_miss_unchanged; intro option
    | split

theorem exp_evm_miss (reads : Reads) (constructors : Constructors Debug)
    (left right : NodeId) (debug : Debug) (version : Version) (usizeBits : Nat) :
    MissUnchanged (evmStage reads constructors usizeBits opEXP [left, right] debug version) := by
  simp only [evmStage, evmStageWithInputs, logicalOperand, shiftInput_some, opEXP, opBALANCE, opMUL, opDIV,
    Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, BitVec.reduceBEq]
  change MissUnchanged (Effect.bind _ _)
  apply read_miss_unchanged
  intro option
  by_cases zero : (option == some (0 : Word)) = true
  · simp only [zero, Bool.false_eq_true, ↓reduceIte]
    exact terminal_miss_unchanged _
  · simp only [zero, Bool.false_eq_true, ↓reduceIte]
    by_cases one : (option == some (1 : Word)) = true
    · simp only [one, Bool.false_eq_true, ↓reduceIte]
      exact terminal_miss_unchanged _
    · simp only [one, Bool.false_eq_true, ↓reduceIte]
      by_cases two : (option == some (2 : Word) && hasBitwiseShifting version) = true
      · simp only [two, Bool.false_eq_true, ↓reduceIte]
        apply never_miss_unchanged
        repeat first
          | exact terminal_never_miss _
          | apply bind_never_miss; intro id
      · simp only [two, Bool.false_eq_true, ↓reduceIte]
        by_cases minusOne : (option == some (BitVec.allOnes 256)) = true
        · simp only [minusOne, Bool.false_eq_true, ↓reduceIte]
          change MissUnchanged (Effect.bind
            (maxExponent constructors (fun one debug => constructors.operation opAND [right, one] debug) debug) Effect.pure)
          rw [Effect.bind_pure]
          unfold maxExponent
          apply never_miss_unchanged
          repeat first
            | exact terminal_never_miss _
            | apply bind_never_miss; intro id
        · simp only [minusOne, Bool.false_eq_true, ↓reduceIte]
          split <;> exact pure_miss_unchanged _

/-- Complete EXP execution, including constant-folding priority, the binary
stage, all revision-gated rewrites, and every intermediate constructor failure.
The recursive constructor contract remains explicit. -/
theorem exp_simplify_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (simplifyWithOptions reads constructors usizeBits opEXP [left, right] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.exp.value a b 0)) := by
  apply binary_simplify_safe other reads constructors correct before valid sound opEXP left right a b _ 0
    debug options usizeBits lhs rhs rfl
    (binary_exp_safe other reads constructors correct before valid sound left right a b debug options usizeBits lhs rhs)
    (binary_exp_miss reads constructors left right debug options usizeBits)
  intro version _
  exact exp_evm_stage_safe other reads constructors correct before valid sound left right a b debug version usizeBits lhs rhs

theorem interner_exp_simplify_safe (other : Meaning) (pushes : Pushes other) (p : Primitives)
    (contracts : Contracts (Folding.wordMeaning other) p) (reads : Reads) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (simplifyWithOptions reads (implementedConstructors p) usizeBits opEXP [left, right] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.exp.value a b 0)) :=
  exp_simplify_safe other reads (implementedConstructors p)
    (implemented_constructors_sound other pushes p contracts) before valid sound
    left right a b debug options usizeBits lhs rhs

end Compiler.Extraction.Dispatch
