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

private theorem pure_bind_action (value : α) (next : α → Action β) :
    (pure value >>= next) = next value := rfl

theorem mod_power_positive (modulus : Word) (power : Nat)
    (exactPower : BinaryLogarithm.IsPower modulus power) : 1 ≤ modulus.toNat := by
  rw [exactPower.2]
  exact Nat.two_pow_pos power

theorem mod_power_predecessor (modulus : Word) (power : Nat)
    (exactPower : BinaryLogarithm.IsPower modulus power) :
    subWord (m := Action) modulus 1 = pure (BitVec.ofNat 256 (modulus.toNat - 1)) := by
  have positive := mod_power_positive modulus power exactPower
  change (do
    let value ← arithmetic (Folding.Zig.checkedSub modulus.toNat 1)
    pure (BitVec.ofNat 256 value)) = _
  rw [Folding.Zig.checkedSub, if_pos positive]
  rfl

theorem mod_power_mask_value (value modulus : Word) (power : Nat)
    (exactPower : BinaryLogarithm.IsPower modulus power) :
    Folding.Op.mod.value value modulus 0 = value &&& BitVec.ofNat 256 (modulus.toNat - 1) := by
  have nonzero := BinaryLogarithm.power_nonzero modulus power exactPower
  have bound : modulus.toNat - 1 < 2 ^ 256 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) modulus.isLt
  simp only [Folding.Op.value, Binary.eval, nonzero, ↓reduceIte]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_umod, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  rw [exactPower.2, Nat.and_two_pow_sub_one_eq_mod]

/-- Reducing a wrapped 256-bit intermediate preserves a remainder only under
the proved divisibility condition. This is the premise needed by Yul's rewrite. -/
theorem mod_power_wrapped_value (value : Nat) (modulus : Word) (power : Nat)
    (exactPower : BinaryLogarithm.IsPower modulus power) :
    Folding.Op.mod.value (BitVec.ofNat 256 value) modulus 0 = BitVec.ofNat 256 (value % modulus.toNat) := by
  have nonzero := BinaryLogarithm.power_nonzero modulus power exactPower
  have positive := mod_power_positive modulus power exactPower
  have divides : modulus.toNat ∣ 2 ^ 256 := by
    rw [exactPower.2]
    exact Nat.pow_dvd_pow 2 (Nat.le_of_lt exactPower.1)
  have bound : value % modulus.toNat < 2 ^ 256 := Nat.lt_trans (Nat.mod_lt _ positive) modulus.isLt
  simp only [Folding.Op.value, Binary.eval, nonzero, ↓reduceIte]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_umod, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ divides, Nat.mod_eq_of_lt bound]

theorem mod_power_add_value (a b modulus : Word) (power : Nat)
    (exactPower : BinaryLogarithm.IsPower modulus power) :
    Folding.Op.mod.value (Folding.Op.add.value a b 0) modulus 0 = Folding.Op.addmod.value a b modulus := by
  have nonzero := BinaryLogarithm.power_nonzero modulus power exactPower
  simpa only [Folding.Op.value, Binary.eval, nonzero, ↓reduceIte] using
    mod_power_wrapped_value (a.toNat + b.toNat) modulus power exactPower

theorem mod_power_mul_value (a b modulus : Word) (power : Nat)
    (exactPower : BinaryLogarithm.IsPower modulus power) :
    Folding.Op.mod.value (Folding.Op.mul.value a b 0) modulus 0 = Folding.Op.mulmod.value a b modulus := by
  have nonzero := BinaryLogarithm.power_nonzero modulus power exactPower
  simpa only [Folding.Op.value, Binary.eval, nonzero, ↓reduceIte] using
    mod_power_wrapped_value (a.toNat * b.toNat) modulus power exactPower

theorem mod_nested_candidate_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (op : Folding.Op) (supported : op = .mul ∨ op = .add)
    (left right : NodeId) (value modulus : Word) (power : Nat) (debug : Debug)
    (exactPower : BinaryLogarithm.IsPower modulus power)
    (lhs : before.read left = some value) (rhs : before.read right = some modulus)
    (next : Action (Option NodeId))
    (rest : Safe (Folding.wordMeaning other) next before
      (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.mod.value value modulus 0))) :
    Safe (Folding.wordMeaning other) (do
      if let some nested ← readAction (reads.operation left op.opcode) then
        if let [a, b] := nested.items then
          return some (← constructors.operation (if op = .mul then opMULMOD else opADDMOD) [a, b, right] debug)
      next) before (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.mod.value value modulus 0)) := by
  apply read_action_bind_safe _ before _ _ _ valid
  intro option lookup
  cases option with
  | none => exact rest
  | some slice =>
    dsimp only
    split
    next aId bId items =>
      have arity : op.arity = 2 := by rcases supported with rfl | rfl <;> rfl
      obtain ⟨a, b, aRead, bRead, nestedRead⟩ := binary_values other before.read reads sound op arity left aId bId slice lookup items
      have same : value = op.value a b 0 := Option.some.inj (lhs.symm.trans nestedRead)
      rw [same]
      rcases supported with rfl | rfl
      · rw [mod_power_mul_value a b modulus power exactPower]
        exact operation_some_safe other constructors correct before valid .mulmod [aId, bId, right] [a, b, modulus] _ debug
          (by simp [readArguments, aRead, bRead, rhs]) rfl
      · rw [mod_power_add_value a b modulus power exactPower]
        exact operation_some_safe other constructors correct before valid .addmod [aId, bId, right] [a, b, modulus] _ debug
          (by simp [readArguments, aRead, bRead, rhs]) rfl
    next => exact rest

theorem mod_mask_candidate_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (known : Option Word) (debug : Debug) (usizeBits : Nat)
    (lookup : reads.constant right = .ok known)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (do
      if let some modulus := known then
        if (← arithmetic (BinaryLogarithm.binaryLogarithm usizeBits modulus)).isSome then
          return some (← constructors.operation opAND [left, ← constructors.constant (← subWord modulus 1) debug] debug)
      return none) before (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.mod.value a b 0)) := by
  cases known with
  | none => exact Safe.pure _ before none _ valid (by simp)
  | some modulus =>
    apply arithmetic_bind_safe _ before _ _ _ valid
    intro option found
    cases option with
    | none => exact Safe.pure _ before none _ valid (by simp)
    | some power =>
      have exactPower := BinaryLogarithm.found_sound usizeBits modulus power found
      have same : b = modulus := Option.some.inj (rhs.symm.trans (sound.constant right modulus lookup))
      dsimp only [Option.isSome]
      rw [mod_power_predecessor modulus power exactPower, same, mod_power_mask_value a modulus power exactPower]
      apply Safe.bind _ before _ _ _ _ (correct.constant (BitVec.ofNat 256 (modulus.toNat - 1)) debug before valid)
      intro maskId after validAfter stable maskRead
      exact operation_some_safe other constructors correct after validAfter .and [left, maskId]
        [a, BitVec.ofNat 256 (modulus.toNat - 1)] _ debug
        (by simp [readArguments, maskRead, stable left a lhs]) rfl

theorem mod_inline_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (known : Option Word) (debug : Debug) (usizeBits : Nat) (forYul : Bool)
    (lookup : reads.constant right = .ok known)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (do
      if forYul then
        if let some modulus := known then
          if (← arithmetic (BinaryLogarithm.binaryLogarithm usizeBits modulus)).isSome then
            if let some nested ← readAction (reads.operation left opMUL) then
              if let [x, y] := nested.items then
                return some (← constructors.operation opMULMOD [x, y, right] debug)
            if let some nested ← readAction (reads.operation left opADD) then
              if let [x, y] := nested.items then
                return some (← constructors.operation opADDMOD [x, y, right] debug)
      if let some modulus := known then
        if (← arithmetic (BinaryLogarithm.binaryLogarithm usizeBits modulus)).isSome then
          return some (← constructors.operation opAND [left, ← constructors.constant (← subWord modulus 1) debug] debug)
      return none) before (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.mod.value a b 0)) := by
  have tail := mod_mask_candidate_safe other reads constructors correct before valid sound left right a b known debug usizeBits lookup lhs rhs
  cases forYul with
  | false => cases known <;> exact tail
  | true =>
    cases known with
    | none => exact tail
    | some modulus =>
      apply arithmetic_bind_safe _ before _ _ _ valid
      intro option found
      cases option with
      | none => exact tail
      | some power =>
        have exactPower := BinaryLogarithm.found_sound usizeBits modulus power found
        have same : b = modulus := Option.some.inj (rhs.symm.trans (sound.constant right modulus lookup))
        subst b
        apply mod_nested_candidate_safe other reads constructors correct before valid sound .mul (Or.inl rfl)
          left right a modulus power debug exactPower lhs rhs
        exact mod_nested_candidate_safe other reads constructors correct before valid sound .add (Or.inr rfl)
          left right a modulus power debug exactPower lhs rhs _ tail

theorem binary_mod_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (binaryStage reads constructors usizeBits opMOD left right debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.mod.value a b 0)) := by
  unfold binaryStage binaryStageWithInputs
  simp only [opSDIV, opAND, opBYTE, opSLT, opSGT, opXOR, opOR,
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
    have tail := mod_inline_safe other reads constructors correct before valid sound left right a b rc debug usizeBits options.forYul rightRead lhs rhs
    split
    next equal =>
      have facts := equal_facts_reliable _ before.read reads sound left right a b lhs rhs equal
      split
      next replacement selected =>
        apply algebraic_selected_safe other constructors correct before valid _ 0 .equal _ left right a b _ debug lhs rhs facts replacement selected
        rfl
      next => cases rc <;> simpa only [pure_bind_action] using tail
    next => cases rc <;> simpa only [pure_bind_action] using tail

theorem binary_mod_miss (reads : Reads) (constructors : Constructors Debug)
    (left right : NodeId) (debug : Debug) (options : Options) (usizeBits : Nat) :
    MissUnchanged (binaryStage reads constructors usizeBits opMOD left right debug options) := by
  unfold binaryStage binaryStageWithInputs
  simp only [opSDIV, opAND, opBYTE, opSLT, opSGT, opXOR, opOR,
    opSIGNEXTEND, opMOD, opSHL, opSHR, opMUL, opDIV, opSUB, Associative.isAssociative,
    Bool.false_eq_true, ↓reduceIte, Bool.false_or, Bool.or_false, Bool.true_or, Bool.or_true,
    List.contains_cons, List.contains_nil, beq_self_eq_true, BitVec.reduceBEq]
  repeat first
    | exact pure_miss_unchanged _
    | exact terminal_miss_unchanged _
    | apply read_miss_unchanged; intro option
    | apply arithmetic_miss_unchanged; intro option
    | split
    | apply never_miss_unchanged
      repeat first
        | exact terminal_never_miss _
        | apply bind_never_miss; intro id

theorem mod_evm_stage (reads : Reads) (constructors : Constructors Debug)
    (arguments : List NodeId) (debug : Debug) (version : Version) (usizeBits : Nat) :
    evmStage reads constructors usizeBits opMOD arguments debug version = pure none := by
  simp only [evmStage, evmStageWithInputs, logicalOperand, opMOD, opBALANCE, opEXP, opMUL, opDIV,
    Bool.false_eq_true, ↓reduceIte, BitVec.reduceBEq]
  repeat first | rfl | split

/-- Complete MOD execution, with table priority, ordered Yul multiplication and
addition candidates, checked predecessor construction, mask fallback and all
revision choices. Recursive constructor preservation remains explicit. -/
theorem mod_simplify_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (simplifyWithOptions reads constructors usizeBits opMOD [left, right] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.mod.value a b 0)) := by
  apply binary_simplify_safe other reads constructors correct before valid sound opMOD left right a b _ 0
    debug options usizeBits lhs rhs rfl
    (binary_mod_safe other reads constructors correct before valid sound left right a b debug options usizeBits lhs rhs)
    (binary_mod_miss reads constructors left right debug options usizeBits)
  intro version _
  rw [mod_evm_stage reads constructors]
  exact Safe.pure _ before none _ valid (by simp)

theorem interner_mod_simplify_safe (other : Meaning) (pushes : Pushes other) (p : Primitives)
    (contracts : Contracts (Folding.wordMeaning other) p) (reads : Reads) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (simplifyWithOptions reads (implementedConstructors p) usizeBits opMOD [left, right] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.mod.value a b 0)) :=
  mod_simplify_safe other reads (implementedConstructors p)
    (implemented_constructors_sound other pushes p contracts) before valid sound
    left right a b debug options usizeBits lhs rhs

end Compiler.Extraction.Dispatch
