/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchAssociativeProofs

namespace Compiler.Extraction.Dispatch
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096

private theorem pure_bind_action (value : α) (next : α → Action β) :
    (pure value >>= next) = next value := rfl

theorem shift_product_miss (reads : Reads) (build : OperationBuilder Debug)
    (value shiftId : NodeId) (debug : Debug) :
    MissUnchanged (ShiftMasks.powerOfTwoShiftProduct reads build value shiftId debug) := by
  unfold ShiftMasks.powerOfTwoShiftProduct
  repeat first
    | exact pure_miss_unchanged _
    | exact terminal_miss_unchanged _
    | apply read_miss_unchanged; intro option
    | split

theorem shift_product_pair_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (do
      if let some id ← ShiftMasks.powerOfTwoShiftProduct reads constructors.operation left right debug then return some id
      if let some id ← ShiftMasks.powerOfTwoShiftProduct reads constructors.operation right left debug then return some id
      return none) before (fun result after => ∀ id, result = some id → after.read id = some (a * b)) := by
  apply optional_bind_safe_of_unchanged _ _ _ before _
    (ShiftMasks.shift_product_safe other reads constructors.operation correct.operation before valid sound left right a b debug lhs rhs)
    (shift_product_miss reads constructors.operation left right debug)
  · intro id; rfl
  · apply optional_bind_safe_of_unchanged _ _ _ before _
      (by simpa only [BitVec.mul_comm b a] using
        ShiftMasks.shift_product_safe other reads constructors.operation correct.operation before valid sound right left b a debug rhs lhs)
      (shift_product_miss reads constructors.operation right left debug)
    · intro id; rfl
    · exact Safe.pure _ before none _ valid (by simp)

theorem binary_mul_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (binaryStage reads constructors usizeBits opMUL left right debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (a * b)) := by
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
    have tail := reassociation_pair_safe other reads constructors correct before valid sound .mul (Or.inr (Or.inl rfl))
      left right a b debug lhs rhs _ (shift_product_pair_safe other reads constructors correct before valid sound left right a b debug lhs rhs)
    split
    next equal =>
      have facts := equal_facts_reliable _ before.read reads sound left right a b lhs rhs equal
      split
      next replacement selected =>
        apply algebraic_selected_safe other constructors correct before valid _ 0 .equal _ left right a b _ debug lhs rhs facts replacement selected
        rfl
      next => simpa only [Folding.Op.opcode, Folding.Op.value, pure_bind_action] using tail
    next => simpa only [Folding.Op.opcode, Folding.Op.value, pure_bind_action] using tail

theorem binary_mul_miss (reads : Reads) (constructors : Constructors Debug)
    (left right : NodeId) (debug : Debug) (options : Options) (usizeBits : Nat) :
    MissUnchanged (binaryStage reads constructors usizeBits opMUL left right debug options) := by
  unfold binaryStage binaryStageWithInputs
  simp only [opSDIV, opAND, opBYTE, opSLT, opSGT, opXOR, opOR,
    opSIGNEXTEND, opMOD, opSHL, opSHR, opMUL, opDIV, opSUB, Associative.isAssociative,
    Bool.false_eq_true, ↓reduceIte, Bool.false_or, Bool.or_false, Bool.true_or, Bool.or_true,
    List.contains_cons, List.contains_nil, beq_self_eq_true, BitVec.reduceBEq]
  repeat first
    | exact pure_miss_unchanged _
    | exact terminal_miss_unchanged _
    | apply read_miss_unchanged; intro option
    | intro id; rfl
    | apply optional_bind_miss_unchanged _ _ (reassociate_miss reads constructors _ _ _ _ debug)
    | apply optional_bind_miss_unchanged _ _ (shift_product_miss reads constructors.operation _ _ debug)
    | split

theorem binary_log_mul_value (usizeBits : Nat) (constant : Word) (power : Nat) (value : Word)
    (found : BinaryLogarithm.binaryLogarithm usizeBits constant = .ok (some power)) :
    constant * value = Folding.Op.shl.value (BitVec.ofNat 256 power) value 0 := by
  rw [BitVec.mul_comm constant value, ← BinaryLogarithm.found_shift_value usizeBits constant power found]
  exact ShiftMasks.power_shift_value _ _

/-- The power literal is allocated before its use by SHL. All failures retain
the real intermediate heap, including failure of the second constructor. -/
theorem constant_shift_some_safe (other : Meaning) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (amount value : Word) (operand : NodeId) (debug : Debug)
    (actual : before.read operand = some value) :
    Safe (Folding.wordMeaning other) (do
      return some (← constructors.operation opSHL [← constructors.constant amount debug, operand] debug)) before
      (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.shl.value amount value 0)) :=
  constant_left_operation_some_safe other constructors correct before valid .shl amount value _ operand debug actual rfl

theorem mul_power_candidate_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (constantId operand : NodeId) (a b : Word) (debug : Debug) (usizeBits : Nat)
    (lhs : before.read constantId = some a) (rhs : before.read operand = some b)
    (next : Action (Option NodeId))
    (rest : Safe (Folding.wordMeaning other) next before
      (fun result after => ∀ id, result = some id → after.read id = some (a * b))) :
    Safe (Folding.wordMeaning other) (do
      if let some constant ← readAction (reads.constant constantId) then
        if let some power ← arithmetic (BinaryLogarithm.binaryLogarithm usizeBits constant) then
          return some (← constructors.operation opSHL [← constructors.constant (BitVec.ofNat 256 power) debug, operand] debug)
      next) before (fun result after => ∀ id, result = some id → after.read id = some (a * b)) := by
  apply read_action_bind_safe _ before _ _ _ valid
  intro option lookup
  cases option with
  | none => exact rest
  | some constant =>
    apply arithmetic_bind_safe _ before _ _ _ valid
    intro option found
    cases option with
    | none => exact rest
    | some power =>
      have same : a = constant := Option.some.inj (lhs.symm.trans (sound.constant constantId constant lookup))
      rw [same, binary_log_mul_value usizeBits constant power b found]
      exact constant_shift_some_safe other constructors correct before valid _ b operand debug rhs

theorem mul_evm_stage_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (version : Version) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (evmStage reads constructors usizeBits opMUL [left, right] debug version) before
      (fun result after => ∀ id, result = some id → after.read id = some (a * b)) := by
  simp only [evmStage, evmStageWithInputs, logicalOperand, shiftInput_some, opMUL, opBALANCE, opEXP, opDIV,
    Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, BitVec.reduceBEq]
  by_cases enabled : hasBitwiseShifting version = true
  · simp only [enabled, ↓reduceIte]
    apply mul_power_candidate_safe other reads constructors correct before valid sound left right a b debug usizeBits lhs rhs
    have rest := mul_power_candidate_safe other reads constructors correct before valid sound right left b a debug usizeBits rhs lhs
      (pure none) (Safe.pure _ before none _ valid (by simp))
    simpa only [BitVec.mul_comm b a, pure_bind_action] using rest
  · simp only [enabled, ↓reduceIte]
    exact Safe.pure _ before none _ valid (by simp)

theorem mul_evm_miss (reads : Reads) (constructors : Constructors Debug)
    (left right : NodeId) (debug : Debug) (version : Version) (usizeBits : Nat) :
    MissUnchanged (evmStage reads constructors usizeBits opMUL [left, right] debug version) := by
  simp only [evmStage, evmStageWithInputs, logicalOperand, shiftInput_some, opMUL, opBALANCE, opEXP, opDIV,
    Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, BitVec.reduceBEq]
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

/-- The full MUL path includes constant/table priority, both reassociation and
shift-product candidates, and the actual revision-gated power-of-two rules.
There is no host-width lower-bound assumption: checked native faults remain
failures and every successful logarithm result has a proved meaning. -/
theorem mul_simplify_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (simplifyWithOptions reads constructors usizeBits opMUL [left, right] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (a * b)) := by
  apply binary_simplify_safe other reads constructors correct before valid sound opMUL left right a b _ 0
    debug options usizeBits lhs rhs rfl
    (binary_mul_safe other reads constructors correct before valid sound left right a b debug options usizeBits lhs rhs)
    (binary_mul_miss reads constructors left right debug options usizeBits)
  intro version _
  exact mul_evm_stage_safe other reads constructors correct before valid sound left right a b debug version usizeBits lhs rhs

theorem interner_mul_simplify_safe (other : Meaning) (pushes : Pushes other) (p : Primitives)
    (contracts : Contracts (Folding.wordMeaning other) p) (reads : Reads) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (simplifyWithOptions reads (implementedConstructors p) usizeBits opMUL [left, right] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (a * b)) :=
  mul_simplify_safe other reads (implementedConstructors p)
    (implemented_constructors_sound other pushes p contracts) before valid sound
    left right a b debug options usizeBits lhs rhs

end Compiler.Extraction.Dispatch
