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

namespace Preservation

/-- The queried SHL slice supplies the actual indexed initializer load. Its
reached state, preserved reads and errors are passed to the SHR child proof. -/
theorem shift_divisor_safe {State Failure Debug : Type} [MonadLift (Except Error) (Effect State Failure)]
    (logic : BuilderLogic (Effect State Failure) State) (rules : ReadRules logic)
    (other : Meaning) (reads : Reads) (constructors : Constructors Debug (Effect State Failure))
    (before : State) (valid : logic.valid before)
    (sound : Sound (Folding.wordMeaning other) (logic.read before) reads)
    (left right : NodeId) (a b : Word) (debug : Debug)
    (shift : OperationRule logic constructors debug .shr)
    (operand : OperandRead (Effect State Failure))
    (inputs : UnaryPreservation.Inputs logic reads operand before)
    (lhs : (logic.read before) left = some a) (rhs : (logic.read before) right = some b) :
    logic.safe (do
      if let some shift ← readAction (reads.operation right opSHL) then
        if let [amount, base] := shift.items then
          if (← readAction (reads.constant base)) == some 1 then
            return some (← constructors.operation opSHR [← operand shift 0 amount, left] debug)
      return none) before (fun result after => ∀ id, result = some id → logic.read after id = some (a / b)) := by
  apply rules.bind before _ _ _ valid
  intro option lookup
  cases option with
  | none => exact logic.pure before none _ valid (by simp)
  | some slice =>
    dsimp only
    split
    next amountId baseId items =>
      apply rules.bind before _ _ _ valid
      intro constant found
      by_cases one : constant = some (1 : Word)
      · subst constant
        simp only [beq_self_eq_true, ↓reduceIte]
        obtain ⟨amount, base, amountRead, baseRead, shiftedFact⟩ := binary_values other (logic.read before) reads sound .shl
          rfl right amountId baseId slice lookup items
        have baseOne : base = 1 := Option.some.inj (baseRead.symm.trans (sound.constant baseId 1 found))
        subst base
        have same : b = Folding.Op.shl.value amount 1 0 := Option.some.inj (rhs.symm.trans shiftedFact)
        rw [same]
        change logic.safe _ before (fun result after => ∀ id, result = some id →
          logic.read after id = some (Folding.Op.div.value a (Folding.Op.shl.value amount 1 0) 0))
        rw [ShiftMasks.divisor_shift_value]
        apply logic.bind before _ _ _ _ (inputs right opSHL slice lookup 0 amountId (by simp [items]))
        intro loaded after validAfter stable actual
        subst loaded
        exact UnaryPreservation.some_safe logic _ after _
          (shift [amountId, left] [amount, a] _ after validAfter
            (by simp [readArguments, stable _ _ amountRead, stable _ _ lhs]) rfl)
      · have different : (constant == some (1 : Word)) = false := by simpa using one
        simp only [different, Bool.false_eq_true, ↓reduceIte]
        exact logic.pure before none _ valid (by simp)
    next => exact logic.pure before none _ valid (by simp)

theorem binary_div_safe {State Failure Debug : Type} [MonadLift (Except Error) (Effect State Failure)]
    (logic : BuilderLogic (Effect State Failure) State) (rules : ReadRules logic)
    (other : Meaning) (reads : Reads) (constructors : Constructors Debug (Effect State Failure))
    (debug : Debug) (correct : BuilderRules logic (algebraicBuilder constructors) debug)
    (shift : OperationRule logic constructors debug .shr)
    (before : State) (valid : logic.valid before)
    (sound : Sound (Folding.wordMeaning other) (logic.read before) reads)
    (left right : NodeId) (a b : Word) (options : Options) (usizeBits : Nat)
    (operand : OperandRead (Effect State Failure))
    (inputs : UnaryPreservation.Inputs logic reads operand before)
    (lhs : (logic.read before) left = some a) (rhs : (logic.read before) right = some b) :
    logic.safe (binaryStageWithInputs reads constructors usizeBits opDIV left right debug options operand) before
      (fun result after => ∀ id, result = some id → logic.read after id = some (a / b)) := by
  unfold binaryStageWithInputs
  simp only [opSDIV, opAND, opBYTE, opSLT, opSGT, opXOR, opOR,
    opSIGNEXTEND, opMOD, opSHL, opSHR, opMUL, opDIV, opSUB, Associative.isAssociative,
    Bool.false_eq_true, ↓reduceIte, Bool.false_or, Bool.or_false, Bool.true_or, Bool.or_true,
    List.contains_cons, List.contains_nil, beq_self_eq_true, BitVec.reduceBEq]
  apply rules.bind before _ _ _ valid
  intro lc leftRead
  apply rules.bind before _ _ _ valid
  intro rc rightRead
  have reliable := constant_facts_reliable _ (logic.read before) reads sound left right a b lhs rhs lc rc leftRead rightRead
  split
  next replacement selected =>
    apply algebraic_selected_safe logic other constructors debug correct before valid _ 0 .constants _ left right a b _ lhs rhs reliable replacement selected
    rfl
  next =>
    split
    next equal =>
      have facts := equal_facts_reliable _ (logic.read before) reads sound left right a b lhs rhs equal
      split
      next replacement selected =>
        apply algebraic_selected_safe logic other constructors debug correct before valid _ 0 .equal _ left right a b _ lhs rhs facts replacement selected
        rfl
      next => exact shift_divisor_safe logic rules other reads constructors before valid sound left right a b debug shift operand inputs lhs rhs
    next => exact shift_divisor_safe logic rules other reads constructors before valid sound left right a b debug shift operand inputs lhs rhs

end Preservation

theorem shift_divisor_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (do
      if let some shift ← readAction (reads.operation right opSHL) then
        if let [amount, base] := shift.items then
          if (← readAction (reads.constant base)) == some 1 then
            return some (← constructors.operation opSHR [amount, left] debug)
      return none) before (fun result after => ∀ id, result = some id → after.read id = some (a / b)) := by
  exact Preservation.shift_divisor_safe (Interner.builderLogic (Folding.wordMeaning other))
    (Preservation.logicalReadRules _) other reads constructors before valid sound left right a b debug
    (fun ids values value state invariant actual evaluated =>
      correct.operation .shr ids values value debug state invariant actual evaluated)
    logicalOperand (UnaryPreservation.logicalInputs _ reads before valid) lhs rhs

theorem binary_div_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (binaryStage reads constructors usizeBits opDIV left right debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (a / b)) := by
  exact Preservation.binary_div_safe (Interner.builderLogic (Folding.wordMeaning other))
    (Preservation.logicalReadRules _) other reads constructors debug
    (Preservation.logicalBuilderRules other constructors correct debug)
    (fun ids values value state invariant actual evaluated =>
      correct.operation .shr ids values value debug state invariant actual evaluated)
    before valid sound left right a b options usizeBits logicalOperand
    (UnaryPreservation.logicalInputs _ reads before valid) lhs rhs

theorem binary_div_miss (reads : Reads) (constructors : Constructors Debug)
    (left right : NodeId) (debug : Debug) (options : Options) (usizeBits : Nat) :
    MissUnchanged (binaryStage reads constructors usizeBits opDIV left right debug options) := by
  unfold binaryStage binaryStageWithInputs
  simp only [opSDIV, opAND, opBYTE, opSLT, opSGT, opXOR, opOR,
    opSIGNEXTEND, opMOD, opSHL, opSHR, opMUL, opDIV, opSUB, Associative.isAssociative,
    Bool.false_eq_true, ↓reduceIte, Bool.false_or, Bool.or_false, Bool.true_or, Bool.or_true,
    List.contains_cons, List.contains_nil, beq_self_eq_true, BitVec.reduceBEq]
  repeat first
    | exact pure_miss_unchanged _
    | exact terminal_miss_unchanged _
    | apply read_miss_unchanged; intro option
    | split

theorem binary_log_div_value (usizeBits : Nat) (constant : Word) (power : Nat) (value : Word)
    (found : BinaryLogarithm.binaryLogarithm usizeBits constant = .ok (some power)) :
    value / constant = Folding.Op.shr.value (BitVec.ofNat 256 power) value 0 := by
  rw [← BinaryLogarithm.found_shift_value usizeBits constant power found]
  exact ShiftMasks.divisor_shift_value _ _

theorem div_evm_stage_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (version : Version) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (evmStage reads constructors usizeBits opDIV [left, right] debug version) before
      (fun result after => ∀ id, result = some id → after.read id = some (a / b)) := by
  simp only [evmStage, evmStageWithInputs, logicalOperand, shiftInput_some, opMUL, opBALANCE, opEXP, opDIV,
    Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, BitVec.reduceBEq]
  by_cases enabled : hasBitwiseShifting version = true
  · simp only [enabled, ↓reduceIte]
    apply read_action_bind_safe _ before _ _ _ valid
    intro option lookup
    cases option with
    | none => exact Safe.pure _ before none _ valid (by simp)
    | some constant =>
      apply arithmetic_bind_safe _ before _ _ _ valid
      intro option found
      cases option with
      | none => exact Safe.pure _ before none _ valid (by simp)
      | some power =>
        have same : b = constant := Option.some.inj (rhs.symm.trans (sound.constant right constant lookup))
        rw [same, binary_log_div_value usizeBits constant power a found]
        exact constant_left_operation_some_safe other constructors correct before valid
          .shr (BitVec.ofNat 256 power) a _ left debug lhs rfl
  · simp only [enabled, ↓reduceIte]
    exact Safe.pure _ before none _ valid (by simp)

theorem div_evm_miss (reads : Reads) (constructors : Constructors Debug)
    (left right : NodeId) (debug : Debug) (version : Version) (usizeBits : Nat) :
    MissUnchanged (evmStage reads constructors usizeBits opDIV [left, right] debug version) := by
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

/-- Complete ordered DIV execution, including zero divisors, arbitrarily large
shift words, revision gates, checked host-width faults and constructor failures.
Recursive constructor preservation remains an explicit hypothesis. -/
theorem div_simplify_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (simplifyWithOptions reads constructors usizeBits opDIV [left, right] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (a / b)) := by
  apply binary_simplify_safe other reads constructors correct before valid sound opDIV left right a b _ 0
    debug options usizeBits lhs rhs rfl
    (binary_div_safe other reads constructors correct before valid sound left right a b debug options usizeBits lhs rhs)
    (binary_div_miss reads constructors left right debug options usizeBits)
  intro version _
  exact div_evm_stage_safe other reads constructors correct before valid sound left right a b debug version usizeBits lhs rhs

theorem interner_div_simplify_safe (other : Meaning) (pushes : Pushes other) (p : Primitives)
    (contracts : Contracts (Folding.wordMeaning other) p) (reads : Reads) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (simplifyWithOptions reads (implementedConstructors p) usizeBits opDIV [left, right] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (a / b)) :=
  div_simplify_safe other reads (implementedConstructors p)
    (implemented_constructors_sound other pushes p contracts) before valid sound
    left right a b debug options usizeBits lhs rhs

end Compiler.Extraction.Dispatch
