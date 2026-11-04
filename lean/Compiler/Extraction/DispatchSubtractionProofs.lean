/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchAlgebraicProofs

namespace Compiler.Extraction.Dispatch
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192

private theorem pure_bind_action (value : α) (next : α → Action β) :
    (pure value >>= next) = next value := rfl

theorem sub_constant_value (a b : Word) : a - b = a + (0 - b) := by
  simp [BitVec.sub_eq_add_neg]

theorem sub_left_add_value (a c b : Word) : (a + c) - b = (a - b) + c := by
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  rw [BitVec.add_comm c (-b)]

theorem sub_right_add_value (a b c : Word) : a - (b + c) = (a - b) + (0 - c) := by
  simp [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.add_assoc]

theorem sub_left_sub_right_value (a c b : Word) : (a - c) - b = (a - b) - c := by
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  rw [BitVec.add_comm (-c) (-b)]

theorem sub_left_sub_left_value (c a b : Word) : (c - a) - b = c - (a + b) :=
  BitVec.sub_sub c a b

theorem sub_right_sub_right_value (a b c : Word) : a - (b - c) = (a - b) + c := by
  simp [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]

theorem sub_right_sub_left_value (a c b : Word) : a - (c - b) = (a + b) + (0 - c) := by
  simp [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]
  rw [BitVec.add_comm (-c) b]

/-- The six nested SUB branches first build a binary expression, then obtain a
constant, then rebuild in the specified operand order. Keep the constant action
explicit: materializing an existing ID and allocating a negation are distinct
source operations. Failures retain the actual intermediate heap. -/
theorem sub_rebuild_safe (other : Meaning) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (first last : Folding.Op) (arity : first.arity = 2)
    (left right : NodeId) (a b constant expected : Word) (debug : Debug)
    (lhs : before.read left = some a) (rhs : before.read right = some b)
    (literal : Action NodeId)
    (literalSafe : ∀ heap, Invariant (Folding.wordMeaning other) heap →
      Safe (Folding.wordMeaning other) literal heap (fun id after => after.read id = some constant))
    (constantFirst : Bool)
    (evaluated : last.eval (if constantFirst then [constant, first.value a b 0]
      else [first.value a b 0, constant]) = some expected) :
    Safe (Folding.wordMeaning other) (do
      let expression ← constructors.operation first.opcode [left, right] debug
      let id ← literal
      return some (← constructors.operation last.opcode
        (if constantFirst then [id, expression] else [expression, id]) debug)) before
      (fun result after => ∀ id, result = some id → after.read id = some expected) := by
  apply Safe.bind _ before _ _ _ _ (correct.operation first [left, right] [a, b] (first.value a b 0) debug before valid
    (by simp [readArguments, lhs, rhs]) (by simp [Folding.Op.eval, arity]))
  intro expression after validAfter _ expressionRead
  apply Safe.bind _ after _ _ _ _ (literalSafe after validAfter)
  intro constantId final validFinal stable constantRead
  apply operation_some_safe other constructors correct final validFinal last _ _ expected debug _ evaluated
  cases constantFirst <;> simp [readArguments, constantRead, stable expression _ expressionRead]

theorem sub_left_add_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug)
    (lhs : before.read left = some a) (rhs : before.read right = some b)
    (next : Action (Option NodeId))
    (rest : Safe (Folding.wordMeaning other) next before
      (fun result after => ∀ id, result = some id → after.read id = some (a - b))) :
    Safe (Folding.wordMeaning other) (do
      if let some nested ← readAction (reads.operation left opADD) then
        if let some parts ← readAction (splitConstant reads nested.items) then
          let difference ← constructors.operation opSUB [parts.expression, right] debug
          return some (← constructors.operation opADD
            [difference, ← constructors.materialize parts.constantExpression parts.value debug] debug)
      next) before (fun result after => ∀ id, result = some id → after.read id = some (a - b)) := by
  apply read_action_bind_safe _ before _ _ _ valid
  intro option lookup
  cases option with
  | none => exact rest
  | some slice =>
    apply read_action_bind_safe _ before _ _ _ valid
    intro option selected
    cases option with
    | none => exact rest
    | some parts =>
      obtain ⟨value, valueRead, nestedRead⟩ := split_value other before.read reads sound .add (Or.inl rfl) left slice parts lookup selected
      have same : a = value + parts.value := Option.some.inj (lhs.symm.trans nestedRead)
      rw [same, sub_left_add_value]
      exact sub_rebuild_safe other constructors correct before valid .sub .add rfl _ right value b parts.value _ debug
        valueRead rhs _ (fun heap valid => correct.materialize _ _ debug heap valid) false rfl

theorem sub_right_add_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug)
    (lhs : before.read left = some a) (rhs : before.read right = some b)
    (next : Action (Option NodeId))
    (rest : Safe (Folding.wordMeaning other) next before
      (fun result after => ∀ id, result = some id → after.read id = some (a - b))) :
    Safe (Folding.wordMeaning other) (do
      if let some nested ← readAction (reads.operation right opADD) then
        if let some parts ← readAction (splitConstant reads nested.items) then
          let difference ← constructors.operation opSUB [left, parts.expression] debug
          return some (← constructors.operation opADD [difference, ← constructors.constant (0 - parts.value) debug] debug)
      next) before (fun result after => ∀ id, result = some id → after.read id = some (a - b)) := by
  apply read_action_bind_safe _ before _ _ _ valid
  intro option lookup
  cases option with
  | none => exact rest
  | some slice =>
    apply read_action_bind_safe _ before _ _ _ valid
    intro option selected
    cases option with
    | none => exact rest
    | some parts =>
      obtain ⟨value, valueRead, nestedRead⟩ := split_value other before.read reads sound .add (Or.inl rfl) right slice parts lookup selected
      have same : b = value + parts.value := Option.some.inj (rhs.symm.trans nestedRead)
      rw [same, sub_right_add_value]
      exact sub_rebuild_safe other constructors correct before valid .sub .add rfl left _ a value (0 - parts.value) _ debug
        lhs valueRead _ (fun heap valid => correct.constant _ debug heap valid) false rfl

theorem sub_left_sub_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug)
    (lhs : before.read left = some a) (rhs : before.read right = some b)
    (next : Action (Option NodeId))
    (rest : Safe (Folding.wordMeaning other) next before
      (fun result after => ∀ id, result = some id → after.read id = some (a - b))) :
    Safe (Folding.wordMeaning other) (do
      if let some nested ← readAction (reads.operation left opSUB) then
        if let [x, y] := nested.items then
          if let some constant ← readAction (reads.constant y) then
            let difference ← constructors.operation opSUB [x, right] debug
            return some (← constructors.operation opSUB [difference, ← constructors.materialize y constant debug] debug)
          if let some constant ← readAction (reads.constant x) then
            let sum ← constructors.operation opADD [y, right] debug
            return some (← constructors.operation opSUB [← constructors.materialize x constant debug, sum] debug)
      next) before (fun result after => ∀ id, result = some id → after.read id = some (a - b)) := by
  apply read_action_bind_safe _ before _ _ _ valid
  intro option lookup
  cases option with
  | none => exact rest
  | some slice =>
    dsimp only
    split
    next xId yId items =>
      obtain ⟨x, y, xRead, yRead, nestedRead⟩ := binary_values other before.read reads sound .sub rfl left xId yId slice lookup items
      have same : a = x - y := Option.some.inj (lhs.symm.trans nestedRead)
      apply read_action_bind_safe _ before _ _ _ valid
      intro option constantRead
      cases option with
      | some constant =>
        have equal : y = constant := Option.some.inj (yRead.symm.trans (sound.constant yId constant constantRead))
        rw [same, equal, sub_left_sub_right_value]
        exact sub_rebuild_safe other constructors correct before valid .sub .sub rfl xId right x b constant _ debug
          xRead rhs _ (fun heap valid => correct.materialize _ _ debug heap valid) false rfl
      | none =>
        apply read_action_bind_safe _ before _ _ _ valid
        intro option constantRead
        cases option with
        | none => exact rest
        | some constant =>
          have equal : x = constant := Option.some.inj (xRead.symm.trans (sound.constant xId constant constantRead))
          rw [same, equal, sub_left_sub_left_value]
          exact sub_rebuild_safe other constructors correct before valid .add .sub rfl yId right y b constant _ debug
            yRead rhs _ (fun heap valid => correct.materialize _ _ debug heap valid) true rfl
    next => exact rest

theorem sub_right_sub_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug)
    (lhs : before.read left = some a) (rhs : before.read right = some b)
    (next : Action (Option NodeId))
    (rest : Safe (Folding.wordMeaning other) next before
      (fun result after => ∀ id, result = some id → after.read id = some (a - b))) :
    Safe (Folding.wordMeaning other) (do
      if let some nested ← readAction (reads.operation right opSUB) then
        if let [x, y] := nested.items then
          if let some constant ← readAction (reads.constant y) then
            let difference ← constructors.operation opSUB [left, x] debug
            return some (← constructors.operation opADD [difference, ← constructors.constant constant debug] debug)
          if let some constant ← readAction (reads.constant x) then
            let sum ← constructors.operation opADD [left, y] debug
            return some (← constructors.operation opADD [sum, ← constructors.constant (0 - constant) debug] debug)
      next) before (fun result after => ∀ id, result = some id → after.read id = some (a - b)) := by
  apply read_action_bind_safe _ before _ _ _ valid
  intro option lookup
  cases option with
  | none => exact rest
  | some slice =>
    dsimp only
    split
    next xId yId items =>
      obtain ⟨x, y, xRead, yRead, nestedRead⟩ := binary_values other before.read reads sound .sub rfl right xId yId slice lookup items
      have same : b = x - y := Option.some.inj (rhs.symm.trans nestedRead)
      apply read_action_bind_safe _ before _ _ _ valid
      intro option constantRead
      cases option with
      | some constant =>
        have equal : y = constant := Option.some.inj (yRead.symm.trans (sound.constant yId constant constantRead))
        rw [same, equal, sub_right_sub_right_value]
        exact sub_rebuild_safe other constructors correct before valid .sub .add rfl left xId a x constant _ debug
          lhs xRead _ (fun heap valid => correct.constant _ debug heap valid) false rfl
      | none =>
        apply read_action_bind_safe _ before _ _ _ valid
        intro option constantRead
        cases option with
        | none => exact rest
        | some constant =>
          have equal : x = constant := Option.some.inj (xRead.symm.trans (sound.constant xId constant constantRead))
          rw [same, equal, sub_right_sub_left_value]
          exact sub_rebuild_safe other constructors correct before valid .add .add rfl left yId a y (0 - constant) _ debug
            lhs yRead _ (fun heap valid => correct.constant _ debug heap valid) false rfl
    next => exact rest

theorem sub_inline_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (known : Option Word) (debug : Debug)
    (lookup : reads.constant right = .ok known)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (do
      if let some constant := known then
        return some (← constructors.operation opADD [left, ← constructors.constant (0 - constant) debug] debug)
      if let some nested ← readAction (reads.operation left opADD) then
        if let some parts ← readAction (splitConstant reads nested.items) then
          let difference ← constructors.operation opSUB [parts.expression, right] debug
          return some (← constructors.operation opADD
            [difference, ← constructors.materialize parts.constantExpression parts.value debug] debug)
      if let some nested ← readAction (reads.operation right opADD) then
        if let some parts ← readAction (splitConstant reads nested.items) then
          let difference ← constructors.operation opSUB [left, parts.expression] debug
          return some (← constructors.operation opADD [difference, ← constructors.constant (0 - parts.value) debug] debug)
      if let some nested ← readAction (reads.operation left opSUB) then
        if let [a, b] := nested.items then
          if let some constant ← readAction (reads.constant b) then
            let difference ← constructors.operation opSUB [a, right] debug
            return some (← constructors.operation opSUB [difference, ← constructors.materialize b constant debug] debug)
          if let some constant ← readAction (reads.constant a) then
            let sum ← constructors.operation opADD [b, right] debug
            return some (← constructors.operation opSUB [← constructors.materialize a constant debug, sum] debug)
      if let some nested ← readAction (reads.operation right opSUB) then
        if let [a, b] := nested.items then
          if let some constant ← readAction (reads.constant b) then
            let difference ← constructors.operation opSUB [left, a] debug
            return some (← constructors.operation opADD [difference, ← constructors.constant constant debug] debug)
          if let some constant ← readAction (reads.constant a) then
            let sum ← constructors.operation opADD [left, b] debug
            return some (← constructors.operation opADD [sum, ← constructors.constant (0 - constant) debug] debug)
      return none) before (fun result after => ∀ id, result = some id → after.read id = some (a - b)) := by
  cases known with
  | some constant =>
    have same : b = constant := Option.some.inj (rhs.symm.trans (sound.constant right constant lookup))
    rw [same, sub_constant_value]
    apply Safe.bind _ before _ _ _ _ (correct.constant (0 - constant) debug before valid)
    intro constantId after validAfter stable constantRead
    exact operation_some_safe other constructors correct after validAfter .add [left, constantId] [a, 0 - constant] _ debug
      (by simp [readArguments, constantRead, stable left a lhs]) rfl
  | none =>
    apply sub_left_add_safe other reads constructors correct before valid sound left right a b debug lhs rhs
    apply sub_right_add_safe other reads constructors correct before valid sound left right a b debug lhs rhs
    apply sub_left_sub_safe other reads constructors correct before valid sound left right a b debug lhs rhs
    apply sub_right_sub_safe other reads constructors correct before valid sound left right a b debug lhs rhs
    exact Safe.pure _ before none _ valid (by simp)

theorem binary_sub_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (binaryStage reads constructors usizeBits opSUB left right debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.sub.value a b 0)) := by
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
    have tail := sub_inline_safe other reads constructors correct before valid sound left right a b rc debug rightRead lhs rhs
    split
    next equal =>
      have facts := equal_facts_reliable _ before.read reads sound left right a b lhs rhs equal
      split
      next replacement selected =>
        apply algebraic_selected_safe other constructors correct before valid _ 0 .equal _ left right a b _ debug lhs rhs facts replacement selected
        rfl
      next => cases rc <;> simpa only [pure_bind_action] using tail
    next => cases rc <;> simpa only [pure_bind_action] using tail

theorem binary_sub_miss (reads : Reads) (constructors : Constructors Debug)
    (left right : NodeId) (debug : Debug) (options : Options) (usizeBits : Nat) :
    MissUnchanged (binaryStage reads constructors usizeBits opSUB left right debug options) := by
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

theorem sub_evm_stage (reads : Reads) (constructors : Constructors Debug)
    (arguments : List NodeId) (debug : Debug) (version : Version) (usizeBits : Nat) :
    evmStage reads constructors usizeBits opSUB arguments debug version = pure none := by
  simp only [evmStage, evmStageWithInputs, logicalOperand, opSUB, opBALANCE, opEXP, opMUL, opDIV,
    Bool.false_eq_true, ↓reduceIte, BitVec.reduceBEq]
  repeat first | rfl | split

/-- Complete SUB dispatch: folding and table rules precede the seven inline
rewrites. Recursive constructor preservation and read coherence remain explicit. -/
theorem sub_simplify_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (simplifyWithOptions reads constructors usizeBits opSUB [left, right] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.sub.value a b 0)) := by
  apply binary_simplify_safe other reads constructors correct before valid sound opSUB left right a b _ 0
    debug options usizeBits lhs rhs rfl
    (binary_sub_safe other reads constructors correct before valid sound left right a b debug options usizeBits lhs rhs)
    (binary_sub_miss reads constructors left right debug options usizeBits)
  intro version _
  rw [sub_evm_stage reads constructors]
  exact Safe.pure _ before none _ valid (by simp)

theorem interner_sub_simplify_safe (other : Meaning) (pushes : Pushes other) (p : Primitives)
    (contracts : Contracts (Folding.wordMeaning other) p) (reads : Reads) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (simplifyWithOptions reads (implementedConstructors p) usizeBits opSUB [left, right] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (Folding.Op.sub.value a b 0)) :=
  sub_simplify_safe other reads (implementedConstructors p)
    (implemented_constructors_sound other pushes p contracts) before valid sound
    left right a b debug options usizeBits lhs rhs

end Compiler.Extraction.Dispatch
