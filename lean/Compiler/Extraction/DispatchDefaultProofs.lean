/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchWordProofs

namespace Compiler.Extraction.Dispatch
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem nonword_opcode (instruction : Opcode) (unknown : Folding.decodeWord instruction = none)
    (op : Folding.Op) : instruction ≠ op.opcode := by
  intro equal
  rw [equal, Folding.decode_word_opcode] at unknown
  contradiction

theorem nonword_table (instruction : Opcode) (unknown : Folding.decodeWord instruction = none)
    (stage : Stage) (facts : Facts) : zigSelect instruction stage facts = none := by
  apply zigSelectFrom_unknown
  intro rule _ same
  exact nonword_opcode instruction unknown (binaryWordOp rule.op)
    (same.symm.trans (binary_word_opcode rule.op).symm)

/-- Unknown binary instructions still perform both constant reads, in order.
They never call a constructor; read faults are not silently turned into misses. -/
theorem nonword_binary (reads : Reads) (constructors : Constructors Debug)
    (usizeBits : Nat) (instruction : Opcode) (left right : NodeId) (debug : Debug) (options : Options)
    (unknown : Folding.decodeWord instruction = none) :
    binaryStage reads constructors usizeBits instruction left right debug options = (do
      let _ ← readAction (reads.constant left)
      let _ ← readAction (reads.constant right)
      return none) := by
  have absent (op : Folding.Op) : (instruction == op.opcode) = false := by
    exact beq_eq_false_iff_ne.mpr (nonword_opcode instruction unknown op)
  have notAdd := absent .add
  have notMul := absent .mul
  have notSub := absent .sub
  have notDiv := absent .div
  have notSdiv := absent .sdiv
  have notMod := absent .mod
  have notByte := absent .byte
  have notSlt := absent .slt
  have notSgt := absent .sgt
  have notAnd := absent .and
  have notOr := absent .or
  have notXor := absent .xor
  have notSignextend := absent .signextend
  have notShl := absent .shl
  have notShr := absent .shr
  simp only [Folding.Op.opcode] at notAdd notMul notSub notDiv notSdiv notMod notByte
  simp only [Folding.Op.opcode] at notSlt notSgt notAnd notOr notXor notSignextend notShl notShr
  simp only [binaryStage, binaryStageWithInputs, nonword_table instruction unknown, opSDIV, opAND, opBYTE, opSLT, opSGT,
    opXOR, opOR, opSIGNEXTEND, opMOD, opSHL, opSHR, opMUL, opDIV, opSUB,
    Associative.isAssociative, notAdd, notMul, notSub, notDiv, notSdiv, notMod, notByte,
    notSlt, notSgt, notAnd, notOr, notXor, notSignextend, notShl, notShr,
    List.contains_cons, List.contains_nil, beq_iff_eq, Bool.false_or, Bool.or_false,
    Bool.false_eq_true, ↓reduceIte]
  repeat first | rfl | split

theorem nonword_unary (reads : Reads) (constructors : Constructors Debug)
    (instruction : Opcode) (operand : NodeId) (debug : Debug)
    (unknown : Folding.decodeWord instruction = none) :
    unaryStage reads constructors instruction operand debug = pure none := by
  have notNot := nonword_opcode instruction unknown .not
  have notIszero := nonword_opcode instruction unknown .iszero
  simp only [Folding.Op.opcode] at notNot notIszero
  simp only [unaryStage, unaryStageWithInputs, opNOT, opISZERO, beq_iff_eq, notNot, notIszero, ↓reduceIte]
  rfl

theorem nonword_evm_stage (reads : Reads) (constructors : Constructors Debug)
    (usizeBits : Nat) (instruction : Opcode) (arguments : List NodeId) (debug : Debug) (version : Version)
    (unknown : Folding.decodeWord instruction = none) (notBalance : instruction ≠ opBALANCE) :
    evmStage reads constructors usizeBits instruction arguments debug version = pure none := by
  have balance : (instruction == opBALANCE) = false := beq_eq_false_iff_ne.mpr notBalance
  have exponent : (instruction == opEXP) = false := beq_eq_false_iff_ne.mpr (nonword_opcode instruction unknown .exp)
  have mul : (instruction == opMUL) = false := beq_eq_false_iff_ne.mpr (nonword_opcode instruction unknown .mul)
  have div : (instruction == opDIV) = false := beq_eq_false_iff_ne.mpr (nonword_opcode instruction unknown .div)
  simp only [evmStage, evmStageWithInputs, logicalOperand, balance, exponent, mul, div, Bool.false_eq_true, ↓reduceIte]
  repeat first | rfl | split

theorem nonword_constant_safe (meaning : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (instruction : Opcode) (arguments : List NodeId) (debug : Debug)
    (unknown : Folding.decodeWord instruction = none) (before : Heap) (valid : Invariant meaning before)
    (expected : Word) :
    Safe meaning (constantStage reads constructors instruction arguments debug) before
      (fun result after => ∀ id, result = some id → after.read id = some expected) := by
  unfold constantStage
  split
  · exact Safe.pure _ before none _ valid (by simp)
  · apply read_action_bind_safe _ before _ _ _ valid
    intro option _
    cases option with
    | none => exact Safe.pure _ before none _ valid (by simp)
    | some values =>
      dsimp only
      rw [Folding.folding_unknown instruction values (nonword_opcode instruction unknown)]
      exact Safe.pure _ before none _ valid (by simp)

theorem nonword_binary_safe (meaning : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (usizeBits : Nat) (instruction : Opcode) (left right : NodeId) (debug : Debug) (options : Options)
    (unknown : Folding.decodeWord instruction = none) (before : Heap) (valid : Invariant meaning before)
    (expected : Word) :
    Safe meaning (binaryStage reads constructors usizeBits instruction left right debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some expected) := by
  rw [nonword_binary reads constructors usizeBits instruction left right debug options unknown]
  apply read_action_bind_safe _ before _ _ _ valid
  intro _ _
  apply read_action_bind_safe _ before _ _ _ valid
  intro _ _
  exact Safe.pure _ before none _ valid (by simp)

theorem nonword_binary_miss (reads : Reads) (constructors : Constructors Debug)
    (usizeBits : Nat) (instruction : Opcode) (left right : NodeId) (debug : Debug) (options : Options)
    (unknown : Folding.decodeWord instruction = none) :
    MissUnchanged (binaryStage reads constructors usizeBits instruction left right debug options) := by
  rw [nonword_binary reads constructors usizeBits instruction left right debug options unknown]
  apply read_miss_unchanged
  intro _
  apply read_miss_unchanged
  intro _
  exact pure_miss_unchanged none

/-- All non-word instructions miss normally or preserve a read fault, unless
the caller enables the account-specific BALANCE revision rule. This does not
need a denotation or constructor hypothesis because no replacement is built. -/
theorem nonword_simplify_safe (meaning : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (usizeBits : Nat) (instruction : Opcode) (arguments : List NodeId) (debug : Debug) (options : Options)
    (unknown : Folding.decodeWord instruction = none)
    (noBalanceRule : options.evmVersion = none ∨ instruction ≠ opBALANCE)
    (before : Heap) (valid : Invariant meaning before) (expected : Word) :
    Safe meaning (simplifyWithOptions reads constructors usizeBits instruction arguments debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some expected) := by
  have revision (arguments : List NodeId) : Safe meaning (match options.evmVersion with
      | some version => evmStage reads constructors usizeBits instruction arguments debug version
      | none => pure none) before
      (fun result after => ∀ id, result = some id → after.read id = some expected) := by
    cases chosen : options.evmVersion with
    | none => exact Safe.pure _ before none _ valid (by simp)
    | some version =>
      have notBalance : instruction ≠ opBALANCE := noBalanceRule.resolve_left (by simp [chosen])
      dsimp only
      rw [nonword_evm_stage reads constructors usizeBits instruction arguments debug version unknown notBalance]
      exact Safe.pure _ before none _ valid (by simp)
  have unary : Safe meaning (orNext (match arguments with
      | [value] => unaryStage reads constructors instruction value debug
      | _ => pure none) (match options.evmVersion with
      | some version => evmStage reads constructors usizeBits instruction arguments debug version
      | none => pure none)) before
      (fun result after => ∀ id, result = some id → after.read id = some expected) := by
    split
    · rw [nonword_unary reads constructors instruction _ debug unknown]
      exact revision _
    · exact revision _
  unfold simplifyWithOptions simplifyOptionsWithInputs
  apply or_next_safe_of_unchanged _ _ _ before _
    (nonword_constant_safe meaning reads constructors instruction arguments debug unknown before valid expected)
    (constant_stage_miss reads constructors instruction arguments debug)
  apply or_next_safe_of_unchanged _ _ _ before _ _ _ unary
  · split
    · exact nonword_binary_safe meaning reads constructors usizeBits instruction _ _ debug options unknown before valid expected
    · exact Safe.pure _ before none _ valid (by simp)
  · split
    · exact nonword_binary_miss reads constructors usizeBits instruction _ _ debug options unknown
    · exact pure_miss_unchanged none

/-- Every opcode byte and every defined application, with the account-specific
revision rule explicitly disabled or excluded. Other revision rules are covered
by the word theorem; their execution order is unchanged. -/
theorem simplify_without_balance_safe (env : AddressMask.Environment) (other : Meaning)
    (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound (wordBaseMeaning env other) constructors)
    (addressCorrect : AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) constructors.operation)
    (sarCorrect : ArithmeticShift.Constructs (AddressMask.addressMeaning env other) constructors.operation)
    (before : Heap) (valid : Invariant (wordDispatchMeaning env other) before)
    (sound : Sound (wordDispatchMeaning env other) before.read reads)
    (instruction : Opcode) (arguments : List NodeId) (values : List Word) (expected : Word) (sequence : BitVec 32)
    (debug : Debug) (options : Options) (usizeBits : Nat)
    (noBalanceRule : options.evmVersion = none ∨ instruction ≠ opBALANCE)
    (actual : readArguments before.read arguments = some values)
    (evaluated : (wordDispatchMeaning env other).operation instruction sequence values = some expected) :
    Safe (wordDispatchMeaning env other)
      (simplifyWithOptions reads constructors usizeBits instruction arguments debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some expected) := by
  cases decoded : Folding.decodeWord instruction with
  | none =>
    exact nonword_simplify_safe _ reads constructors usizeBits instruction arguments debug options
      decoded noBalanceRule before valid expected
  | some op =>
    exact decoded_word_simplify_safe env other reads constructors correct addressCorrect sarCorrect
      before valid sound instruction op decoded arguments values expected sequence debug options usizeBits actual evaluated

/-- The actual libevmasm entry point has no revision tail. This theorem has no
opcode exclusion, and account/storage/memory epochs retain their original model. -/
theorem default_simplify_safe (env : AddressMask.Environment) (other : Meaning)
    (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound (wordBaseMeaning env other) constructors)
    (addressCorrect : AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) constructors.operation)
    (sarCorrect : ArithmeticShift.Constructs (AddressMask.addressMeaning env other) constructors.operation)
    (before : Heap) (valid : Invariant (wordDispatchMeaning env other) before)
    (sound : Sound (wordDispatchMeaning env other) before.read reads)
    (instruction : Opcode) (arguments : List NodeId) (values : List Word) (expected : Word) (sequence : BitVec 32)
    (debug : Debug) (usizeBits : Nat)
    (actual : readArguments before.read arguments = some values)
    (evaluated : (wordDispatchMeaning env other).operation instruction sequence values = some expected) :
    Safe (wordDispatchMeaning env other)
      (simplify reads constructors usizeBits instruction arguments debug) before
      (fun result after => ∀ id, result = some id → after.read id = some expected) :=
  simplify_without_balance_safe env other reads constructors correct addressCorrect sarCorrect before valid sound
    instruction arguments values expected sequence debug defaultOptions usizeBits (Or.inl rfl) actual evaluated

theorem interner_default_simplify_safe (env : AddressMask.Environment) (other : Meaning)
    (pushes : Pushes other) (p : Primitives) (contracts : Contracts (wordDispatchMeaning env other) p)
    (reads : Reads) (before : Heap) (valid : Invariant (wordDispatchMeaning env other) before)
    (sound : Sound (wordDispatchMeaning env other) before.read reads)
    (instruction : Opcode) (arguments : List NodeId) (values : List Word) (expected : Word) (sequence : BitVec 32)
    (debug : Debug) (usizeBits : Nat)
    (actual : readArguments before.read arguments = some values)
    (evaluated : (wordDispatchMeaning env other).operation instruction sequence values = some expected) :
    Safe (wordDispatchMeaning env other)
      (simplify reads (implementedConstructors p) usizeBits instruction arguments debug) before
      (fun result after => ∀ id, result = some id → after.read id = some expected) := by
  apply default_simplify_safe env other reads (implementedConstructors p)
    (implemented_constructors_sound (wordBaseMeaning env other) pushes p contracts) _ _
    before valid sound instruction arguments values expected sequence debug usizeBits actual evaluated
  · exact AddressMask.interner_constructs env (ArithmeticShift.shiftMeaning other) p
      (by simpa only [word_dispatch_address_model] using contracts)
  · exact ArithmeticShift.interner_constructs (AddressMask.addressMeaning env other) p contracts

/-- The normalized operation-key interface used by interning. The request's
epoch is retained in its denotation, even though the dispatcher does not inspect it. -/
theorem default_key_simplify_safe (env : AddressMask.Environment) (other : Meaning)
    (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound (wordBaseMeaning env other) constructors)
    (addressCorrect : AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) constructors.operation)
    (sarCorrect : ArithmeticShift.Constructs (AddressMask.addressMeaning env other) constructors.operation)
    (before : Heap) (valid : Invariant (wordDispatchMeaning env other) before)
    (sound : Sound (wordDispatchMeaning env other) before.read reads)
    (key : Key) (operation : key.kind = 1) (expected : Word) (debug : Debug) (usizeBits : Nat)
    (evaluated : key.eval (wordDispatchMeaning env other) before.read = some expected) :
    Safe (wordDispatchMeaning env other)
      (simplify reads constructors usizeBits key.instruction key.arguments debug) before
      (fun result after => ∀ id, result = some id → after.read id = some expected) := by
  cases actual : readArguments before.read key.arguments with
  | none => simp [Key.eval, actual] at evaluated
  | some values =>
    exact default_simplify_safe env other reads constructors correct addressCorrect sarCorrect before valid sound
      key.instruction key.arguments values expected key.sequence debug usizeBits actual
      (by simpa [Key.eval, actual, operation] using evaluated)

end Compiler.Extraction.Dispatch
