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

/-- Constructors start only after all missing-match exits. Once started, the
complete sequence ends with a match or a retained failure, never a miss. -/
theorem reassociate_miss (reads : Reads) (constructors : Constructors Debug) (instruction : Opcode)
    (nested other : NodeId) (right : Bool) (debug : Debug) :
    MissUnchanged (reassociate reads constructors instruction nested other right debug) := by
  unfold reassociate
  repeat first
    | exact pure_miss_unchanged _
    | apply read_miss_unchanged; intro option
    | split
    | apply never_miss_unchanged
      repeat first
        | exact terminal_never_miss _
        | apply bind_never_miss; intro id

theorem repeated_miss (reads : Reads) (localBuild : LocalOperationBuilder Debug) (instruction : Opcode)
    (nested repeated : NodeId) (first : Bool) (debug : Debug) :
    MissUnchanged (dropRepeatedLocal reads localBuild instruction nested repeated first debug) := by
  unfold dropRepeatedLocal
  repeat first
    | exact pure_miss_unchanged _
    | exact terminal_miss_unchanged _
    | apply read_miss_unchanged; intro option
    | split

theorem reassociation_pair_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (op : Folding.Op) (supported : Supported op) (left right : NodeId) (a b : Word) (debug : Debug)
    (lhs : before.read left = some a) (rhs : before.read right = some b)
    (next : Action (Option NodeId))
    (rest : Safe (Folding.wordMeaning other) next before
      (fun result after => ∀ id, result = some id → after.read id = some (op.value a b 0))) :
    Safe (Folding.wordMeaning other) (do
      if let some id ← reassociate reads constructors op.opcode left right false debug then return some id
      if let some id ← reassociate reads constructors op.opcode right left true debug then return some id
      next) before (fun result after => ∀ id, result = some id → after.read id = some (op.value a b 0)) := by
  apply optional_bind_safe_of_unchanged _ _ _ before _
    (reassociate_safe other reads constructors correct before valid sound op supported left right false a b lhs rhs debug)
    (reassociate_miss reads constructors op.opcode left right false debug)
  · intro id; rfl
  · apply optional_bind_safe_of_unchanged _ _ _ before _
      (reassociate_safe other reads constructors correct before valid sound op supported right left true b a rhs lhs debug)
      (reassociate_miss reads constructors op.opcode right left true debug)
    · intro id; rfl
    · exact rest

theorem repeated_pair_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (op : Folding.Op) (idempotent : Idempotent op) (left right : NodeId) (a b : Word) (debug : Debug)
    (lhs : before.read left = some a) (rhs : before.read right = some b)
    (next : Action (Option NodeId))
    (rest : Safe (Folding.wordMeaning other) next before
      (fun result after => ∀ id, result = some id → after.read id = some (op.value a b 0))) :
    Safe (Folding.wordMeaning other) (do
      if let some id ← dropRepeatedLocal reads constructors.localOperation op.opcode left right false debug then return some id
      if let some id ← dropRepeatedLocal reads constructors.localOperation op.opcode right left true debug then return some id
      next) before (fun result after => ∀ id, result = some id → after.read id = some (op.value a b 0)) := by
  apply optional_bind_safe_of_unchanged _ _ _ before _
    (drop_repeated_local_safe other reads constructors.localOperation correct.localOperation before valid sound op idempotent left right false a b lhs rhs debug)
    (repeated_miss reads constructors.localOperation op.opcode left right false debug)
  · intro id; rfl
  · apply optional_bind_safe_of_unchanged _ _ _ before _
      (drop_repeated_local_safe other reads constructors.localOperation correct.localOperation before valid sound op idempotent right left true b a rhs lhs debug)
      (repeated_miss reads constructors.localOperation op.opcode right left true debug)
    · intro id; rfl
    · exact rest

theorem xor_capture_value (other : Meaning) (read : Read) (reads : Reads)
    (sound : Sound (Folding.wordMeaning other) read reads) (left right result : NodeId) (a b : Word)
    (lhs : read left = some a) (rhs : read right = some b)
    (found : cancelNestedBinary reads opXOR left right = .ok (some result)) :
    read result = some (a ^^^ b) := by
  obtain ⟨nestedValue, resultValue, nestedRead, resultRead, equation⟩ :=
    cancel_xor_sound other read reads sound left right result a lhs found
  have same := Option.some.inj (nestedRead.symm.trans rhs)
  subst nestedValue
  rw [← equation] at resultRead
  exact resultRead

theorem or_absorption_value (other : Meaning) (read : Read) (reads : Reads)
    (sound : Sound (Folding.wordMeaning other) read reads) (left right result : NodeId) (a b : Word)
    (lhs : read left = some a) (rhs : read right = some b)
    (found : absorbedOccurrence reads left right opAND = .ok (some result)) :
    a ||| b = a ∧ read result = some a := by
  obtain ⟨nestedValue, nestedRead, resultRead, equation⟩ :=
    absorbed_and_sound other read reads sound left right result a lhs found
  have same := Option.some.inj (nestedRead.symm.trans rhs)
  subst nestedValue
  exact ⟨equation, resultRead⟩

theorem or_negation_value (other : Meaning) (read : Read) (reads : Reads)
    (sound : Sound (Folding.wordMeaning other) read reads) (left right : NodeId) (a b : Word)
    (lhs : read left = some a) (rhs : read right = some b)
    (found : isNegation reads left right = .ok true) : a ||| b = BitVec.allOnes 256 := by
  have node := negation_sound other read reads sound left right a lhs found
  have same : b = ~~~a := Option.some.inj (rhs.symm.trans node)
  simp [same]

private theorem xor_tail_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (do
      if let some id ← readAction (cancelNestedBinary reads opXOR left right) then return some id
      if let some id ← readAction (cancelNestedBinary reads opXOR right left) then return some id
      if let some id ← reassociate reads constructors opXOR left right false debug then return some id
      if let some id ← reassociate reads constructors opXOR right left true debug then return some id
      return none) before (fun result after => ∀ id, result = some id → after.read id = some (a ^^^ b)) := by
  apply read_action_bind_safe _ before _ _ _ valid
  intro option found
  cases option with
  | some id =>
    exact Safe.pure _ before (some id) _ valid (by
      intro result equal; cases equal
      exact xor_capture_value other before.read reads sound left right id a b lhs rhs found)
  | none =>
    apply read_action_bind_safe _ before _ _ _ valid
    intro option found
    cases option with
    | some id =>
      exact Safe.pure _ before (some id) _ valid (by
        intro result equal; cases equal
        simpa [BitVec.xor_comm] using xor_capture_value other before.read reads sound right left id b a rhs lhs found)
    | none =>
      apply reassociation_pair_safe other reads constructors correct before valid sound .xor
        (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) left right a b debug lhs rhs
      exact Safe.pure _ before none _ valid (by simp)

private theorem or_tail_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (debug : Debug)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (do
      if (← readAction (absorbedOccurrence reads left right opAND)).isSome then return some left
      if let some id ← readAction (absorbedOccurrence reads right left opAND) then return some id
      if (← readAction (isNegation reads left right)) then
        return some (← constructors.constant (BitVec.allOnes 256) debug)
      if (← readAction (isNegation reads right left)) then
        return some (← constructors.constant (BitVec.allOnes 256) debug)
      if let some id ← dropRepeatedLocal reads constructors.localOperation opOR left right false debug then return some id
      if let some id ← dropRepeatedLocal reads constructors.localOperation opOR right left true debug then return some id
      if let some id ← reassociate reads constructors opOR left right false debug then return some id
      if let some id ← reassociate reads constructors opOR right left true debug then return some id
      return none) before (fun result after => ∀ id, result = some id → after.read id = some (a ||| b)) := by
  apply read_action_bind_safe _ before _ _ _ valid
  intro option found
  cases option with
  | some id =>
    obtain ⟨value, _⟩ := or_absorption_value other before.read reads sound left right id a b lhs rhs found
    exact Safe.pure _ before (some left) _ valid (by intro result equal; cases equal; simpa [value] using lhs)
  | none =>
    apply read_action_bind_safe _ before _ _ _ valid
    intro option found
    cases option with
    | some id =>
      obtain ⟨value, resultRead⟩ := or_absorption_value other before.read reads sound right left id b a rhs lhs found
      exact Safe.pure _ before (some id) _ valid (by
        intro result equal; cases equal
        simpa [BitVec.or_comm a b, value] using resultRead)
    | none =>
      apply read_action_bind_safe _ before _ _ _ valid
      intro negated found
      cases negated with
      | true =>
        rw [or_negation_value other before.read reads sound left right a b lhs rhs found]
        exact constant_some_safe other constructors correct before valid _ debug
      | false =>
        apply read_action_bind_safe _ before _ _ _ valid
        intro negated found
        cases negated with
        | true =>
          rw [BitVec.or_comm a b, or_negation_value other before.read reads sound right left b a rhs lhs found]
          exact constant_some_safe other constructors correct before valid _ debug
        | false =>
          apply repeated_pair_safe other reads constructors correct before valid sound .or (Or.inr rfl) left right a b debug lhs rhs
          apply reassociation_pair_safe other reads constructors correct before valid sound .or
            (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) left right a b debug lhs rhs
          exact Safe.pure _ before none _ valid (by simp)

/-- These are the associative paths whose complete inline rule families are
composed below. MUL and AND have additional rules and are not covered here. -/
def AddOrXor (op : Folding.Op) : Prop := op = .add ∨ op = .or ∨ op = .xor

theorem binary_add_or_xor_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (op : Folding.Op) (supported : AddOrXor op) (left right : NodeId) (a b : Word)
    (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (binaryStage reads constructors usizeBits op.opcode left right debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (op.value a b 0)) := by
  rcases supported with rfl | rfl | rfl
  all_goals
    unfold binaryStage binaryStageWithInputs
    simp only [Folding.Op.opcode, opSDIV, opAND, opBYTE, opSLT, opSGT, opXOR, opOR,
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
        next =>
          first
          | simpa only [pure_bind_action] using
              reassociation_pair_safe other reads constructors correct before valid sound .add
                (Or.inl rfl) left right a b debug lhs rhs (pure none) (Safe.pure _ before none _ valid (by simp))
          | simpa only [pure_bind_action] using or_tail_safe other reads constructors correct before valid sound left right a b debug lhs rhs
          | simpa only [pure_bind_action] using xor_tail_safe other reads constructors correct before valid sound left right a b debug lhs rhs
      next =>
        first
        | simpa only [pure_bind_action] using
            reassociation_pair_safe other reads constructors correct before valid sound .add
              (Or.inl rfl) left right a b debug lhs rhs (pure none) (Safe.pure _ before none _ valid (by simp))
        | simpa only [pure_bind_action] using or_tail_safe other reads constructors correct before valid sound left right a b debug lhs rhs
        | simpa only [pure_bind_action] using xor_tail_safe other reads constructors correct before valid sound left right a b debug lhs rhs

theorem binary_add_or_xor_miss (reads : Reads) (constructors : Constructors Debug)
    (op : Folding.Op) (supported : AddOrXor op) (left right : NodeId)
    (debug : Debug) (options : Options) (usizeBits : Nat) :
    MissUnchanged (binaryStage reads constructors usizeBits op.opcode left right debug options) := by
  rcases supported with rfl | rfl | rfl
  all_goals
    unfold binaryStage binaryStageWithInputs
    simp only [Folding.Op.opcode, opSDIV, opAND, opBYTE, opSLT, opSGT, opXOR, opOR,
      opSIGNEXTEND, opMOD, opSHL, opSHR, opMUL, opDIV, opSUB, Associative.isAssociative,
      Bool.false_eq_true, ↓reduceIte, Bool.false_or, Bool.or_false, Bool.true_or, Bool.or_true,
      List.contains_cons, List.contains_nil, beq_self_eq_true, BitVec.reduceBEq]
    repeat first
      | exact pure_miss_unchanged _
      | exact terminal_miss_unchanged _
      | apply read_miss_unchanged; intro option
      | intro id; rfl
      | apply optional_bind_miss_unchanged _ _ (reassociate_miss reads constructors _ _ _ _ debug)
      | apply optional_bind_miss_unchanged _ _ (repeated_miss reads constructors.localOperation _ _ _ _ debug)
      | split

theorem add_or_xor_evm_stage (reads : Reads) (constructors : Constructors Debug)
    (op : Folding.Op) (supported : AddOrXor op) (arguments : List NodeId)
    (debug : Debug) (version : Version) (usizeBits : Nat) :
    evmStage reads constructors usizeBits op.opcode arguments debug version = pure none := by
  rcases supported with rfl | rfl | rfl
  all_goals
    simp only [evmStage, evmStageWithInputs, logicalOperand, Folding.Op.opcode, opBALANCE, opEXP, opMUL, opDIV,
      Bool.false_eq_true, ↓reduceIte, BitVec.reduceBEq]
    repeat first | rfl | split

theorem add_or_xor_simplify_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (op : Folding.Op) (supported : AddOrXor op) (left right : NodeId) (a b : Word)
    (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (simplifyWithOptions reads constructors usizeBits op.opcode [left, right] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (op.value a b 0)) := by
  have denotation : (Folding.wordMeaning other).operation op.opcode 0 [a, b] = some (op.value a b 0) := by
    rw [Folding.word_meaning_operation]
    rcases supported with rfl | rfl | rfl <;> rfl
  apply binary_simplify_safe other reads constructors correct before valid sound op.opcode left right a b _ 0
    debug options usizeBits lhs rhs denotation
    (binary_add_or_xor_safe other reads constructors correct before valid sound op supported left right a b debug options usizeBits lhs rhs)
    (binary_add_or_xor_miss reads constructors op supported left right debug options usizeBits)
  intro version _
  rw [add_or_xor_evm_stage reads constructors op supported]
  exact Safe.pure _ before none _ valid (by simp)

theorem interner_add_or_xor_simplify_safe (other : Meaning) (pushes : Pushes other) (p : Primitives)
    (contracts : Contracts (Folding.wordMeaning other) p) (reads : Reads) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (op : Folding.Op) (supported : AddOrXor op) (left right : NodeId) (a b : Word)
    (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b) :
    Safe (Folding.wordMeaning other) (simplifyWithOptions reads (implementedConstructors p) usizeBits op.opcode [left, right] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some (op.value a b 0)) :=
  add_or_xor_simplify_safe other reads (implementedConstructors p)
    (implemented_constructors_sound other pushes p contracts) before valid sound
    op supported left right a b debug options usizeBits lhs rhs

end Compiler.Extraction.Dispatch
