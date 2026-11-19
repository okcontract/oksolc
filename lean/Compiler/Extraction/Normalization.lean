/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.WordMeaning
import Compiler.Extraction.Interner

namespace Compiler.Extraction.Cache
open Compiler.Algebraic Contract.Yul
set_option linter.unusedSimpArgs false

/-- The extracted commutativity table admits exactly binary word operations.
No law is assumed for the caller's interpretation of other instructions. -/
theorem commutative_word_opcode (opcode : Opcode)
    (member : opcode ∈ normalizeCode.commutative) :
    ∃ op : Folding.Op, op.opcode = opcode ∧ op.arity = 2 ∧
      ∀ a b, op.value a b 0 = op.value b a 0 := by
  simp only [normalizeCode, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨.add, rfl, rfl, fun a b => commutative_sound .add a b rfl⟩
  · exact ⟨.mul, rfl, rfl, fun a b => commutative_sound .mul a b rfl⟩
  · exact ⟨.eq, rfl, rfl, fun a b => commutative_sound .eq a b rfl⟩
  · exact ⟨.and, rfl, rfl, fun a b => commutative_sound .and a b rfl⟩
  · exact ⟨.or, rfl, rfl, fun a b => commutative_sound .or a b rfl⟩
  · exact ⟨.xor, rfl, rfl, fun a b => commutative_sound .xor a b rfl⟩

theorem read_eval_wrong_arity (read : Read) (op : Folding.Op) (ids : List NodeId)
    (wrong : ids.length ≠ op.arity) :
    (readArguments read ids).bind op.eval = none := by
  cases actual : readArguments read ids with
  | none => rfl
  | some values =>
    have length := readArguments_length read ids values actual
    simp [Folding.Op.eval, length, wrong]

/-- This equality includes absent reads and malformed arities. Sorting cannot
turn an undefined application into a defined one, or discard a missing operand. -/
theorem read_eval_binary_permutation (read : Read) (op : Folding.Op)
    (arity : op.arity = 2) (commutes : ∀ a b, op.value a b 0 = op.value b a 0)
    (before after : List NodeId) (permutation : after.Perm before) :
    (readArguments read after).bind op.eval = (readArguments read before).bind op.eval := by
  by_cases length : before.length = 2
  · cases before with
    | nil => simp at length
    | cons a rest =>
      cases rest with
      | nil => simp at length
      | cons b rest =>
        have empty : rest = [] := by simpa using length
        subst rest
        rcases pair_permutation a b after permutation with ordered | swapped
        · rw [ordered]
        · rw [swapped]
          cases lhs : read a <;> cases rhs : read b <;>
            simp [readArguments, lhs, rhs, Folding.Op.eval, arity]
          exact commutes _ _
  · have wrongBefore : before.length ≠ op.arity := by simpa only [arity] using length
    have wrongAfter : after.length ≠ op.arity := by simpa only [permutation.length_eq] using wrongBefore
    rw [read_eval_wrong_arity read op after wrongAfter, read_eval_wrong_arity read op before wrongBefore]

/-- Semantic preservation of every successful result of the source-bound
normalization code, for arbitrary item kinds, arities, epochs and partial reads.
The copy/sort primitive must preserve the complete argument multiset. -/
theorem normalize_word (other : Meaning) (sort : List NodeId → List NodeId)
    (permutation : ∀ ids, (sort ids).Perm ids) (item : Item) (before after : List NodeId)
    (read : Read) (sequence : BitVec 32)
    (normalized : normalizeCode.run sort item before = some after) :
    item.eval (Folding.wordMeaning other) read after sequence =
      item.eval (Folding.wordMeaning other) read before sequence := by
  by_cases operation : item.kind = 1
  · cases instruction : item.instruction with
    | none => simp [NormalizeCode.run, normalizeCode, Test.run, operation, instruction] at normalized
    | some opcode =>
      by_cases member : opcode ∈ normalizeCode.commutative
      · by_cases enough : 2 ≤ before.length
        · have sorted : after = sort before := by
            simpa [NormalizeCode.run, show normalizeCode.guard = .operation from rfl,
              show normalizeCode.threshold = 2 from rfl, Test.run, operation, instruction, member, enough] using normalized.symm
          subst after
          obtain ⟨op, encoded, arity, commutes⟩ := commutative_word_opcode opcode member
          subst opcode
          simpa [Item.eval, operation, instruction, Folding.wordMeaning, Folding.decode_word_opcode] using
            read_eval_binary_permutation read op arity commutes before (sort before) (permutation before)
        · have unchanged : after = before := by
            simpa [NormalizeCode.run, show normalizeCode.guard = .operation from rfl,
              show normalizeCode.threshold = 2 from rfl, Test.run, operation, instruction, enough] using normalized.symm
          rw [unchanged]
      · have unchanged : after = before := by
          simpa [NormalizeCode.run, show normalizeCode.guard = .operation from rfl,
            Test.run, operation, instruction, member] using normalized.symm
        rw [unchanged]
  · have operation' : item.kind ≠ 1#32 := operation
    have unchanged : after = before := by
      simpa [NormalizeCode.run, show normalizeCode.guard = .operation from rfl,
        Test.run, operation'] using normalized.symm
    rw [unchanged]

/-- Native successful normalization must refine the extracted value projection.
Failures impose no fabricated semantic result; allocation and lifetime safety
remain separate primitive obligations. -/
def NormalizationRefines (sort : List NodeId → List NodeId) (p : Interner.Primitives) : Prop :=
  ∀ request args cursor after, p.normalize request cursor = (.ok args, after) →
    normalizeCode.run sort request.item request.arguments = some args

theorem normalizes_of_source (other : Meaning) (sort : List NodeId → List NodeId)
    (permutation : ∀ ids, (sort ids).Perm ids) (p : Interner.Primitives)
    (refines : NormalizationRefines sort p) : Interner.Normalizes (Folding.wordMeaning other) p := by
  intro request args read cursor after actual
  exact normalize_word other sort permutation request.item request.arguments args read request.sequence
    (refines request args cursor after actual)

end Compiler.Extraction.Cache
