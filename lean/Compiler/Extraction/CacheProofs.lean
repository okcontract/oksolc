/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.CacheProgram

namespace Compiler.Extraction.Cache
open Compiler.Algebraic Contract.Yul
set_option linter.unusedSimpArgs false

/-- Every key component is compared, including argument contents and the
sequence distinguishing observations. Hash collisions need not be impossible. -/
theorem equality_iff (a b : Key) : equal equalityFields a b = true ↔ a = b := by
  cases a
  cases b
  simp [equal, equalityFields, Field.equal, Key.mk.injEq, and_comm]

theorem key_sound (meaning : Meaning) (read : Read) (item : Item) (arguments : List NodeId)
    (sequence : BitVec 32) (key : Key) (made : keyCode.run item arguments sequence = some key) :
    key.eval meaning read = item.eval meaning read arguments sequence := by
  unfold KeyCode.run keyCode Test.run Scalar.run at made
  by_cases operation : item.kind = 1
  · cases instruction : item.instruction with
    | none => simp [operation, instruction] at made
    | some opcode =>
      simp [operation, instruction] at made
      subst key
      simp [Key.eval, Item.eval, operation, instruction]
  · have operation' : item.kind ≠ 1#32 := operation
    simp [operation'] at made
    subst key
    simp [Key.eval, Item.eval, operation']

/-- Key construction preserves the supplied arguments and observation sequence. -/
theorem key_inputs (item : Item) (arguments : List NodeId) (sequence : BitVec 32)
    (key : Key) (made : keyCode.run item arguments sequence = some key) :
    key.arguments = arguments ∧ key.sequence = sequence := by
  unfold KeyCode.run keyCode Test.run Scalar.run at made
  by_cases operation : item.kind = 1#32
  · cases instruction : item.instruction with
    | none => simp [operation, instruction] at made
    | some opcode => simp [operation, instruction] at made; cases made; exact ⟨rfl, rfl⟩
  · simp [operation] at made
    cases made
    exact ⟨rfl, rfl⟩

theorem key_missing_instruction (item : Item) (arguments : List NodeId) (sequence : BitVec 32)
    (operation : item.kind = 1) (missing : item.instruction = none) :
    keyCode.run item arguments sequence = none := by
  simp [keyCode, KeyCode.run, Test.run, Scalar.run, operation, missing]

theorem readArguments_length (read : Read) (ids : List NodeId) (values : List Word)
    (actual : readArguments read ids = some values) : values.length = ids.length := by
  induction ids generalizing values with
  | nil => simp [readArguments] at actual; subst values; rfl
  | cons id rest ih =>
    cases head : read id with
    | none => simp [readArguments, head] at actual
    | some value =>
      cases tail : readArguments read rest with
      | none => simp [readArguments, head, tail] at actual
      | some words =>
        simp [readArguments, head, tail] at actual
        subst values
        simp [ih words tail]

theorem readArguments_stable (before after : Read) (stable : Preserves (fun r => r) before after)
    (ids : List NodeId) (values : List Word) (read : readArguments before ids = some values) :
    readArguments after ids = some values := by
  induction ids generalizing values with
  | nil => simpa [readArguments] using read
  | cons id rest ih =>
    cases h : before id with
    | none => simp [readArguments, h] at read
    | some value =>
      cases tail : readArguments before rest with
      | none => simp [readArguments, h, tail] at read
      | some words =>
        simp [readArguments, h, tail] at read
        subst values
        simp [readArguments, stable id value h, ih words tail]

theorem key_stable (meaning : Meaning) (before after : Read)
    (stable : Preserves (fun r => r) before after) (key : Key) (value : Word)
    (read : key.eval meaning before = some value) : key.eval meaning after = some value := by
  cases args : readArguments before key.arguments with
  | none => simp [Key.eval, args] at read
  | some words =>
    simpa [Key.eval, readArguments_stable before after stable key.arguments words args] using
      (show (if key.kind = 1 then meaning.operation key.instruction key.sequence words
        else meaning.atom key.kind key.data key.sequence words) = some value by
        simpa [Key.eval, args] using read)

theorem valid_stable (meaning : Meaning) (before after : Read) (table : Table)
    (valid : Valid meaning before table) (stable : Preserves (fun r => r) before after) :
    Valid meaning after table := by
  intro key id found
  obtain ⟨value, denotation, actual⟩ := valid key id found
  exact ⟨value, key_stable meaning before after stable key value denotation, stable id value actual⟩

/-- The map primitive returns an entry matching the extracted equality.
The invariant supplies a valid ID and denotation, not just equal key bytes. -/
theorem hit_sound (meaning : Meaning) (read : Read) (table : Table)
    (valid : Valid meaning read table) (query stored : Key) (id : NodeId)
    (matched : equal equalityFields query stored = true) (found : table stored = some id) :
    ∃ value, query.eval meaning read = some value ∧ read id = some value := by
  have same := (equality_iff query stored).mp matched
  subst stored
  exact valid query id found

theorem put_valid (meaning : Meaning) (read : Read) (table : Table)
    (valid : Valid meaning read table) (key : Key) (id : NodeId) (value : Word)
    (denotation : key.eval meaning read = some value) (actual : read id = some value) :
    Valid meaning read (put equalityFields table key id) := by
  intro query result found
  unfold put at found
  by_cases same : equal equalityFields query key = true
  · have eq := (equality_iff query key).mp same
    subst query
    simp [same] at found
    subst result
    exact ⟨value, denotation, actual⟩
  · simp [same] at found
    exact valid query result found

theorem put_returns (table : Table) (key : Key) (id : NodeId) :
    put equalityFields table key id key = some id := by
  simp [put, (equality_iff key key).mpr rfl]

/-- Sort's primitive contract is permutation of the copied argument slice.
The extracted commutativity list determines where that contract is sufficient. -/
theorem commutative_sound (op : Binary) (a b : Word)
    (admitted : normalizeCode.commutative.contains (productionOpcode op) = true) :
    op.eval a b = op.eval b a := by
  cases op <;> simp [normalizeCode, productionOpcode] at admitted
  all_goals first
    | exact BitVec.add_comm _ _
    | exact BitVec.mul_comm _ _
    | exact BitVec.and_comm _ _
    | exact BitVec.or_comm _ _
    | exact BitVec.xor_comm _ _
    | skip
  change boolWord (a == b) = boolWord (b == a)
  by_cases h : a = b
  · subst b; rfl
  · have ab : (a == b) = false := beq_eq_false_iff_ne.mpr h
    have ba : (b == a) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
    rw [ab, ba]

theorem pair_permutation {α : Type} (a b : α) (items : List α) (perm : items.Perm [a, b]) :
    items = [a, b] ∨ items = [b, a] := by
  have length := perm.length_eq
  cases items with
  | nil => simp at length
  | cons x rest =>
    cases rest with
    | nil => simp at length
    | cons y rest =>
      have empty : rest = [] := by simpa using length
      subst rest
      have member := perm.mem_iff.mp (show x ∈ [x, y] by simp)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · have tail := perm.cons_inv
        have : y = b := by simpa using tail
        subst y
        exact Or.inl rfl
      · have tail := (perm.trans (List.Perm.swap x a [])).cons_inv
        have : y = a := by simpa using tail
        subst y
        exact Or.inr rfl

/-- Valid binary arities preserve denotation. Malformed arities do not receive
this theorem; unknown/noncommutative operations retain argument order. -/
theorem normalize_binary (sort : List NodeId → List NodeId)
    (permutation : ∀ ids, (sort ids).Perm ids) (op : Binary) (data : Word)
    (read : NodeId → Word) (a b : NodeId) :
    let ids := normalizeCode.run sort ⟨1, some (productionOpcode op), data⟩ [a, b]
    ids.map (List.map read) = some [read a, read b] ∨
      (ids.map (List.map read) = some [read b, read a] ∧ op.eval (read a) (read b) = op.eval (read b) (read a)) := by
  dsimp only
  by_cases commutes : normalizeCode.commutative.contains (productionOpcode op) = true
  · have member : productionOpcode op ∈ normalizeCode.commutative := by simpa using commutes
    have normalized : normalizeCode.run sort ⟨1, some (productionOpcode op), data⟩ [a, b] = some (sort [a, b]) := by
      simp [NormalizeCode.run, show normalizeCode.guard = .operation from rfl,
        show normalizeCode.threshold = 2 from rfl, Test.run, member]
    rw [normalized]
    rcases pair_permutation a b (sort [a, b]) (permutation [a, b]) with ordered | swapped
    · exact Or.inl (by simp [ordered])
    · exact Or.inr ⟨by simp [swapped], commutative_sound op _ _ commutes⟩
  · have absent : productionOpcode op ∉ normalizeCode.commutative := by simpa using commutes
    have normalized : normalizeCode.run sort ⟨1, some (productionOpcode op), data⟩ [a, b] = some [a, b] := by
      simp [NormalizeCode.run, show normalizeCode.guard = .operation from rfl, Test.run, absent]
    rw [normalized]
    exact Or.inl rfl

theorem normalize_noncommutative (sort : List NodeId → List NodeId)
    (opcode : Opcode) (data : Word) (ids : List NodeId)
    (ordered : normalizeCode.commutative.contains opcode = false) :
    normalizeCode.run sort ⟨1, some opcode, data⟩ ids = some ids := by
  have absent : opcode ∉ normalizeCode.commutative := by simpa using ordered
  simp [NormalizeCode.run, show normalizeCode.guard = .operation from rfl, Test.run, absent]

theorem normalize_constant (sort : List NodeId → List NodeId) (value : Word) :
    normalizeCode.run sort ⟨2, none, value⟩ [] = some [] := rfl

theorem normalize_missing_instruction (sort : List NodeId → List NodeId) (data : Word) (ids : List NodeId) :
    normalizeCode.run sort ⟨1, none, data⟩ ids = none := rfl

end Compiler.Extraction.Cache
