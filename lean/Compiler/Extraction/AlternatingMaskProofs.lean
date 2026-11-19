/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.AlternatingMaskProgram

namespace Compiler.Extraction.AlternatingMask
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.Extraction.Interner Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul
set_option linter.unusedSimpArgs false

private theorem pure_ok (value : α) : (pure value : Except ReadError α) = .ok value := rfl
private theorem bind_ok (value : α) (next : α → Except ReadError β) :
    ((.ok value : Except ReadError α) >>= next) = next value := rfl
private theorem bind_error (error : ReadError) (next : α → Except ReadError β) :
    ((.error error : Except ReadError α) >>= next) = .error error := rfl
attribute [local simp] pure_ok bind_ok bind_error

theorem and_opcode : andOpcode = Folding.Op.and.opcode := rfl
theorem or_opcode : orOpcode = Folding.Op.or.opcode := rfl

theorem candidate_found (reads : Reads) (choice : Choice) (left right : NodeId) (capture : Capture)
    (found : matchCandidate reads choice left right = .ok (some capture)) :
    ∃ alternatives inner al ar il ir a b,
      reads.constant (pick choice.outerSecond right left) = .ok (some b) ∧
      reads.operation (pick choice.outerSecond left right) orOpcode = .ok (some alternatives) ∧
      alternatives.items = [al, ar] ∧
      reads.operation (pick choice.innerSecond al ar) andOpcode = .ok (some inner) ∧
      inner.items = [il, ir] ∧
      reads.constant (pick choice.constantFirst ir il) = .ok (some a) ∧
      capture = ⟨pick choice.constantFirst il ir,
        pick choice.innerSecond ar al, pick choice.outerSecond right left, a, b,
        inner, alternatives, if choice.constantFirst then 1 else 0, if choice.innerSecond then 0 else 1⟩ := by
  unfold matchCandidate at found
  cases outerLookup : reads.constant (pick choice.outerSecond right left) with
  | error error => simp [outerLookup] at found
  | ok outerOption =>
    cases outerOption with
    | none => simp [outerLookup] at found
    | some b =>
      simp only [outerLookup, bind_ok] at found
      cases alternativeLookup : reads.operation (pick choice.outerSecond left right) orOpcode with
      | error error => simp [alternativeLookup] at found
      | ok alternativeOption =>
        cases alternativeOption with
        | none => simp [alternativeLookup] at found
        | some alternatives =>
          simp only [alternativeLookup, bind_ok] at found
          split at found
          next al ar items =>
            cases innerLookup : reads.operation (pick choice.innerSecond al ar) andOpcode with
            | error error => simp [innerLookup] at found
            | ok innerOption =>
              cases innerOption with
              | none => simp [innerLookup] at found
              | some inner =>
                simp only [innerLookup, bind_ok] at found
                split at found
                next il ir innerItems =>
                  cases constantLookup : reads.constant (pick choice.constantFirst ir il) with
                  | error error => simp [constantLookup] at found
                  | ok constantOption =>
                    cases constantOption with
                    | none => simp [constantLookup] at found
                    | some a =>
                      simp only [constantLookup, bind_ok, pure_ok, Except.ok.injEq, Option.some.injEq] at found
                      exact ⟨alternatives, inner, al, ar, il, ir, a, b,
                        by rfl, by rfl, items, innerLookup, innerItems, constantLookup, found.symm⟩
                next => simp at found
          next => simp at found

theorem candidate_sound (other : Meaning) (read : Read) (reads : Reads)
    (sound : Sound (Folding.wordMeaning other) read reads) (choice : Choice)
    (left right : NodeId) (a b : Word) (lhs : read left = some a) (rhs : read right = some b)
    (capture : Capture) (found : matchCandidate reads choice left right = .ok (some capture)) :
    ∃ x y, read capture.expression = some x ∧ read capture.otherExpression = some y ∧
      outputValue x capture.innerMask y capture.outerMask = a &&& b := by
  obtain ⟨alternatives, inner, al, ar, il, ir, im, om, maskLookup, altLookup, items,
    innerLookup, innerItems, constantLookup, rfl⟩ := candidate_found reads choice left right capture found
  have maskRead := sound.constant _ _ maskLookup
  have constantRead := sound.constant _ _ constantLookup
  obtain ⟨u, v, ul, vr, innerRead⟩ := binary_values other read reads sound .and rfl _ il ir inner innerLookup innerItems
  obtain ⟨p, q, pl, qr, altRead⟩ := binary_values other read reads sound .or rfl _ al ar alternatives altLookup items
  refine ⟨pick choice.constantFirst u v, pick choice.innerSecond q p, ?_, ?_, ?_⟩
  · cases h : choice.constantFirst <;> simp [pick, h, ul, vr]
  · cases h : choice.innerSecond <;> simp [pick, h, pl, qr]
  · rw [← distribution choice]
    rcases choice with ⟨cf, ins, outs⟩
    cases cf <;> cases ins <;> cases outs <;>
      simp only [pick, Bool.false_eq_true, ↓reduceIte, Folding.Op.value, Binary.eval] at * <;>
      simp_all only [Option.some.injEq]
    all_goals subst_vars; rfl

/-- Each of the five fallible calls keeps every prior valid ID and the cache
invariant. The postcondition applies only to success; Safe also covers errors
with whatever intermediate graph growth the constructors actually retained. -/
theorem build_safe (other : Meaning) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (capture : Capture) (debug : Debug)
    (before : Heap) (valid : Invariant (Folding.wordMeaning other) before)
    (x y : Word) (expression : before.read capture.expression = some x)
    (otherExpression : before.read capture.otherExpression = some y) :
    Safe (Folding.wordMeaning other) (buildCandidate constructors capture debug) before
      (fun id after => after.read id = some (outputValue x capture.innerMask y capture.outerMask)) := by
  unfold buildCandidate
  apply Safe.bind _ before _ _ _ _ (correct.constant _ debug before valid)
  intro constant h1 valid1 stable1 constantRead
  apply Safe.bind _ h1 _ _ _ _ (binary_construct other constructors correct .and (by simp [Supported])
    capture.expression constant x _ debug h1 valid1 (stable1 _ _ expression) constantRead)
  intro left h2 valid2 stable2 leftRead
  apply Safe.bind _ h2 _ _ _ _ (correct.materialize capture.outerMaskId capture.outerMask debug h2 valid2)
  intro materialized h3 valid3 stable3 materializedRead
  apply Safe.bind _ h3 _ _ _ _ (binary_construct other constructors correct .and (by simp [Supported])
    capture.otherExpression materialized y _ debug h3 valid3
      (stable3 _ _ (stable2 _ _ (stable1 _ _ otherExpression))) materializedRead)
  intro right h4 valid4 stable4 rightRead
  exact binary_construct other constructors correct .or (by simp [Supported]) left right _ _ debug h4 valid4
    (stable4 _ _ (stable3 _ _ leftRead)) rightRead

theorem search_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (lhs : before.read left = some a)
    (rhs : before.read right = some b) (debug : Debug) (candidates : List Choice) :
    Safe (Folding.wordMeaning other) (search reads constructors left right debug candidates) before
      (fun result after => ∀ id, result = some id → after.read id = some (a &&& b)) := by
  induction candidates with
  | nil => exact Safe.pure _ before none _ valid (by simp)
  | cons choice rest ih =>
    unfold search
    apply read_action_bind_safe _ before _ _ _ valid
    intro option found
    cases option with
    | none => exact ih
    | some capture =>
      obtain ⟨x, y, expression, otherExpression, value⟩ :=
        candidate_sound other before.read reads sound choice left right a b lhs rhs capture found
      apply Safe.bind _ before _ _ _ _ (build_safe other constructors correct capture debug before valid x y expression otherExpression)
      intro result after validAfter _ actual
      exact Safe.pure _ after (some result) _ validAfter (by intro id equal; cases equal; simpa only [value] using actual)

theorem distribute_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (lhs : before.read left = some a)
    (rhs : before.read right = some b) (debug : Debug) :
    Safe (Folding.wordMeaning other) (distributeAlternatingMask reads constructors left right debug) before
      (fun result after => ∀ id, result = some id → after.read id = some (a &&& b)) :=
  search_safe other reads constructors correct before valid sound left right a b lhs rhs debug choices

theorem interner_distribute_safe (other : Meaning) (pushes : Pushes other) (p : Primitives)
    (contracts : Contracts (Folding.wordMeaning other) p) (reads : Reads) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (left right : NodeId) (a b : Word) (lhs : before.read left = some a)
    (rhs : before.read right = some b) (debug : Debug) :
    Safe (Folding.wordMeaning other) (distributeAlternatingMask reads (implementedConstructors p) left right debug) before
      (fun result after => ∀ id, result = some id → after.read id = some (a &&& b)) :=
  distribute_safe other reads (implementedConstructors p) (implemented_constructors_sound other pushes p contracts)
    before valid sound left right a b lhs rhs debug

private theorem pure_bind (value : α) (next : α → Action β) :
    ((pure value : Action α) >>= next) = next value := rfl

theorem search_skips (reads : Reads) (constructors : Constructors Debug) (left right : NodeId)
    (debug : Debug) (misses remaining : List Choice)
    (miss : ∀ choice ∈ misses, matchCandidate reads choice left right = .ok none) :
    search reads constructors left right debug (misses ++ remaining) =
      search reads constructors left right debug remaining := by
  induction misses with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.cons_append, search, searchWithInputs, miss head (by simp), readAction, pure_bind]
    exact ih (by intro choice member; exact miss choice (by simp [member]))

theorem search_stops (reads : Reads) (constructors : Constructors Debug) (left right : NodeId)
    (debug : Debug) (choice : Choice) (rest : List Choice) (capture : Capture)
    (found : matchCandidate reads choice left right = .ok (some capture)) :
    search reads constructors left right debug (choice :: rest) =
      (buildCandidate constructors capture debug >>= fun id => pure (some id)) := by
  simp only [search, searchWithInputs, found, readAction, pure_bind, buildCandidate]

theorem search_failure (reads : Reads) (constructors : Constructors Debug) (left right : NodeId)
    (debug : Debug) (choice : Choice) (rest : List Choice) (capture : Capture)
    (found : matchCandidate reads choice left right = .ok (some capture))
    (before after : Heap) (error : Error)
    (failed : buildCandidate constructors capture debug before = (.error error, after)) :
    search reads constructors left right debug (choice :: rest) before = (.error error, after) := by
  rw [search_stops reads constructors left right debug choice rest capture found]
  exact Effect.bind_failure _ _ before after error failed

theorem search_miss (reads : Reads) (constructors : Constructors Debug) (left right : NodeId)
    (debug : Debug) (candidates : List Choice) (before : Heap)
    (miss : ∀ choice ∈ candidates, matchCandidate reads choice left right = .ok none) :
    search reads constructors left right debug candidates before = (.ok none, before) := by
  have skipped := search_skips reads constructors left right debug candidates [] miss
  simpa only [List.append_nil] using congrFun skipped before

end Compiler.Extraction.AlternatingMask
