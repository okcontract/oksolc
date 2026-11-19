/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.DispatchProgram

namespace Compiler.Extraction.Dispatch
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul

/-- Factoring the literal segment retains the original effect order and exact
reached heap on both child and operation failure. -/
theorem shiftInput_some (c : Constructors Debug (Effect Heap Error)) (first : Bool)
    (opcode : Opcode) (value : Word) (id : NodeId) (debug : Debug) :
    (do return some (← shiftInput c first opcode value (pure id) debug)) =
      (do let constant ← c.constant value debug
          return some (← c.operation opcode (if first then [constant, id] else [id, constant]) debug)) := by
  cases first <;> funext before <;>
    simp only [shiftInput, Bool.false_eq_true, ↓reduceIte, bind, Effect.bind, pure, Effect.pure] <;>
    cases called : c.constant value debug before with
    | mk result after => cases result <;> rfl
set_option linter.unusedSimpArgs false

theorem or_next_safe (meaning : Meaning) (stage next : Action (Option NodeId)) (before : Heap)
    (post : NodeId → Heap → Prop)
    (first : Safe meaning stage before (fun result after => ∀ id, result = some id → post id after))
    (rest : ∀ middle, Invariant meaning middle → Stable before middle →
      Safe meaning next middle (fun result after => ∀ id, result = some id → post id after)) :
    Safe meaning (orNext stage next) before (fun result after => ∀ id, result = some id → post id after) := by
  unfold orNext
  apply Safe.bind _ before _ _ _ _ first
  intro option middle valid stable actual
  cases option with
  | none => exact rest middle valid stable
  | some id => exact Safe.pure _ middle (some id) _ valid actual

theorem or_next_failure (stage next : Action (Option NodeId)) (before after : Heap) (error : Error)
    (failed : stage before = (.error error, after)) :
    orNext stage next before = (.error error, after) :=
  Effect.bind_failure stage _ before after error failed

theorem or_next_match (stage next : Action (Option NodeId)) (before after : Heap) (id : NodeId)
    (matched : stage before = (.ok (some id), after)) :
    orNext stage next before = (.ok (some id), after) := by
  change Effect.bind stage (fun option => match option with
    | some result => pure (some result) | none => next) before = _
  simp only [Effect.bind, matched]
  rfl

theorem or_next_miss (stage next : Action (Option NodeId)) (before middle : Heap)
    (missed : stage before = (.ok none, middle)) : orNext stage next before = next middle := by
  change Effect.bind stage (fun option => match option with
    | some result => pure (some result) | none => next) before = _
  simp only [Effect.bind, missed]

private theorem pure_ok (value : α) : (pure value : Except Storage.ReadError α) = .ok value := rfl
private theorem bind_ok (value : α) (next : α → Except Storage.ReadError β) :
    ((.ok value : Except Storage.ReadError α) >>= next) = next value := rfl
private theorem bind_error (error : Storage.ReadError) (next : α → Except Storage.ReadError β) :
    ((.error error : Except Storage.ReadError α) >>= next) = .error error := rfl
attribute [local simp] pure_ok bind_ok bind_error

theorem collected_values (meaning : Meaning) (read : Read) (reads : Reads)
    (sound : Sound meaning read reads) (ids : List NodeId) (values : List Word)
    (collected : collectConstants reads ids = .ok (some values)) :
    readArguments read ids = some values ∧ values.length = ids.length := by
  induction ids generalizing values with
  | nil => simp [collectConstants] at collected; subst values; exact ⟨rfl, rfl⟩
  | cons id rest ih =>
    cases lookup : reads.constant id with
    | error error => simp [collectConstants, lookup] at collected
    | ok option =>
      cases option with
      | none => simp [collectConstants, lookup] at collected
      | some value =>
        cases more : collectConstants reads rest with
        | error error => simp [collectConstants, lookup, more] at collected
        | ok option =>
          cases option with
          | none => simp [collectConstants, lookup, more] at collected
          | some tail =>
            simp [collectConstants, lookup, more] at collected
            subst values
            obtain ⟨actual, size⟩ := ih tail more
            exact ⟨by simp [readArguments, sound.constant id value lookup, actual], by simp [size]⟩

theorem folding_found (other : Meaning) (opcode : Opcode) (sequence : BitVec 32)
    (values : List Word) (value : Word)
    (found : Folding.run Folding.helpers Folding.clauses opcode values = .ok (some value)) :
    (Folding.wordMeaning other).operation opcode sequence values = some value := by
  classical
  by_cases known : ∃ op : Folding.Op, opcode = op.opcode
  · obtain ⟨op, rfl⟩ := known
    rw [Folding.folding_meaning other op sequence values] at found
    exact Except.ok.inj found
  · have unknown : ∀ op : Folding.Op, opcode ≠ op.opcode := by simpa using known
    rw [Folding.folding_unknown opcode values unknown] at found
    simp at found

/-- The shared pure bridge from collected graph constants and the extracted
folder to the request's denotation. It does not choose a constructor outcome. -/
theorem folded_value (other : Meaning) (read : Read) (reads : Reads)
    (sound : Sound (Folding.wordMeaning other) read reads) (instruction : Opcode)
    (arguments : List NodeId) (values : List Word) (expected computed : Word) (sequence : BitVec 32)
    (actual : readArguments read arguments = some values)
    (denotation : (Folding.wordMeaning other).operation instruction sequence values = some expected)
    {collectedValues : List Word}
    (collected : collectConstants reads arguments = .ok (some collectedValues))
    (folded : Folding.run Folding.helpers Folding.clauses instruction collectedValues = .ok (some computed)) :
    computed = expected := by
  have same := Option.some.inj (actual.symm.trans (collected_values _ read reads sound arguments collectedValues collected).1)
  subst collectedValues
  exact Option.some.inj ((folding_found other instruction sequence values computed folded).symm.trans denotation)

namespace Preservation
variable {State Failure Debug : Type} [MonadLift (Except Error) (Effect State Failure)]

/-- One recursive operation callback, at the caller's debug and the actual
valid reached state. Shared by the logical and native dispatcher proofs. -/
def OperationRule {State Failure Debug : Type} (logic : BuilderLogic (Effect State Failure) State)
    (constructors : Constructors Debug (Effect State Failure)) (debug : Debug) (op : Folding.Op) : Prop :=
  ∀ ids values value before, logic.valid before →
    readArguments (logic.read before) ids = some values → op.eval values = some value →
    logic.safe (constructors.operation op.opcode ids debug) before
      (fun id after => logic.read after id = some value)

/-- Read effects retain their exact observation and error policy. The same
law serves folding and the later source-query stages. -/
structure ReadRules (logic : BuilderLogic (Effect State Failure) State) : Prop where
  bind : ∀ {α β} before (result : Except Storage.ReadError α) (next : α → Effect State Failure β) post,
    logic.valid before →
    (∀ value, result = .ok value → logic.safe (next value) before post) →
    logic.safe (readAction result >>= next) before post

/-- Arithmetic errors use the existing safety-fault lift, not a normal miss. -/
theorem ReadRules.arithmetic (logic : BuilderLogic (Effect State Failure) State) (rules : ReadRules logic)
    (before : State) (result : Except Folding.Fault α) (next : α → Effect State Failure β) post
    (valid : logic.valid before)
    (continuation : ∀ value, result = .ok value → logic.safe (next value) before post) :
    logic.safe (arithmetic result >>= next) before post := by
  cases result with
  | ok value => exact continuation value rfl
  | error error =>
    apply rules.bind before (.error .safetyFault) next post valid
    intro value impossible
    cases impossible

/-- The child contract is required only when this source stage actually selects
it. Its request word, caller debug and initial state are fixed by that call. -/
def ConstantChild (logic : BuilderLogic (Effect State Failure) State) (reads : Reads)
    (constructors : Constructors Debug (Effect State Failure)) (instruction : Opcode)
    (arguments : List NodeId) (debug : Debug) (before : State) (expected : Word) : Prop :=
  ∀ values, arguments.length ≤ 3 → arguments ≠ [] →
    collectConstants reads arguments = .ok (some values) →
    Folding.run Folding.helpers Folding.clauses instruction values = .ok (some expected) →
    logic.safe (constructors.constant expected debug) before (fun id after => logic.read after id = some expected)

/-- Full folding-stage preservation, including arity skips, unknown constants
or opcodes and read/arithmetic/child failure. Only a normal miss returns the
initial state; successful children and failures keep their reached effects. -/
theorem constant_stage_safe (logic : BuilderLogic (Effect State Failure) State) (rules : ReadRules logic)
    (other : Meaning) (reads : Reads) (constructors : Constructors Debug (Effect State Failure))
    (instruction : Opcode) (arguments : List NodeId) (values : List Word) (expected : Word)
    (sequence : BitVec 32) (debug : Debug) (before : State) (valid : logic.valid before)
    (sound : Sound (Folding.wordMeaning other) (logic.read before) reads)
    (actual : readArguments (logic.read before) arguments = some values)
    (denotation : (Folding.wordMeaning other).operation instruction sequence values = some expected)
    (constant : ConstantChild logic reads constructors instruction arguments debug before expected) :
    logic.safe (constantStage reads constructors instruction arguments debug) before
      (fun result after => (∀ id, result = some id → logic.read after id = some expected) ∧
        (result = none → after = before)) := by
  unfold constantStage
  split
  · exact logic.pure before none _ valid (by simp)
  · rename_i enabled
    have bounded : arguments.length ≤ 3 := Nat.le_of_not_gt (fun large => enabled (Or.inl large))
    have nonempty : arguments ≠ [] := by intro empty; subst arguments; simp at enabled
    apply rules.bind before _ _ _ valid
    intro option collected
    cases option with
    | none => exact logic.pure before none _ valid (by simp)
    | some collectedValues =>
      apply rules.arithmetic logic before _ _ _ valid
      intro option folded
      cases option with
      | none => exact logic.pure before none _ valid (by simp)
      | some foldedValue =>
        have same := folded_value other (logic.read before) reads sound instruction arguments values expected foldedValue sequence
          actual denotation collected folded
        subst foldedValue
        apply logic.bind before _ _ _ _ (constant collectedValues bounded nonempty collected folded)
        intro result after validAfter _ resultRead
        exact logic.pure after (some result) _ validAfter
          ⟨by intro id equal; cases equal; exact resultRead, by simp⟩

omit [MonadLift (Except Error) (Effect State Failure)] in
/-- A source-derived miss equation lets the continuation reuse its original
query facts. A match or error retains the prefix's actual reached state. -/
theorem or_next_safe (logic : BuilderLogic (Effect State Failure) State)
    (stage next : Effect State Failure (Option NodeId)) (before : State) (post : NodeId → State → Prop)
    (first : logic.safe stage before (fun result after =>
      (∀ id, result = some id → post id after) ∧ (result = none → after = before)))
    (rest : logic.safe next before (fun result after => ∀ id, result = some id → post id after)) :
    logic.safe (orNext stage next) before (fun result after => ∀ id, result = some id → post id after) := by
  unfold orNext
  apply logic.bind before _ _ _ _ first
  intro result middle valid _ facts
  cases result with
  | none =>
    have same := facts.2 rfl
    subst middle
    exact rest
  | some id => exact logic.pure middle (some id) _ valid facts.1

/-- Logical clients use the existing read-failure proof. -/
def logicalReadRules (meaning : Meaning) : ReadRules (Interner.builderLogic meaning) where
  bind := fun before result next post valid continuation => read_action_bind_safe meaning before result next post valid continuation

end Preservation

theorem arithmetic_bind_safe (meaning : Meaning) (before : Heap) (result : Except Folding.Fault α)
    (next : α → Action β) (post : β → Heap → Prop) (valid : Invariant meaning before)
    (continuation : ∀ value, result = .ok value → Safe meaning (next value) before post) :
    Safe meaning (arithmetic result >>= next) before post := by
  exact Preservation.ReadRules.arithmetic (Interner.builderLogic meaning) (Preservation.logicalReadRules meaning)
    before result next post valid continuation

/-- The stack array in the native prefix is read only after all entries are
initialized. The extracted list has the same length and collected values. -/
theorem constant_stage_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (instruction : Opcode) (arguments : List NodeId)
    (values : List Word) (value : Word) (sequence : BitVec 32) (debug : Debug) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (actual : readArguments before.read arguments = some values)
    (denotation : (Folding.wordMeaning other).operation instruction sequence values = some value) :
    Safe (Folding.wordMeaning other) (constantStage reads constructors instruction arguments debug) before
      (fun result after => ∀ id, result = some id → after.read id = some value) := by
  have checked := Preservation.constant_stage_safe (Interner.builderLogic (Folding.wordMeaning other))
    (Preservation.logicalReadRules _) other reads constructors instruction arguments values value sequence debug before valid
    sound actual denotation (fun _ _ _ _ _ => correct.constant value debug before valid)
  intro result after ran
  have got := checked result after ran
  refine ⟨got.1, got.2.1, ?_⟩
  cases result with
  | error error => trivial
  | ok option => exact got.2.2.1

def MissUnchanged (action : Action (Option NodeId)) : Prop :=
  ∀ before after, action before = (.ok none, after) → after = before

def NeverMiss (action : Action (Option NodeId)) : Prop :=
  ∀ before after, action before ≠ (.ok none, after)

theorem never_miss_unchanged (action : Action (Option NodeId)) (terminal : NeverMiss action) :
    MissUnchanged action := fun before after missed => False.elim (terminal before after missed)

theorem bind_never_miss (action : Action α) (next : α → Action (Option NodeId))
    (terminal : ∀ value, NeverMiss (next value)) : NeverMiss (action >>= next) := by
  intro before after missed
  change Effect.bind action next before = _ at missed
  cases run : action before with
  | mk result middle =>
    cases result with
    | error error => simp [Effect.bind, run] at missed
    | ok value => exact terminal value middle after (by simpa [Effect.bind, run] using missed)

theorem terminal_never_miss (action : Action NodeId) : NeverMiss (do return some (← action)) := by
  apply bind_never_miss
  intro id before after missed
  change (Except.ok (some id), before) = (Except.ok none, after) at missed
  simp at missed

theorem pure_miss_unchanged (option : Option NodeId) : MissUnchanged (pure option) := by
  intro before after missed
  exact (Prod.mk.inj missed).2.symm

theorem terminal_miss_unchanged (action : Action NodeId) :
    MissUnchanged (do return some (← action)) :=
  never_miss_unchanged _ (terminal_never_miss action)

theorem read_miss_unchanged (result : Except Storage.ReadError α)
    (next : α → Action (Option NodeId)) (rest : ∀ value, MissUnchanged (next value)) :
    MissUnchanged (readAction result >>= next) := by
  cases result with
  | ok value => exact rest value
  | error error =>
    intro before after missed
    change Effect.bind (readAction (.error error)) next before = _ at missed
    cases error <;> simp [readAction, fail, Effect.bind] at missed

theorem arithmetic_miss_unchanged (result : Except Folding.Fault α)
    (next : α → Action (Option NodeId)) (rest : ∀ value, MissUnchanged (next value)) :
    MissUnchanged (arithmetic result >>= next) := by
  cases result with
  | ok value => exact rest value
  | error error =>
    intro before after missed
    change Effect.bind (arithmetic (.error error)) next before = _ at missed
    simp [arithmetic, fail, Effect.bind] at missed

theorem constant_stage_miss (reads : Reads) (constructors : Constructors Debug)
    (instruction : Opcode) (arguments : List NodeId) (debug : Debug) :
    MissUnchanged (constantStage reads constructors instruction arguments debug) := by
  unfold constantStage
  repeat first
    | exact pure_miss_unchanged _
    | exact terminal_miss_unchanged _
    | apply read_miss_unchanged; intro option
    | apply arithmetic_miss_unchanged; intro option
    | split

/-- A read-only miss lets the next stage reuse the original read-soundness
premise. Stability alone would not justify arbitrary equality callbacks after
heap growth. Successful matches and failures retain their actual final heaps. -/
theorem or_next_safe_of_unchanged (meaning : Meaning) (stage next : Action (Option NodeId)) (before : Heap)
    (post : NodeId → Heap → Prop)
    (first : Safe meaning stage before (fun result after => ∀ id, result = some id → post id after))
    (unchanged : MissUnchanged stage)
    (rest : Safe meaning next before (fun result after => ∀ id, result = some id → post id after)) :
    Safe meaning (orNext stage next) before (fun result after => ∀ id, result = some id → post id after) := by
  have first' : Safe meaning stage before (fun result after =>
      (∀ id, result = some id → post id after) ∧ (result = none → after = before)) := by
    intro outcome after run
    obtain ⟨valid, stable, actual⟩ := first outcome after run
    refine ⟨valid, stable, ?_⟩
    cases outcome with
    | error error => trivial
    | ok result =>
      refine ⟨actual, ?_⟩
      intro miss
      subst result
      exact unchanged before after run
  exact Preservation.or_next_safe (Interner.builderLogic meaning) stage next before post first' rest

theorem or_next_miss_unchanged (stage next : Action (Option NodeId))
    (first : MissUnchanged stage) (rest : MissUnchanged next) : MissUnchanged (orNext stage next) := by
  intro before after missed
  change Effect.bind stage (fun result => match result with
    | some id => pure (some id) | none => next) before = _ at missed
  cases run : stage before with
  | mk result middle =>
    cases result with
    | error error => simp [Effect.bind, run] at missed
    | ok option =>
      cases option with
      | none => exact (rest middle after (by simpa [Effect.bind, run] using missed)).trans (first before middle run)
      | some id =>
        simp only [Effect.bind, run] at missed
        change (Except.ok (some id), middle) = (Except.ok none, after) at missed
        simp at missed

theorem optional_bind_eq (stage : Action (Option NodeId)) (next : Option NodeId → Action (Option NodeId))
    (matched : ∀ id, next (some id) = pure (some id)) :
    (stage >>= next) = orNext stage (next none) := by
  unfold orNext
  apply congrArg (fun tail : Option NodeId → Action (Option NodeId) => stage >>= tail)
  funext option
  cases option with
  | none => rfl
  | some id => exact matched id

theorem optional_bind_safe_of_unchanged (meaning : Meaning) (stage : Action (Option NodeId))
    (next : Option NodeId → Action (Option NodeId)) (before : Heap) (post : NodeId → Heap → Prop)
    (first : Safe meaning stage before (fun result after => ∀ id, result = some id → post id after))
    (unchanged : MissUnchanged stage) (matched : ∀ id, next (some id) = pure (some id))
    (rest : Safe meaning (next none) before (fun result after => ∀ id, result = some id → post id after)) :
    Safe meaning (stage >>= next) before (fun result after => ∀ id, result = some id → post id after) := by
  rw [optional_bind_eq stage next matched]
  exact or_next_safe_of_unchanged meaning stage (next none) before post first unchanged rest

theorem optional_bind_miss_unchanged (stage : Action (Option NodeId))
    (next : Option NodeId → Action (Option NodeId)) (first : MissUnchanged stage)
    (matched : ∀ id, next (some id) = pure (some id)) (rest : MissUnchanged (next none)) :
    MissUnchanged (stage >>= next) := by
  rw [optional_bind_eq stage next matched]
  exact or_next_miss_unchanged stage (next none) first rest

/-- Binary inputs share this complete stage composition. Each opcode family
must still prove its entire binary stage, exact normal-miss state, and every
enabled revision-stage outcome; no unproved stage is skipped. -/
theorem binary_simplify_safe (other : Meaning) (reads : Reads) (constructors : Constructors Debug)
    (correct : ConstructorSound other constructors) (before : Heap)
    (valid : Invariant (Folding.wordMeaning other) before)
    (sound : Sound (Folding.wordMeaning other) before.read reads)
    (instruction : Opcode) (left right : NodeId) (a b expected : Word) (sequence : BitVec 32)
    (debug : Debug) (options : Options) (usizeBits : Nat)
    (lhs : before.read left = some a) (rhs : before.read right = some b)
    (denotation : (Folding.wordMeaning other).operation instruction sequence [a, b] = some expected)
    (binary : Safe (Folding.wordMeaning other) (binaryStage reads constructors usizeBits instruction left right debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some expected))
    (missed : MissUnchanged (binaryStage reads constructors usizeBits instruction left right debug options))
    (revision : ∀ version, options.evmVersion = some version →
      Safe (Folding.wordMeaning other) (evmStage reads constructors usizeBits instruction [left, right] debug version) before
        (fun result after => ∀ id, result = some id → after.read id = some expected)) :
    Safe (Folding.wordMeaning other) (simplifyWithOptions reads constructors usizeBits instruction [left, right] debug options) before
      (fun result after => ∀ id, result = some id → after.read id = some expected) := by
  unfold simplifyWithOptions simplifyOptionsWithInputs
  simp only [← binaryStage.eq_def, ← unaryStage.eq_def, ← evmStage.eq_def]
  apply or_next_safe_of_unchanged _ _ _ before _
    (constant_stage_safe other reads constructors correct instruction [left, right] [a, b] expected sequence debug before valid sound
      (by simp [readArguments, lhs, rhs]) denotation)
    (constant_stage_miss reads constructors instruction [left, right] debug)
  apply or_next_safe_of_unchanged _ _ _ before _ binary missed
  change Safe _ (match options.evmVersion with
    | some version => evmStage reads constructors usizeBits instruction [left, right] debug version
    | none => pure none) before _
  cases choice : options.evmVersion with
  | none => exact Safe.pure _ before none _ valid (by simp)
  | some version => exact revision version choice

theorem default_options : defaultOptions = ({} : Options) := rfl

theorem revision_gates (version : Version) :
    hasBitwiseShifting version =
      (match version with | .homestead | .tangerineWhistle | .spuriousDragon | .byzantium => false | _ => true) ∧
    hasSelfBalance version =
      (match version with | .homestead | .tangerineWhistle | .spuriousDragon | .byzantium | .constantinople | .petersburg => false | _ => true) := by
  cases version <;> exact ⟨rfl, rfl⟩

end Compiler.Extraction.Dispatch
