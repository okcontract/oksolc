/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.Graph

/-! An ownership-sensitive instruction language for the actual insertion
transaction. Allocator/container/clone primitives have explicit atomic contracts:
failure leaves their input resources intact; success allocates fresh disjoint
storage or publishes the given value. The initialized item is a logical owned
resource even when its payload needs no allocation. This models ownership and
cleanup, not addresses, allocator internals or arbitrary mutable aliases. -/
namespace Compiler.Extraction.Storage

inductive Resource where
  | normalized | arguments | allocation | value
  deriving DecidableEq, BEq, Repr

inductive Owner where
  | absent | local | graph | table | freed
  deriving DecidableEq, BEq, Repr

structure State where
  owner : Resource → Owner := fun r => if r == .normalized then .local else .absent
  flag : Resource → Bool := fun _ => false
  aliasesNormalized : Bool := false
  appended : Bool := false
  published : Bool := false
  capturedId : Bool := false
  invalid : Bool := false

def State.setFlag (s : State) (resource : Resource) (value : Bool) : State :=
  { s with flag := fun r => if r == resource then value else s.flag r }

def State.move (s : State) (resource : Resource) (before after : Owner) : State :=
  if s.owner resource == before then
    { s with owner := fun r => if r == resource then after else s.owner r }
  else { s with invalid := true }

def State.argument (s : State) : Resource :=
  if s.aliasesNormalized then .normalized else .arguments

inductive Allocation where
  | arguments | item | clone | append | publish
  deriving DecidableEq, BEq, Repr

structure Input where
  deterministic : Bool
  room : Bool
  succeeds : Allocation → Bool

inductive Command where
  | flag (resource : Resource) (value : Bool)
  | duplicateArguments | aliasArguments | createItem | cloneItem
  | captureId | append | publish
  deriving DecidableEq, Repr

def Command.allocation : Command → Option Allocation
  | .duplicateArguments => some .arguments
  | .createItem => some .item
  | .cloneItem => some .clone
  | .append => some .append
  | .publish => some .publish
  | _ => none

def Command.success (input : Input) (s : State) : Command → State
  | .flag resource value => s.setFlag resource value
  | .duplicateArguments => s.move .arguments .absent .local
  | .aliasArguments => { s with aliasesNormalized := true }
  | .createItem => s.move .allocation .absent .local
  | .cloneItem =>
    if s.owner .allocation == .local then s.move .value .absent .local
    else { s with invalid := true }
  | .captureId => { s with capturedId := true, invalid := s.invalid || !input.room }
  | .append =>
    let after := ((s.move s.argument .local .graph).move .allocation .local .graph).move .value .local .graph
    { after with appended := true, invalid := after.invalid || s.appended || !s.capturedId }
  | .publish =>
    let after := s.move .normalized .local .table
    { after with published := true, invalid := after.invalid || !s.appended }

/-- A fallible primitive may update private effect state on either outcome.
The ownership transition itself still uses the existing atomic contract. -/
def Command.runWith (input : Input) (attempt : Allocation → σ → Bool × σ)
    (command : Command) (s : State) (effects : σ) : (Bool × State) × σ :=
  match command.allocation with
  | some site =>
    let (ok, after) := attempt site effects
    ((ok, if ok then command.success input s else s), after)
  | none => ((true, command.success input s), effects)

def Command.run (input : Input) (command : Command) (s : State) : Bool × State :=
  (command.runWith input (fun site (_ : Unit) => (input.succeeds site, ())) s ()).1

inductive Release where
  | normalized | arguments | allocation | value | lastValue | pop
  deriving DecidableEq, Repr

def Release.run (s : State) : Release → State
  | .normalized => s.move .normalized .local .freed
  | .arguments => s.move s.argument .local .freed
  | .allocation =>
    if s.owner .value == .absent || s.owner .value == .freed then
      s.move .allocation .local .freed
    else { s with invalid := true }
  | .value => s.move .value .local .freed
  | .lastValue =>
    let after := ((s.move s.argument .graph .freed).move .value .graph .freed).move .allocation .graph .freed
    { after with invalid := after.invalid || !s.appended || s.published }
  | .pop =>
    { s with appended := false, invalid := s.invalid || !s.appended || s.published ||
      !(s.owner s.argument == .freed && s.owner .allocation == .freed && s.owner .value == .freed) }

inductive Cleanup where
  | guarded (flag : Resource) (release : Release)
  | sequence (releases : List Release)
  deriving DecidableEq, Repr

def Cleanup.run (cleanup : Cleanup) (s : State) : State :=
  match cleanup with
  | .guarded flag release => if s.flag flag then release.run s else s
  | .sequence releases => releases.foldl (fun state release => release.run state) s

inductive Outcome where
  | success | allocationFailure | capacityFailure
  deriving DecidableEq, BEq, Repr

inductive Test where
  | deterministic | noRoom
  deriving DecidableEq, Repr

def Test.eval (input : Input) : Test → Bool
  | .deterministic => input.deterministic
  | .noRoom => !input.room

inductive Program where
  | done
  | ret
  | capacityError
  | command (command : Command) (next : Program)
  | branch (test : Test) (yes no next : Program)
  | scope (errorOnly : Bool) (cleanup : Cleanup) (body : Program)
  deriving DecidableEq, Repr

/-- `none` is local fallthrough; an outcome exits the function. Deferred cleanup
runs in reverse registration order, with errdefer skipped only on success.
Private primitive effects survive cleanup and errors. `input.succeeds` is used
only by the state-independent `run` wrapper; this interpreter uses `attempt`. -/
def Program.runWith (input : Input) (attempt : Allocation → σ → Bool × σ) :
    Program → State → σ → (Option Outcome × State) × σ
  | .done, state, effects => ((none, state), effects)
  | .ret, state, effects => ((some .success, { state with invalid := state.invalid || !state.capturedId }), effects)
  | .capacityError, state, effects => ((some .capacityFailure, state), effects)
  | .command action next, state, effects =>
    let ((ok, after), effects) := action.runWith input attempt state effects
    if ok then next.runWith input attempt after effects else ((some .allocationFailure, after), effects)
  | .branch test yes no next, state, effects =>
    let ((outcome, after), effects) :=
      if test.eval input then yes.runWith input attempt state effects else no.runWith input attempt state effects
    match outcome with
    | none => next.runWith input attempt after effects
    | some result => ((some result, after), effects)
  | .scope errorOnly cleanup body, state, effects =>
    let ((outcome, after), effects) := body.runWith input attempt state effects
    if errorOnly && (outcome == some .success || outcome == none) then ((outcome, after), effects)
    else ((outcome, cleanup.run after), effects)

def Program.run (input : Input) (program : Program) (state : State) : Option Outcome × State :=
  (program.runWith input (fun site (_ : Unit) => (input.succeeds site, ())) state ()).1

def Released (state : State) : Prop :=
  state.invalid = false ∧ state.appended = false ∧ state.published = false ∧
    ∀ resource, state.owner resource = .absent ∨ state.owner resource = .freed

def Published (deterministic : Bool) (state : State) : Prop :=
  state.invalid = false ∧ state.appended = true ∧ state.capturedId = true ∧
    state.published = deterministic ∧ state.owner .allocation = .graph ∧
    state.owner .value = .graph ∧
    if deterministic then state.owner .normalized = .table ∧ state.owner .arguments = .graph
    else state.owner .normalized = .graph ∧ state.owner .arguments = .absent

def SafeResult (deterministic : Bool) : Option Outcome × State → Prop
  | (some .success, state) => Published deterministic state
  | (some .allocationFailure, state) => Released state
  | (some .capacityFailure, state) => Released state
  | (none, _) => False

instance (p : Resource → Prop) [DecidablePred p] : Decidable (∀ r, p r) :=
  decidable_of_iff (p .normalized ∧ p .arguments ∧ p .allocation ∧ p .value)
    ⟨fun h r => by cases r <;> simp_all, fun h => ⟨h _, h _, h _, h _⟩⟩

instance (state : State) : Decidable (Released state) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
instance (d : Bool) (state : State) : Decidable (Published d state) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))
instance (d : Bool) (result : Option Outcome × State) : Decidable (SafeResult d result) := by
  rcases result with ⟨outcome, state⟩
  cases outcome with
  | none => exact inferInstanceAs (Decidable False)
  | some result => cases result with
    | success => exact inferInstanceAs (Decidable (Published d state))
    | allocationFailure => exact inferInstanceAs (Decidable (Released state))
    | capacityFailure => exact inferInstanceAs (Decidable (Released state))

end Compiler.Extraction.Storage
