/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.DispatchEffects
import Compiler.Extraction.DispatchDefaultProofs
import Compiler.Extraction.InternerPhysicalDispatch

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Recursive
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray

/-- Ordinary outcomes preserve the predicate at the actual reached world.
Rejected semantic faults impose no invented cleanup or rollback observation. -/
def Keeps (predicate : World σ → Prop) (action : GraphAction σ α) : Prop :=
  ∀ before, predicate before → ordinary (action before).1 = true → predicate (action before).2

theorem keeps_bind (predicate : World σ → Prop) (first : GraphAction σ α) (next : α → GraphAction σ β)
    (initial : Keeps predicate first) (following : ∀ value, Keeps predicate (next value)) :
    Keeps predicate (first >>= next) := by
  intro before held completed
  cases ran : first before with
  | mk result middle =>
    cases result with
    | error fault =>
      simpa only [bind, Effect.bind, ran] using initial before held (by simpa only [bind, Effect.bind, ran] using completed)
    | ok value =>
      have kept := initial before held (by rw [ran]; rfl)
      rw [ran] at kept
      simpa only [bind, Effect.bind, ran] using following value middle kept (by simpa only [bind, Effect.bind, ran] using completed)

def keeping (predicate : World σ → Prop) : Dispatch.Effects (GraphAction σ) (GraphAction σ) where
  related := fun action _ => Keeps predicate action
  pure := fun _ _ held _ => held
  bind := fun first following => keeps_bind predicate _ _ first following
  lift := fun _ _ held _ => held

theorem constructors_keep (predicate : World σ → Prop) (find : Find σ)
    (borrow : ∀ request, Keeps predicate (find request)) :
    (keeping predicate).Constructors (constructors (Debug := Unit) find) (constructors find) :=
  ⟨fun _ _ _ => borrow _, fun _ _ => borrow _, fun _ _ _ => borrow _, fun _ _ _ _ => borrow _, fun _ _ _ _ _ _ => borrow _⟩

/-- Discharge the caller's simplify ownership field for the complete generated
dispatcher. Only recursive constructors, not simplification itself, are assumed
to preserve the borrowed caller slice. -/
theorem simplify_borrows (allocator : Nat) (source : View) (values : List NodeId)
    (p : Primitives σ) (reads : Interner.Heap → Nested.Reads) (usizeBits : Nat) (find : Find σ)
    (borrow : ∀ slice request, Keeps (Held allocator source values slice) (find request))
    (key : Key) (slice : ArgumentSlice) (before : World σ) (held : Held allocator source values slice before) :
    let executed := (callbacks p reads usizeBits find).simplify key slice before
    ordinary executed.1 = true → Held allocator source values slice executed.2 :=
  (keeping (Held allocator source values slice)).simplify
    (constructors_keep _ find (borrow slice)) (reads before.graph) usizeBits key.instruction key.arguments () before held

/-- Exact ordinary simulation under a fixed observation of physical state.
The state types may include invocation-local scopes. The observation is chosen
before the action; bind compares the actual reached state, including any
resource cursor advanced by a proper child. -/
def ProjectsAt (observe : Native → Model) (predicate : Native → Prop)
    (physical : Effect Native Fault α) (logical : Effect Model Interner.Error α) : Prop :=
  ∀ before, predicate before → ordinary (physical before).1 = true →
    predicate (physical before).2 ∧
    (physical before).1 = (logical (observe before)).1.mapError Fault.language ∧
    observe (physical before).2 = (logical (observe before)).2

/-- The legacy graph observation remains a specialization. It does not imply
that allocator effects outside `World.graph` have stopped advancing. -/
def Projects (predicate : World σ → Prop) (physical : GraphAction σ α) (logical : Interner.Action α) : Prop :=
  ProjectsAt World.graph predicate physical logical

/-- Observe a native effect cursor without erasing any graph field. Production
use must bind `cursor` to the complete invocation's actual resource events. -/
def cursorGraph (cursor : World σ → Nat) (world : World σ) : Interner.Heap :=
  { world.graph with allocationCursor := cursor world }

/-- The first action may require facts specific to its actual input. Only its
reached predicate is needed by following actions. This is the same ordinary
bind proof used by the invariant-preserving interface below. -/
theorem projects_at_bind_from (observe : Native → Model) (predicate : Native → Prop)
    (first : Effect Native Fault α) (model : Effect Model Interner.Error α)
    (next : α → Effect Native Fault β) (nextModel : α → Effect Model Interner.Error β)
    (before : Native)
    (initial : ordinary (first before).1 = true → predicate (first before).2 ∧
      (first before).1 = (model (observe before)).1.mapError Fault.language ∧
      observe (first before).2 = (model (observe before)).2)
    (following : ∀ value, ProjectsAt observe predicate (next value) (nextModel value)) :
    ordinary ((first >>= next) before).1 = true → predicate ((first >>= next) before).2 ∧
      ((first >>= next) before).1 = ((model >>= nextModel) (observe before)).1.mapError Fault.language ∧
      observe ((first >>= next) before).2 = ((model >>= nextModel) (observe before)).2 := by
  intro completed
  cases ran : first before with
  | mk result middle =>
    cases modelRan : model (observe before) with
    | mk modelResult modelMiddle =>
      cases result with
      | error fault =>
        have checked := initial (by simpa only [bind, Effect.bind, ran] using completed)
        simp only [ran, modelRan] at checked
        cases modelResult with
        | ok value => cases checked.2.1
        | error error =>
          simpa only [bind, Effect.bind, ran, modelRan, Except.mapError, Except.error.injEq] using checked
      | ok value =>
        have checked := initial (by rw [ran]; rfl)
        simp only [ran, modelRan] at checked
        cases modelResult with
        | error error => cases checked.2.1
        | ok modelValue =>
          have equal : value = modelValue := Except.ok.inj checked.2.1
          subst modelValue
          have final := following value middle checked.1 (by simpa only [bind, Effect.bind, ran] using completed)
          simpa only [bind, Effect.bind, ran, modelRan, checked.2.2] using final

theorem projects_at_bind (observe : Native → Model) (predicate : Native → Prop)
    (first : Effect Native Fault α) (model : Effect Model Interner.Error α)
    (next : α → Effect Native Fault β) (nextModel : α → Effect Model Interner.Error β)
    (initial : ProjectsAt observe predicate first model) (following : ∀ value, ProjectsAt observe predicate (next value) (nextModel value)) :
    ProjectsAt observe predicate (first >>= next) (model >>= nextModel) :=
  fun before held => projects_at_bind_from observe predicate first model next nextModel before (initial before held) following

/-- The original bind theorem uses the same reached-state composition. -/
theorem projects_bind (predicate : World σ → Prop) (first : GraphAction σ α) (model : Interner.Action α)
    (next : α → GraphAction σ β) (nextModel : α → Interner.Action β)
    (initial : Projects predicate first model) (following : ∀ value, Projects predicate (next value) (nextModel value)) :
    Projects predicate (first >>= next) (model >>= nextModel) :=
  projects_at_bind World.graph predicate first model next nextModel initial following

/-- Reuse the dispatcher effect algebra with an explicit physical observation. -/
def projectionAt (observe : World σ → Interner.Heap) (predicate : World σ → Prop) :
    Dispatch.Effects (GraphAction σ) Interner.Action where
  related := ProjectsAt observe predicate
  pure := fun _ _ held _ => ⟨held, rfl, rfl⟩
  bind := fun first following => projects_at_bind observe predicate _ _ _ _ first following
  lift := fun _ _ held _ => ⟨held, rfl, rfl⟩

def projection (predicate : World σ → Prop) : Dispatch.Effects (GraphAction σ) Interner.Action where
  related := Projects predicate
  pure := fun _ _ held _ => ⟨held, rfl, rfl⟩
  bind := fun first following => projects_bind predicate _ _ _ _ first following
  lift := fun _ _ held _ => ⟨held, rfl, rfl⟩

/-- Transfer a logical word proof at one actual execution. The observation may
include a resource cursor; callers retain exact result and reached-state binding. -/
theorem safe_at (meaning : Meaning) (before after : Interner.Heap) (result : Except Fault α)
    (logical : Interner.Action α) (post : α → Interner.Heap → Prop)
    (projected : ordinary result = true → result = (logical before).1.mapError Fault.language ∧ after = (logical before).2)
    (safe : Interner.Safe meaning logical before post) : Semantic.Ensures meaning before result after post := by
  intro completed
  have checked := projected completed
  rw [checked.1, checked.2]
  have valid := safe (logical before).1 (logical before).2 rfl
  cases outcome : (logical before).1 <;> simpa only [outcome, Except.mapError] using valid

theorem ProjectsAt.safe (observe : World σ → Interner.Heap) (predicate : World σ → Prop) (physical : GraphAction σ α) (logical : Interner.Action α)
    (related : ProjectsAt observe predicate physical logical) (meaning : Meaning) (before : World σ)
    (held : predicate before) (post : α → Interner.Heap → Prop)
    (safe : Interner.Safe meaning logical (observe before) post) :
    Semantic.Ensures meaning (observe before) (physical before).1 (observe (physical before).2) post :=
  safe_at meaning (observe before) (observe (physical before).2) (physical before).1 logical post
    (fun completed => (related before held completed).2) safe

/-- The graph-only semantic client specializes the observed-state proof. -/
theorem Projects.safe (predicate : World σ → Prop) (physical : GraphAction σ α) (logical : Interner.Action α)
    (related : Projects predicate physical logical) (meaning : Meaning) (before : World σ)
    (held : predicate before) (post : α → Interner.Heap → Prop)
    (safe : Interner.Safe meaning logical before.graph post) :
    Semantic.Ensures meaning before.graph (physical before).1 (physical before).2.graph post :=
  ProjectsAt.safe World.graph predicate physical logical related meaning before held post safe

/-- Exact simulation keeps the advancing resource cursor. Its semantic result
then transfers to the actual native graph for a read-based postcondition. No
raw-graph equality or unchanged resource position is assumed. -/
theorem ProjectsAt.safe_cursor (cursor : World σ → Nat) (predicate : World σ → Prop)
    (physical : GraphAction σ α) (logical : Interner.Action α)
    (related : ProjectsAt (cursorGraph cursor) predicate physical logical) (meaning : Meaning) (before : World σ)
    (held : predicate before) (post : α → Read → Prop)
    (safe : Interner.Safe meaning logical (cursorGraph cursor before) (fun value heap => post value heap.read)) :
    Semantic.Ensures meaning before.graph (physical before).1 (physical before).2.graph
      (fun value heap => post value heap.read) :=
  (Semantic.Ensures.cursor_iff meaning before.graph (physical before).2.graph (physical before).1
    (cursor before) (cursor (physical before).2) post).mp
    (ProjectsAt.safe (cursorGraph cursor) predicate physical logical related meaning before held _ safe)

/-- The full dispatcher consumes proper-child simulation at the observed
resource position and derives the same native borrow and word conclusions.
The actual read snapshot is preserved; only its logical cursor is supplied by
the complete execution's observer. -/
theorem simplify_verified_cursor (cursor : World σ → Nat) (predicate : World σ → Prop) (p : Primitives σ)
    (reads : Interner.Heap → Nested.Reads) (usizeBits : Nat) (find : Find σ)
    (model : Associative.Constructors Unit)
    (coupled : (projectionAt (cursorGraph cursor) predicate).Constructors (constructors find) model)
    (env : AddressMask.Environment) (other : Meaning)
    (correct : Associative.ConstructorSound (Dispatch.wordBaseMeaning env other) model)
    (addresses : AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) model.operation)
    (shifts : ArithmeticShift.Constructs (AddressMask.addressMeaning env other) model.operation)
    (key : Key) (slice : ArgumentSlice) (before : World σ) (expected : Word)
    (held : predicate before) (operation : key.kind = 1)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
    (sound : Nested.Sound (Dispatch.wordDispatchMeaning env other) before.graph.read (reads before.graph))
    (evaluated : key.eval (Dispatch.wordDispatchMeaning env other) before.graph.read = some expected) :
    let executed := (callbacks p reads usizeBits find).simplify key slice before
    (ordinary executed.1 = true → predicate executed.2) ∧
    Semantic.Ensures (Dispatch.wordDispatchMeaning env other) before.graph executed.1 executed.2.graph
      (fun found after => ∀ id, found = some id → after.read id = some expected) := by
  have related := (projectionAt (cursorGraph cursor) predicate).simplify coupled (reads before.graph)
    usizeBits key.instruction key.arguments ()
  exact ⟨fun completed => (related before held completed).1,
    ProjectsAt.safe_cursor cursor predicate _ _ related (Dispatch.wordDispatchMeaning env other) before held
      (fun found read => ∀ id, found = some id → read id = some expected)
      (Dispatch.default_key_simplify_safe env other _ model correct addresses shifts
        (cursorGraph cursor before) (valid.with_cursor (cursor before)) sound key operation expected () usizeBits evaluated)⟩

/-- Transfer the existing universal word proof to the same physical dispatcher
execution, under exact constructor simulation. Native recursive constructor
simulation and graph implementation are still obligations, not axioms. -/
theorem simplify_verified (predicate : World σ → Prop) (p : Primitives σ)
    (reads : Interner.Heap → Nested.Reads) (usizeBits : Nat) (find : Find σ)
    (model : Associative.Constructors Unit) (coupled : (projection predicate).Constructors (constructors find) model)
    (env : AddressMask.Environment) (other : Meaning)
    (correct : Associative.ConstructorSound (Dispatch.wordBaseMeaning env other) model)
    (addresses : AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) model.operation)
    (shifts : ArithmeticShift.Constructs (AddressMask.addressMeaning env other) model.operation)
    (key : Key) (slice : ArgumentSlice) (before : World σ) (expected : Word)
    (held : predicate before) (operation : key.kind = 1)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
    (sound : Nested.Sound (Dispatch.wordDispatchMeaning env other) before.graph.read (reads before.graph))
    (evaluated : key.eval (Dispatch.wordDispatchMeaning env other) before.graph.read = some expected) :
    let executed := (callbacks p reads usizeBits find).simplify key slice before
    (ordinary executed.1 = true → predicate executed.2) ∧
    Semantic.Ensures (Dispatch.wordDispatchMeaning env other) before.graph executed.1 executed.2.graph
      (fun found after => ∀ id, found = some id → after.read id = some expected) := by
  exact simplify_verified_cursor (fun world => world.graph.allocationCursor) predicate p reads usizeBits find model
    coupled env other correct addresses shifts key slice before expected held operation valid sound evaluated

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Recursive
