/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPhysicalDispatchPreservation
import Compiler.Extraction.InternerPhysicalDispatchTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Recursive.PreservationTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open Normalization.Tests

/-- A concrete simulation fixture: logical recursive construction changes the
graph, and each physical call records an effect. This is not native argument
preparation or the missing simulation for recursive physical Caller.find. -/
def counted (action : Interner.Action α) : GraphAction Nat α := fun before =>
  let (result, graph) := action before.graph
  (result.mapError Fault.language, { before with graph, memory := { before.memory with effects := before.memory.effects + 1 } })

theorem counted_projects (allocator : Nat) (source : View) (values : List NodeId) (slice : ArgumentSlice)
    (action : Interner.Action α) : Projects (Held allocator source values slice) (counted action) action := by
  intro before held _completed
  cases ran : action before.graph with
  | mk result graph =>
    simp only [counted, ran]
    exact ⟨⟨⟨⟨held.1.1.memory, held.1.1.related, held.1.1.injected⟩, held.1.2⟩, held.2⟩, trivial, trivial⟩

def outerSlice : ArgumentSlice := ⟨4, [1, 2, 3]⟩
def prepared := (observed true source items .transfer).2
def world : World Nat := ⟨Compiler.Extraction.Recursive.Tests.initial, prepared⟩
def borrowed : World Nat → Prop := Held 7 source items outerSlice

theorem outer_held : borrowed world := by
  have checked := full_contract .transfer 160
  generalize executed : Normalization.run normalizationOwnershipCode success 160 7 true source buffer items .transfer before = outcome at checked
  rcases outcome with ⟨result, after⟩
  have observedEq : observed true source items .transfer = (result, after) := executed
  have accepted := allocated_transfer.1
  rw [observedEq] at accepted
  have verified := checked.1.verified
  dsimp only at accepted
  rw [accepted] at verified
  have same : prepared = after := congrArg Prod.snd observedEq
  dsimp only [borrowed, world]
  rw [same]
  exact ⟨⟨verified.1, verified.2.1⟩, verified.2.2.2.2.2, by intro _; decide⟩

def logical (depth : Nat) := Compiler.Extraction.Recursive.unfold
  Compiler.Extraction.Recursive.Tests.primitives Compiler.Extraction.Recursive.Tests.reads 64 depth
def physical (depth : Nat) : Find Nat := fun request => counted (logical depth request)

theorem coupled (depth : Nat) : (projection borrowed).Constructors (constructors (physical depth))
    (Compiler.Extraction.Recursive.constructors (Debug := Unit) (logical depth)) :=
  ⟨fun _ _ _ => counted_projects _ _ _ _ _, fun _ _ => counted_projects _ _ _ _ _,
    fun _ _ _ => counted_projects _ _ _ _ _, fun _ _ _ _ => counted_projects _ _ _ _ _, fun _ _ _ _ _ _ => counted_projects _ _ _ _ _⟩

theorem logical_sound (depth : Nat) : Compiler.Extraction.Recursive.FindSound Compiler.Extraction.Recursive.Tests.model (logical depth) :=
  Compiler.Extraction.Recursive.unfold_safe _ _ Compiler.Extraction.Recursive.Tests.pushes _
    Compiler.Extraction.Recursive.Tests.primitive_contracts _ (fun heap _ => Compiler.Extraction.Recursive.Tests.reads_sound heap) 64 depth

def key : Key := ⟨1, 1, 0, [0, 1], 77⟩
def run (depth : Nat) := (callbacks (Tests.seed false) Compiler.Extraction.Recursive.Tests.reads 64 (physical depth)).simplify key outerSlice world

/-- Every finite logical recursive unfolding instantiates the same physical
dispatcher theorem, with an inhabited nonempty outer borrow. -/
theorem all_depths_verified (depth : Nat) :
    (ordinary (run depth).1 = true → borrowed (run depth).2) ∧
    Semantic.Ensures Compiler.Extraction.Recursive.Tests.model world.graph (run depth).1 (run depth).2.graph
      (fun found after => ∀ id, found = some id → after.read id = some 42) := by
  have words := Compiler.Extraction.Recursive.constructors_sound
    (Dispatch.wordBaseMeaning Compiler.Extraction.Recursive.Tests.env Compiler.Extraction.Recursive.Tests.base)
    Compiler.Extraction.Recursive.Tests.pushes (logical depth) (logical_sound depth) (Debug := Unit)
  have addresses := Compiler.Extraction.Recursive.constructors_address Compiler.Extraction.Recursive.Tests.env
    (ArithmeticShift.shiftMeaning Compiler.Extraction.Recursive.Tests.base) (logical depth)
    (by simpa only [Compiler.Extraction.Recursive.Tests.model, Dispatch.word_dispatch_address_model] using logical_sound depth) (Debug := Unit)
  have shifts := Compiler.Extraction.Recursive.constructors_sar
    (AddressMask.addressMeaning Compiler.Extraction.Recursive.Tests.env Compiler.Extraction.Recursive.Tests.base)
    (logical depth) (logical_sound depth) (Debug := Unit)
  exact simplify_verified borrowed (Tests.seed false) Compiler.Extraction.Recursive.Tests.reads 64 (physical depth)
    _ (coupled depth) _ _ words addresses shifts key outerSlice world 42 outer_held rfl
    ⟨(by intro _ _ impossible; cases impossible), trivial⟩
    (Compiler.Extraction.Recursive.Tests.reads_sound _) (by rfl')

theorem success_observation : (run 1).1 = .ok (some 7) ∧ (run 1).2.graph.read 7 = some 42 ∧
    (run 1).2.memory.effects = world.memory.effects + 1 ∧ (run 1).2.memory.heap 4 = some ⟨7, .arguments [1, 2, 3]⟩ :=
  ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem success_borrows : borrowed (run 1).2 := (all_depths_verified 1).1 rfl

theorem cutoff_retains_effects : (run 0).1 = .error (.language .unsupported) ∧ ordinary (run 0).1 = false ∧
    (run 0).2.memory.effects = world.memory.effects + 1 := ⟨by rfl', by rfl', by rfl'⟩

def failing : Find Nat := fun _ => counted (Interner.fail .outOfMemory)
def failed := (callbacks (Tests.seed false) Compiler.Extraction.Recursive.Tests.reads 64 failing).simplify key outerSlice world

theorem ordinary_failure_borrows : borrowed failed.2 :=
  simplify_borrows 7 source items (Tests.seed false) Compiler.Extraction.Recursive.Tests.reads 64 failing
    (fun slice _request before held completed => (counted_projects 7 source items slice _ before held completed).1)
    key outerSlice world outer_held rfl

theorem ordinary_failure_effects : failed.1 = .error (.language .outOfMemory) ∧
    failed.2.memory.effects = world.memory.effects + 1 := ⟨by rfl', by rfl'⟩

theorem changed_result_rejected : ¬Projects borrowed (pure (8 : NodeId)) (pure 7) := by
  intro related
  have checked := related world outer_held rfl
  have impossible : (8 : NodeId) = 7 := Except.ok.inj checked.2.1
  contradiction

def changedGraph : GraphAction Nat NodeId := fun before =>
  (.ok 7, { before with graph := { before.graph with read := fun _ => none } })

theorem changed_graph_rejected : ¬Projects borrowed changedGraph (pure 7) := by
  intro related
  have impossible := congrArg (fun heap => heap.read 0) (related world outer_held rfl).2.2
  contradiction

/-- Interface fixture for an effect cursor outside the graph. This is not a
native allocator trace or the missing whole-invocation resource coupling. -/
def advance (result : Except Interner.Error α) : GraphAction Nat α := fun before =>
  (result.mapError Fault.language, { before with memory := { before.memory with effects := before.memory.effects + 1 } })

def advanceModel (result : Except Interner.Error α) : Interner.Action α :=
  Interner.liftLocal (fun cursor => (result, cursor + 1))

def observed : World Nat → Interner.Heap := cursorGraph (fun world => world.memory.effects)

theorem advance_projects_held (allocator : Nat) (source : View) (values : List NodeId) (slice : ArgumentSlice)
    (result : Except Interner.Error α) :
    ProjectsAt observed (Held allocator source values slice) (advance result) (advanceModel result) := by
  intro before held _completed
  exact ⟨⟨⟨⟨held.1.1.memory, held.1.1.related, held.1.1.injected⟩, held.1.2⟩, held.2⟩, rfl, rfl⟩

theorem advance_projects (result : Except Interner.Error α) :
    ProjectsAt observed borrowed (advance result) (advanceModel result) :=
  advance_projects_held 7 source items outerSlice result

def cursorRun (result : Except Interner.Error Nat) : GraphAction Nat Nat :=
  advance (.ok 3) >>= fun value => advance (result.map (value + ·))

theorem cursor_bind_projects (result : Except Interner.Error Nat) :
    ProjectsAt observed borrowed (cursorRun result)
      (advanceModel (.ok 3) >>= fun value => advanceModel (result.map (value + ·))) :=
  projects_at_bind observed borrowed _ _ _ _ (advance_projects (.ok 3))
    (fun value => advance_projects (result.map (value + ·)))

theorem cursor_success : (cursorRun (.ok 4) world).1 = .ok 7 ∧
    (observed (cursorRun (.ok 4) world).2).allocationCursor = world.memory.effects + 2 ∧
    (cursorRun (.ok 4) world).2.graph = world.graph ∧ borrowed (cursorRun (.ok 4) world).2 :=
  ⟨rfl, rfl, rfl, (cursor_bind_projects (.ok 4) world outer_held rfl).1⟩

/-- Bind must stop at ordinary OOM without rewinding the already reached cursor. -/
theorem cursor_oom : ((cursorRun (.error .outOfMemory) >>= fun _ => advance (.ok 99)) world).1 =
      .error (.language .outOfMemory) ∧
    (observed ((cursorRun (.error .outOfMemory) >>= fun _ => advance (.ok 99)) world).2).allocationCursor =
      world.memory.effects + 2 ∧ borrowed (cursorRun (.error .outOfMemory) world).2 :=
  ⟨rfl, rfl, (cursor_bind_projects (.error .outOfMemory) world outer_held rfl).1⟩

/-- Nonordinary exhaustion keeps the actual reached effects; simulation does
not turn it into an ordinary language error or imply a valid final frame. -/
theorem cursor_exhaustion : (cursorRun (.error .unsupported) world).1 = .error (.language .unsupported) ∧
    ordinary (cursorRun (.error .unsupported) world).1 = false ∧
    (observed (cursorRun (.error .unsupported) world).2).allocationCursor = world.memory.effects + 2 :=
  ⟨rfl, rfl, rfl⟩

theorem cursor_rewind_rejected : ¬ProjectsAt observed borrowed (advance (.ok (7 : Nat))) (pure 7) := by
  intro related
  have impossible := congrArg Interner.Heap.allocationCursor (related world outer_held rfl).2.2
  simp only [observed, cursorGraph, advance, pure, Effect.pure] at impossible
  omega

theorem cursor_wrong_result_rejected : ¬ProjectsAt observed borrowed (advance (.ok (8 : Nat))) (advanceModel (.ok 7)) := by
  intro related
  have impossible : (8 : Nat) = 7 := Except.ok.inj (related world outer_held rfl).2.1
  contradiction

theorem cursor_changed_read_rejected : ¬ProjectsAt observed borrowed changedGraph (pure 7) := by
  intro related
  have impossible := congrArg (fun heap => heap.read 0) (related world outer_held rfl).2.2
  contradiction

/-- Even ordinary allocation refusal advances the observed resource stream.
The same exact relation cannot be asserted at the raw graph cursor. -/
theorem advancing_raw_graph_rejected :
    ¬Projects borrowed (advance (.error .outOfMemory : Except Interner.Error Nat)) (advanceModel (.error .outOfMemory)) := by
  intro related
  have impossible := congrArg Interner.Heap.allocationCursor (related world outer_held rfl).2.2
  change world.graph.allocationCursor = world.graph.allocationCursor + 1 at impossible
  omega

/-- A successful advancing observation transfers its value and all native
reads as well as graph validity/stability. The cursor itself remains observed. -/
theorem advancing_success_words (before : World Nat) (held : borrowed before)
    (valid : Interner.Invariant Compiler.Extraction.Recursive.Tests.model before.graph) :
    Semantic.Ensures Compiler.Extraction.Recursive.Tests.model before.graph
      (advance (.ok (7 : NodeId)) before).1 (advance (.ok (7 : NodeId)) before).2.graph
      (fun id heap => id = 7 ∧ heap.read = before.graph.read) := by
  apply ProjectsAt.safe_cursor (fun world => world.memory.effects) borrowed _ _ (advance_projects (.ok 7))
    Compiler.Extraction.Recursive.Tests.model before held (fun id read => id = 7 ∧ read = before.graph.read)
  intro result after ran
  have same : (.ok (7 : NodeId), { observed before with allocationCursor := before.memory.effects + 1 }) =
      (result, after) := ran
  cases same
  exact ⟨valid.with_cursor _, fun _ _ found => found, rfl, rfl⟩

/-- The production-facing observation cannot discard a native graph component,
even when its resource cursor differs from the raw graph cursor. -/
theorem cursor_graph_fields (cursor : World σ → Nat) (before : World σ) :
    (cursorGraph cursor before).read = before.graph.read ∧
    (cursorGraph cursor before).table = before.graph.table ∧
    (cursorGraph cursor before).representatives = before.graph.representatives ∧
    (cursorGraph cursor before).allocationCursor = cursor before := ⟨rfl, rfl, rfl, rfl⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Recursive.PreservationTests
