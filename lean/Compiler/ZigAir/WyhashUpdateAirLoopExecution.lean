/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirLoopControl

set_option maxRecDepth 8192

namespace Compiler.ZigAir.WyhashUpdateAir.Loop
open Memory AggregateAir Compiler.Extraction Control.Machine

/-- Admission before allocating the mutable loop index. The byte observations
and root parameters belong to this caller; only the hasher is borrowed mutably.
There is no premise about a round, allocation outcome or loop execution. -/
structure Context (base : State) (id : Nat) where
  frame : CellFrame base id
  valid : base.valid = true
  typed : frame.cell.type = objectType
  source : Cells
  view : ByteSlice.View
  address : Address
  bytes : Nat → BitVec 8
  geometry : ByteSlice.Geometry view
  represented : ByteSlice.Represents source view bytes
  reads : ByteRange.Reads base address view.length bytes
  apart : address.allocation ≠ id
  selfSlot : Nat
  inputSlot : Nat
  indexSlot : Nat
  selfApart : selfSlot ≠ id
  inputApart : inputSlot ≠ id
  selfRead : Memory.load base (slot false (.pointer true false objectType) selfSlot) = .ok (selfPointer id)
  inputRead : Memory.load base (slot false inputType inputSlot) = .ok (.slice inputType address view.length)
  countRead : Memory.load base (.pointer (.pointer false false usize) ⟨inputSlot, 8⟩) =
    .ok (.scalar (.int false 64 view.length))
  indexFresh : base.nextId ≤ indexSlot
  budget : view.length + 48 < addressLimit
  total : Nat

/-- Native memory framing around the existing cell invariant. The index is an
owned local; the source and saved descriptors stay in the caller frame. -/
structure At {base : State} {id : Nat} (ctx : Context base id) (cells : Cells) (index : Nat) (state : State) : Prop where
  core : WyhashUpdate.Core cells ctx.total
  stack : StackFrame (ctx.frame.install cells) state
  counter : ∃ counter : CellFrame state ctx.indexSlot,
    counter.cell.type = usize ∧ counter.cell.cells.valid usize = true
  indexRead : Memory.load state (slot true usize ctx.indexSlot) = .ok (.scalar (.int false 64 index))
  inside : index < ctx.view.length

def Locals {base : State} {id : Nat} (ctx : Context base id) (env : Env) : Prop :=
  env 4 = some (.value (slot false (.pointer true false objectType) ctx.selfSlot)) ∧
  env 7 = some (.value (slot false inputType ctx.inputSlot)) ∧
  env 50 = some (.value (slot true usize ctx.indexSlot))

/-- OOM may occur after complete rounds and a proper prefix of the next three
lanes. This relation records those writes instead of treating update as atomic. -/
inductive Interrupted (source : Cells) (view : ByteSlice.View) : Nat → Cells → Cells → Prop where
  | lane {index cells after : _} (inside : index + 48 < view.length) (completed : Nat)
      (bounded : completed < 3)
      (ran : Round.lanePrefix (.external source view) index completed cells = .ok after) :
      Interrupted source view index cells after
  | next {index cells middle after : _} (inside : index + 48 < view.length)
      (ran : WyhashUpdate.round (.external source view) index cells = .ok middle)
      (rest : Interrupted source view (index + 48) middle after) :
      Interrupted source view index cells after

theorem At.old_load {base state : State} {id index : Nat} {ctx : Context base id} {cells : Cells}
    (live : At ctx cells index state) (address : Address) (apart : address.allocation ≠ id)
    (mutable many : Bool) (child : Ty) (value : Value)
    (read : Memory.load base (.pointer (.pointer mutable many child) address) = .ok value) :
    Memory.load state (.pointer (.pointer mutable many child) address) = .ok value :=
  live.stack.old_load mutable many child address value
    ((ctx.frame.load_outside cells address apart mutable many child).trans read)

theorem At.reads {base state : State} {id index : Nat} {ctx : Context base id} {cells : Cells}
    (live : At ctx cells index state) : ByteRange.Reads state ctx.address ctx.view.length ctx.bytes :=
  ByteRange.Reads.extend live.stack _ _ _
    (ByteRange.Reads.install ctx.frame cells _ _ _ ctx.apart ctx.reads)

theorem At.updated {base state after : State} {id index : Nat} {ctx : Context base id} {cells next : Cells}
    (live : At ctx cells index state) (core : WyhashUpdate.Core next ctx.total)
    (stack : StackFrame (((ctx.frame.replaced cells).extend live.stack).install next) after) :
    StackFrame (ctx.frame.install next) after := by
  have installed := live.stack.install_old (ctx.frame.replaced cells) next (ctx.typed ▸ core.valid)
  rw [ctx.frame.replaced_install] at installed
  exact installed.trans stack

/-- One native execution induction for all complete external blocks. It consumes
the original guard, the shared three-lane round, the counter store and back edge.
Success is the existing cell loop; every native OOM retains its executed prefix. -/
theorem execute {base state : State} {id index : Nat} (ctx : Context base id) (cells : Cells)
    (live : At ctx cells index state) (args : List Register) (env : Env)
    (outer : List (Frame Ty AggregateCall.Prim Ref)) (locals : Locals ctx env) :
    ∃ after,
      (∃ failedCells, Interrupted ctx.source ctx.view index cells failedCells ∧
        WyhashUpdate.Core failedCells ctx.total ∧ StackFrame (ctx.frame.install failedCells) after ∧
        Steps AggregateCall.semantics args (.suspended ⟨body, env, state, frames outer⟩)
          (.finished (.fault .outOfMemory after))) ∨
      ∃ finalCells stop finalEnv, WyhashUpdate.loop ctx.source ctx.view index cells = .ok (finalCells, stop) ∧
        At ctx finalCells stop after ∧
        Steps AggregateCall.semantics args (.suspended ⟨body, env, state, frames outer⟩)
          (.suspended ⟨continuation, finalEnv, after, outer⟩) ∧
        ∀ query < 326, finalEnv query = env query := by
  have bound : index + 48 < addressLimit := by have := live.inside; have := ctx.budget; omega
  have countBound : ctx.view.length < addressLimit := by have := ctx.budget; omega
  have countRead := live.old_load ⟨ctx.inputSlot, 8⟩ ctx.inputApart false false usize _ ctx.countRead
  have first : Steps AggregateCall.semantics args (.suspended ⟨body, env, state, frames outer⟩)
      (.suspended ⟨condition, env, state, innerFrames outer⟩) := .step _ (.refl _)
  have guard := guard_steps state ctx.inputSlot ctx.indexSlot index ctx.view.length bound countBound
    live.indexRead countRead args env (innerFrames outer) locals.2.2 locals.2.1
  let entered := guardEnv env ctx.inputSlot index ctx.view.length
  have enteredLocals : Locals ctx entered := by
    simpa only [Locals, entered, guard_before _ _ _ _ 4 (by decide),
      guard_before _ _ _ _ 7 (by decide), guard_before _ _ _ _ 50 (by decide)] using locals
  by_cases more : index + 48 < ctx.view.length
  · rw [if_pos more] at guard
    let current := (ctx.frame.replaced cells).extend live.stack
    have selfRead := live.old_load ⟨ctx.selfSlot, 0⟩ ctx.selfApart false false
      (.pointer true false objectType) _ ctx.selfRead
    have inputRead := live.old_load ⟨ctx.inputSlot, 0⟩ ctx.inputApart false false inputType _ ctx.inputRead
    obtain ⟨middle, ⟨completed, failedCells, bounded, failed, failedCore, failedStack, failedPath⟩ |
        ⟨nextCells, nextEnv, ran, nextCore, _, roundStack, roundPath, before⟩⟩ :=
      Round.external_steps current live.stack.valid ctx.typed ctx.total live.core ctx.source ctx.view
        ctx.address ctx.bytes ctx.geometry ctx.represented live.reads ctx.apart index (Nat.le_of_lt more)
        countBound ctx.selfSlot ctx.inputSlot ctx.indexSlot selfRead inputRead live.indexRead
        args entered (innerFrames outer) enteredLocals.1 enteredLocals.2.1 enteredLocals.2.2
    · exact ⟨middle, Or.inl ⟨failedCells, .lane more completed bounded failed, failedCore,
        live.updated failedCore failedStack,
        first.trans AggregateCall.semantics args (guard.trans AggregateCall.semantics args failedPath)⟩⟩
    · change WyhashUpdate.round (.external ctx.source ctx.view) index cells = .ok nextCells at ran
      obtain ⟨counter, counterTyped, counterValid⟩ := live.counter
      have indexApart : ctx.indexSlot ≠ id := by
        have := (valid_lookup base id ctx.frame.cell ctx.valid ctx.frame.found).1
        have := ctx.indexFresh
        omega
      let nextCounter := (current.after_other counter nextCells indexApart).extend roundStack
      have nextRead := roundStack.old_load true false usize ⟨ctx.indexSlot, 0⟩ _
        ((current.load_outside nextCells ⟨ctx.indexSlot, 0⟩ indexApart true false usize).trans live.indexRead)
      have nextLocals : Locals ctx nextEnv := by
        simpa only [Locals, before 4 (by decide), before 7 (by decide), before 50 (by decide)] using enteredLocals
      obtain ⟨counterCells, written, tailPath, counterRead⟩ := tail_steps nextCounter counterTyped index bound
        nextRead args nextEnv outer nextLocals.2.2
      have counterValid' : counterCells.valid usize = true :=
        Cells.write_preserves_valid _ _ _ _ _ counterValid written
      have nextStack := (live.updated nextCore roundStack).install ctx.indexSlot nextCounter counterCells
        ctx.indexFresh (counterTyped ▸ counterValid')
      let nextAt : At ctx nextCells (index + 48) (nextCounter.install counterCells) :=
        ⟨nextCore, nextStack, ⟨nextCounter.replaced counterCells, counterTyped, counterValid'⟩, counterRead, more⟩
      let advanced := (tailEnv nextEnv index).set 328 (.value (.scalar .unit))
      have advancedBefore : ∀ query < 326, advanced query = env query := by
        intro query earlier
        dsimp only [advanced]
        rw [Control.Env.set, if_neg (by omega : query ≠ 328), tail_before _ _ query (by omega),
          before query (by omega)]
        exact guard_before _ _ _ _ query (by omega)
      have advancedLocals : Locals ctx advanced := by
        simpa only [Locals, advancedBefore 4 (by decide), advancedBefore 7 (by decide),
          advancedBefore 50 (by decide)] using locals
      have path := first.trans AggregateCall.semantics args <| guard.trans AggregateCall.semantics args <|
        roundPath.trans AggregateCall.semantics args tailPath
      obtain ⟨after, ⟨failedCells, failed, failedCore, failedStack, failedPath⟩ |
          ⟨finalCells, stop, finalEnv, finished, finalAt, finalPath, finalBefore⟩⟩ :=
        execute ctx nextCells nextAt args advanced outer advancedLocals
      · exact ⟨after, Or.inl ⟨failedCells, .next more ran failed, failedCore, failedStack,
          path.trans AggregateCall.semantics args failedPath⟩⟩
      · refine ⟨after, Or.inr ⟨finalCells, stop, finalEnv, ?_, finalAt,
          path.trans AggregateCall.semantics args finalPath, ?_⟩⟩
        · rw [WyhashUpdate.loop, if_neg (by omega : ¬addressLimit ≤ index + 48), if_pos more]
          simpa only [ran, bind, Except.bind] using finished
        · intro query earlier
          exact (finalBefore query earlier).trans (advancedBefore query earlier)
  · rw [if_neg more] at guard
    refine ⟨state, Or.inr ⟨cells, index, entered.set 326 (.value (.scalar .unit)), ?_, live,
      first.trans AggregateCall.semantics args (guard.trans AggregateCall.semantics args ?_), ?_⟩⟩
    · rw [WyhashUpdate.loop, if_neg (by omega : ¬addressLimit ≤ index + 48), if_neg more]
    · exact .step _ (.refl _)
    · intro query earlier
      rw [Control.Env.set, if_neg (by omega : query ≠ 326)]
      exact guard_before _ _ _ _ query (by omega)
termination_by ctx.view.length - index
decreasing_by have := live.inside; omega

/-- Consume the induction at the complete captured loop block. The existing
model theorem supplies its exit bounds and preserved fields; the native proof
supplies execution, ownership and all allocation outcomes. -/
theorem entry_steps {base state : State} {id index : Nat} (ctx : Context base id) (cells : Cells)
    (live : At ctx cells index state) (args : List Register) (env : Env)
    (outer : List (Frame Ty AggregateCall.Prim Ref)) (locals : Locals ctx env) :
    ∃ after,
      (∃ failedCells, Interrupted ctx.source ctx.view index cells failedCells ∧
        WyhashUpdate.Core failedCells ctx.total ∧ StackFrame (ctx.frame.install failedCells) after ∧
        Steps AggregateCall.semantics args (.suspended ⟨entry, env, state, outer⟩)
          (.finished (.fault .outOfMemory after))) ∨
      ∃ finalCells stop finalEnv, WyhashUpdate.loop ctx.source ctx.view index cells = .ok (finalCells, stop) ∧
        At ctx finalCells stop after ∧
        (∀ query, query < 16 ∨ 40 ≤ query → finalCells.lookup query = cells.lookup query) ∧
        index ≤ stop ∧ stop < ctx.view.length ∧ ctx.view.length ≤ stop + 48 ∧ (stop = index ∨ 48 ≤ stop) ∧
        Steps AggregateCall.semantics args (.suspended ⟨entry, env, state, outer⟩)
          (.suspended ⟨continuation, finalEnv, after, outer⟩) ∧
        ∀ query < 326, finalEnv query = env query := by
  have head : Steps AggregateCall.semantics args (.suspended ⟨entry, env, state, outer⟩)
      (.suspended ⟨body, env, state, frames outer⟩) := .step _ (.step _ (.refl _))
  obtain ⟨after, failed | ⟨finalCells, stop, finalEnv, ran, finalAt, path, before⟩⟩ :=
    execute ctx cells live args env outer locals
  · obtain ⟨failedCells, interrupted, core, stack, path⟩ := failed
    exact ⟨after, Or.inl ⟨failedCells, interrupted, core, stack, head.trans AggregateCall.semantics args path⟩⟩
  · obtain ⟨modelCells, modelStop, model, _, retained, lower, upper, ended, started⟩ :=
      WyhashUpdate.loop_verified ctx.source cells ctx.view ctx.bytes ctx.geometry ctx.represented
        ctx.total index live.core live.inside ctx.budget
    have equal := Except.ok.inj (model.symm.trans ran)
    obtain ⟨sameCells, sameStop⟩ := Prod.mk.inj equal
    subst modelCells modelStop
    exact ⟨after, Or.inr ⟨finalCells, stop, finalEnv, ran, finalAt, retained, lower, upper, ended, started,
      head.trans AggregateCall.semantics args path, before⟩⟩

end Compiler.ZigAir.WyhashUpdateAir.Loop
