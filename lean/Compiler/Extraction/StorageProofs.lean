/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.StorageProgram

namespace Compiler.Extraction.Storage
open Compiler.Algebraic
open Contract.Yul

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def allocationPolicy (arguments item clone append publish : Bool) : Allocation → Bool
  | .arguments => arguments
  | .item => item
  | .clone => clone
  | .append => append
  | .publish => publish

theorem allocationPolicy_complete (succeeds : Allocation → Bool) :
    allocationPolicy (succeeds .arguments) (succeeds .item) (succeeds .clone)
      (succeeds .append) (succeeds .publish) = succeeds := by
  funext site
  cases site <;> rfl

/-- All independent outcomes of every fallible primitive, on both ownership
paths and at the capacity boundary. This is a kernel proof by finite case
analysis, not native evaluation or testing a chosen allocation budget. -/
theorem insert_safe (deterministic room arguments item clone append publish : Bool) :
    SafeResult deterministic (insertProgram.run
      ⟨deterministic, room, allocationPolicy arguments item clone append publish⟩ {}) := by
  cases deterministic <;> cases room <;> cases arguments <;> cases item <;>
    cases clone <;> cases append <;> cases publish <;> decide

theorem insert_safe_any (input : Input) : SafeResult input.deterministic (insertProgram.run input {}) := by
  rcases input with ⟨deterministic, room, succeeds⟩
  simpa only [allocationPolicy_complete] using insert_safe deterministic room (succeeds .arguments)
    (succeeds .item) (succeeds .clone) (succeeds .append) (succeeds .publish)

def expectedOutcome (deterministic room arguments item clone append publish : Bool) : Outcome :=
  if !room then .capacityFailure
  else if deterministic && !arguments then .allocationFailure
  else if !item || !clone || !append || (deterministic && !publish) then .allocationFailure
  else .success

/-- Successful allocation and available capacity really produce a node; the
ownership theorem cannot be satisfied by an implementation that always fails. -/
theorem insert_outcome (deterministic room arguments item clone append publish : Bool) :
    (insertProgram.run
      ⟨deterministic, room, allocationPolicy arguments item clone append publish⟩ {}).1 =
      some (expectedOutcome deterministic room arguments item clone append publish) := by
  cases deterministic <;> cases room <;> cases arguments <;> cases item <;>
    cases clone <;> cases append <;> cases publish <;> decide

theorem insert_outcome_any (input : Input) :
    (insertProgram.run input {}).1 = some (expectedOutcome input.deterministic input.room
      (input.succeeds .arguments) (input.succeeds .item) (input.succeeds .clone)
      (input.succeeds .append) (input.succeeds .publish)) := by
  rcases input with ⟨deterministic, room, succeeds⟩
  simpa only [allocationPolicy_complete] using insert_outcome deterministic room (succeeds .arguments)
    (succeeds .item) (succeeds .clone) (succeeds .append) (succeeds .publish)

theorem insert_progress (deterministic : Bool) :
    (insertProgram.run ⟨deterministic, true, allocationPolicy true true true true true⟩ {}).1 =
      some .success := by
  rw [insert_outcome]
  cases deterministic <;> rfl

/-- Projection of the container primitive contracts. Existing cells are immutable;
an append adds exactly the cloned item/argument value, rollback removes that last
cell, and cache publication changes no representative. Cell may include allocation
identity, so this contract also retains the separately allocated item address. -/
def nodesAfter (before : List Cell) (cell : Cell) (state : State) : List Cell :=
  if state.appended then before ++ [cell] else before

def idFor (before : List Cell) : NodeId := BitVec.ofNat 32 before.length

theorem idFor_toNat (before : List Cell) (room : before.length < 2 ^ 32 - 1) :
    (idFor before).toNat = before.length := by
  simp only [idFor, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  omega

theorem published_preserves (before : List Cell) (cell : Cell) (state : State)
    (index : Nat) (valid : index < before.length) :
    (nodesAfter before cell state)[index]? = before[index]? := by
  simp only [nodesAfter]
  split
  · simp [List.getElem?_append, valid]
  · rfl

theorem published_returns (before : List Cell) (cell : Cell) (state : State)
    (published : Published deterministic state) (room : before.length < 2 ^ 32 - 1) :
    (nodesAfter before cell state)[(idFor before).toNat]? = some cell := by
  simp [nodesAfter, published.2.1, idFor_toNat before room]

theorem failure_restores (before : List Cell) (cell : Cell) (state : State)
    (released : Released state) : nodesAfter before cell state = before := by
  simp [nodesAfter, released.2.1]

theorem representative_correct (cells : List Cell) (id : NodeId) :
    representativeProgram.run cells id =
      match cells[id.toNat]? with
      | none => .error .invalidId
      | some cell => .ok cell := by
  unfold representativeProgram Lookup.run Bound.reject Index.eval
  by_cases valid : id.toNat < cells.length
  · simp [valid, Nat.not_le.mpr valid]
  · simp [valid, Nat.le_of_not_gt valid]

/-- No out-of-bounds access, even for invalid IDs. The explicit error remains
distinguishable from a Zig safety fault in the underlying read interpreter. -/
theorem representative_no_fault (cells : List Cell) (id : NodeId) :
    representativeProgram.run cells id ≠ .error .safetyFault := by
  rw [representative_correct]
  cases cells[id.toNat]? <;> simp

theorem constant_correct (cells : List Cell) (id : NodeId) :
    constantProgram.run cells id = .ok (cells[id.toNat]?.bind
      (fun cell => if cell.isPush then some cell.dataValue else none)) := by
  unfold constantProgram ConstantRead.run
  rw [representative_correct]
  cases cells[id.toNat]? with
  | none => rfl
  | some cell => cases h : cell.isPush <;> simp [h]

theorem constant_fact_sound (cells : List Cell) (id : NodeId) (value : Word)
    (found : constantProgram.run cells id = .ok (some value)) :
    readValue cells id = some value := by
  rw [constant_correct] at found
  unfold readValue
  cases entry : cells[id.toNat]? with
  | none => simp [entry] at found
  | some cell =>
    cases push : cell.isPush <;> simp [entry, push] at found
    simp [Cell.value, push, found]

theorem constant_stable (before : List Cell) (cell : Cell) (state : State) (id : NodeId)
    (valid : id.toNat < before.length) :
    constantProgram.run (nodesAfter before cell state) id = constantProgram.run before id := by
  rw [constant_correct, constant_correct, published_preserves before cell state id.toNat valid]

def discoveredFacts (left right : NodeId) (a b : Option Word) : Facts :=
  { left := a, right := b, equal := left == right }

/-- The reliable-facts premise of the rewrite theorem is discharged by actual
constant reads and ID equality, for any values of nonconstant representatives. -/
theorem discoveredFacts_reliable (cells : List Cell) (left right : NodeId)
    (a b : Word) (leftConstant rightConstant : Option Word)
    (leftRead : readValue cells left = some a) (rightRead : readValue cells right = some b)
    (leftFound : constantProgram.run cells left = .ok leftConstant)
    (rightFound : constantProgram.run cells right = .ok rightConstant) :
    (discoveredFacts left right leftConstant rightConstant).Reliable a b := by
  constructor
  · intro value present
    have observed := constant_fact_sound cells left value (leftFound.trans (congrArg Except.ok present))
    exact Option.some.inj (leftRead.symm.trans observed)
  · intro value present
    have observed := constant_fact_sound cells right value (rightFound.trans (congrArg Except.ok present))
    exact Option.some.inj (rightRead.symm.trans observed)
  · intro same
    have ids : left = right := by simpa [discoveredFacts] using same
    subst right
    exact Option.some.inj (leftRead.symm.trans rightRead)

end Compiler.Extraction.Storage
