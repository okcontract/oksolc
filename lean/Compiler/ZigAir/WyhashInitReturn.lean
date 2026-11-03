/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashInit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Compiler.ZigAir.WyhashInit
open Memory AggregateAir Compiler.Extraction

def partialCells : Cells := [(48, WyhashLocal.word 0), (40, WyhashLocal.word 0)]

theorem field_step {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (typed : frame.cell.type = objectType) (args : List Register) (env : Env) (reg : Nat)
    (pointer : env reg = some (objectPointer id)) :
    (Prim.fieldPointer (.local reg) 16).eval args env (frame.install cells) =
      (.ok (lanesPointer id), frame.install cells) :=
  eval_field _ _ _ _ _ _ _ (value_local _ _ _ pointer rfl) (select_lanes frame cells typed)

theorem element_step {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (typed : frame.cell.type = objectType) (args : List Register) (env : Env) (reg : Nat) (index : Fin 3)
    (pointer : env reg = some (lanesPointer id)) :
    (Prim.arrayElementPointer (.local reg) (.constant (.value (.scalar (.int false 64 index.val))))).eval
      args env (frame.install cells) = (.ok (lanePointer id index.val), frame.install cells) := by
  exact eval_element _ _ _ _ _ _ _ index.val (value_local _ _ _ pointer rfl)
    (value_constant _ (Scalar.unsigned_nat_valid index.val 64 (by have := index.isLt; omega)))
    (select_lane frame cells typed index)

theorem lane_load_step {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (typed : frame.cell.type = objectType) (args : List Register) (env : Env) (reg : Nat) (index : Fin 3)
    (bits : BitVec 64) (pointer : env reg = some (lanePointer id index.val))
    (found : cells.lookup (16 + index.val * 8) = some (WyhashLocal.word bits)) :
    (Prim.load (.local reg)).eval args env (frame.install cells) = (.ok (number bits), frame.install cells) := by
  apply eval_load _ _ _ _ _ _ (value_local _ _ _ pointer rfl)
  change (Memory.load _ _).map Register.value = _
  rw [lane_read frame cells typed index bits found]; rfl

theorem lane_store_step {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (typed : frame.cell.type = objectType) (args : List Register) (env : Env) (reg value : Nat) (index : Fin 3)
    (bits : BitVec 64) (pointer : env reg = some (lanePointer id index.val))
    (saved : env value = some (number bits)) :
    (Prim.store (.local reg) (.local value)).eval args env (frame.install cells) =
      (.ok unit, frame.install (cells.set (16 + index.val * 8) (WyhashLocal.word bits))) :=
  eval_store _ _ _ _ _ _ _ _ (value_local _ _ _ pointer rfl)
    (ref_local _ _ _ saved (number_valid bits)) (lane_store frame cells typed index bits)

def snapshot (bits : BitVec 64) : Register := .aggregate objectType (WyhashUpdate.initialCells bits)

theorem initialized_valid (bits : BitVec 64) :
    (WyhashUpdate.initialCells bits).valid objectType = true :=
  WyhashUpdate.store_valid _ 32 bits
    (WyhashUpdate.store_valid _ 24 bits
      (WyhashUpdate.store_valid _ 16 bits
        (WyhashUpdate.store_valid _ 48 0
          (WyhashUpdate.store_valid [] 40 0 rfl (by decide)) (by decide)) (by decide)) (by decide)) (by decide)

theorem result_valid (bits : BitVec 64) : (snapshot bits).valid = true := by
  change (aggregateType objectType && (WyhashUpdate.initialCells bits).valid objectType) = true
  rw [show aggregateType objectType = true from object_aggregate, initialized_valid]
  rfl

theorem result_typed (bits : BitVec 64) : (snapshot bits).hasType objectType = true := by
  change (decide (objectType = objectType) && (snapshot bits).valid) = true
  rw [result_valid]; rfl

theorem returned_load {state : State} {id : Nat} (frame : CellFrame state id)
    (typed : frame.cell.type = objectType) (bits : BitVec 64) (args : List Register) (env : Env)
    (pointer : env 1 = some (objectPointer id)) :
    (Prim.load (.local 1)).eval args env (frame.install (WyhashUpdate.initialCells bits)) =
      (.ok (snapshot bits), frame.install (WyhashUpdate.initialCells bits)) := by
  apply eval_load _ _ _ _ _ _ (value_local _ _ _ pointer rfl)
  have accessed := frame.field_read_access (WyhashUpdate.initialCells bits) 0 frame.layout
    (by rw [object_frame_layout frame typed]; decide) (by simp) (by simp) (by simp)
  rw [object_frame_layout frame typed] at accessed
  have read := load_root _ id { frame.cell with cells := WyhashUpdate.initialCells bits }
    ⟨104, 8⟩ (typed ▸ object_layout) accessed (typed ▸ object_aggregate) (typed ▸ initialized_valid bits)
  simpa only [typed] using read

def copyLane (start : Nat) (index : Fin 3) (next : Code) : Code :=
  .bind start (.pointer true false (.array 3 (.scalar (.int false 64)))) (.fieldPointer (.local 1) 16) <|
  .bind (start + 1) (.pointer true false (.scalar (.int false 64)))
    (.arrayElementPointer (.local start) (.constant (.value (.scalar (.int false 64 index.val))))) <|
  .bind (start + 2) (.pointer true false (.array 3 (.scalar (.int false 64)))) (.fieldPointer (.local 1) 16) <|
  .bind (start + 3) (.pointer true false (.scalar (.int false 64)))
    (.arrayElementPointer (.local (start + 2)) (.constant (.value (.scalar (.int false 64 0))))) <|
  .bind (start + 4) (.scalar (.int false 64)) (.load (.local (start + 3))) <|
  .bind (start + 5) (.scalar .unit) (.store (.local (start + 1)) (.local (start + 4))) next

def copyEnv (env : Env) (start id : Nat) (index : Fin 3) (bits : BitVec 64) : Env :=
  let env := env.set start (lanesPointer id)
  let env := env.set (start + 1) (lanePointer id index.val)
  let env := env.set (start + 2) (lanesPointer id)
  let env := env.set (start + 3) (lanePointer id 0)
  let env := env.set (start + 4) (number bits)
  env.set (start + 5) unit

/-- Both captured lane-copy sequences specialize this one proof. -/
theorem copy_lane {state : State} {id : Nat} (frame : CellFrame state id)
    (typed : frame.cell.type = objectType) (cells : Cells) (bits : BitVec 64)
    (args : List Register) (env : Env) (start : Nat) (index : Fin 3) (next : Code)
    (fresh : 1 < start) (self : env 1 = some (objectPointer id))
    (found : cells.lookup 16 = some (WyhashLocal.word bits)) :
    (copyLane start index next).eval semantics args env (frame.install cells) =
      next.eval semantics args (copyEnv env start id index bits)
        (frame.install (cells.set (16 + index.val * 8) (WyhashLocal.word bits))) := by
  let e1 := env.set start (lanesPointer id)
  let e2 := e1.set (start + 1) (lanePointer id index.val)
  let e3 := e2.set (start + 2) (lanesPointer id)
  let e4 := e3.set (start + 3) (lanePointer id 0)
  let e5 := e4.set (start + 4) (number bits)
  simp only [copyLane]
  refine (bind_ok _ _ _ _ _ _ _ _ _ (field_step frame cells typed args env 1 self) (by rfl)).trans ?_
  refine (bind_ok _ _ _ _ _ _ _ _ _ (element_step frame cells typed args e1 start index (by simp [e1, Control.Env.set])) (by rfl)).trans ?_
  refine (bind_ok _ _ _ _ _ _ _ _ _ (field_step frame cells typed args e2 1
    (by simpa only [e2, e1, Control.Env.set, if_neg (by omega : 1 ≠ start + 1), if_neg (by omega : 1 ≠ start)] using self)) (by rfl)).trans ?_
  refine (bind_ok _ _ _ _ _ _ _ _ _ (element_step frame cells typed args e3 (start + 2) 0 (by simp [e3, Control.Env.set])) (by rfl)).trans ?_
  refine (bind_ok _ _ _ _ _ _ _ _ _ (lane_load_step frame cells typed args e4 (start + 3) 0 bits (by simp [e4, Control.Env.set]) found) (number_typed bits)).trans ?_
  refine (bind_ok _ _ _ _ _ _ _ _ _ (lane_store_step frame cells typed args e5 (start + 1) (start + 4) index bits
    (by simp [e5, e4, e3, e2, Control.Env.set]) (by simp [e5, Control.Env.set])) (by rfl)).trans ?_
  rfl

theorem return_code : GeneratedWyhashInit.fn_init.body.dropBindings 24 =
    (.bind 31 (.scalar .unit) (.store (.local 5) (.local 30))
      (copyLane 32 1 (copyLane 38 2 (.bind 44 objectType (.load (.local 1)) (.ret (.local 44)))))) := by rfl

theorem return_snapshot {state : State} {id : Nat} (frame : CellFrame state id)
    (typed : frame.cell.type = objectType) (bits : BitVec 64) (args : List Register) (env : Env)
    (self : env 1 = some (objectPointer id)) :
    (Control.Code.bind 44 objectType (.load (.local 1)) (.ret (.local 44))).eval semantics args env
      (frame.install (WyhashUpdate.initialCells bits)) =
      .returned (snapshot bits) (frame.install (WyhashUpdate.initialCells bits)) := by
  exact (bind_ok _ _ _ _ _ _ _ _ _ (returned_load frame typed bits args env self) (result_typed bits)).trans
    (ret_ok _ _ _ _ _ (ref_local (env.set 44 (snapshot bits)) 44 (snapshot bits) rfl (result_valid bits)))

/-- Every remaining captured field pointer, scalar copy and whole-object load.
The returned value owns a sparse snapshot; undefined a/b and buffer leaves are
not read or silently initialized. The allocation and caller heap are arbitrary. -/
theorem return_tail {state : State} {id : Nat} (frame : CellFrame state id)
    (typed : frame.cell.type = objectType) (bits : BitVec 64) (args : List Register) (env : Env)
    (self : env 1 = some (objectPointer id)) (first : env 5 = some (lanePointer id 0))
    (value : env 30 = some (number bits)) :
    (GeneratedWyhashInit.fn_init.body.dropBindings 24).eval semantics args env (frame.install partialCells) =
      .returned (snapshot bits) (frame.install (WyhashUpdate.initialCells bits)) := by
  let c0 := partialCells.set 16 (WyhashLocal.word bits)
  let c1 := c0.set 24 (WyhashLocal.word bits)
  let e1 := env.set 31 unit
  let e2 := copyEnv e1 32 id 1 bits
  let e3 := copyEnv e2 38 id 2 bits
  have at0 : c0.lookup 16 = some (WyhashLocal.word bits) := Cells.lookup_set ..
  have at1 : c1.lookup 16 = some (WyhashLocal.word bits) := by
    rw [Cells.lookup_set_other _ _ _ _ (by decide : 16 ≠ 24)]
    exact at0
  rw [return_code]
  refine (bind_ok _ _ _ _ _ _ _ _ _ (lane_store_step frame partialCells typed args env 5 30 0 bits first value) (by rfl)).trans ?_
  refine (copy_lane frame typed c0 bits args e1 32 1 _ (by decide)
    (by simpa [e1, Control.Env.set] using self) at0).trans ?_
  refine (copy_lane frame typed c1 bits args e2 38 2 _ (by decide)
    (by simpa [e2, e1, copyEnv, Control.Env.set] using self) at1).trans ?_
  exact return_snapshot frame typed bits args e3
    (by simpa [e3, e2, e1, copyEnv, Control.Env.set] using self)

end Compiler.ZigAir.WyhashInit
