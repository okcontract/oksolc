/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.GeneratedWyhashInit
import Compiler.ZigAir.ControlProjection
import Compiler.ZigAir.MachineRefinement
import Compiler.ZigAir.AggregateAirProofs
import Compiler.Extraction.WyhashUpdate

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Compiler.ZigAir.WyhashInit
open Memory AggregateAir Compiler.Extraction

abbrev objectType := GeneratedWyhashInit.resultType

def result (seed : BitVec 64) : Register :=
  .aggregate objectType (WyhashUpdate.initialCells (WyhashUpdate.seedState seed))

def emptyEnv : Env := fun _ => none

@[simp] theorem object_layout : GeneratedWyhashInit.resultType.layout = some ⟨104, 8⟩ := by decide +kernel
@[simp] theorem object_aggregate : aggregateType GeneratedWyhashInit.resultType = true := by decide +kernel
@[simp] theorem partial_valid :
    Cells.valid [(48, .scalar (.int false 64 0)), (40, .scalar (.int false 64 0))]
      GeneratedWyhashInit.resultType = true := by decide +kernel
@[simp] theorem lanes_declared :
    fieldType GeneratedWyhashInit.resultType 16 = some (.array 3 (.scalar (.int false 64))) := by decide +kernel
@[simp] theorem lanes_view :
    acceptsView GeneratedWyhashInit.resultType 16 (.array 3 (.scalar (.int false 64))) = true := by decide +kernel

def segment (start count : Nat) (next : Code) : Code :=
  (GeneratedWyhashInit.fn_init.body.dropBindings start).prefixBindings count next

def slot (id : Nat) : Register := .value (.pointer (.pointer true false usize) ⟨id, 0⟩)
def unit : Register := .value (.scalar .unit)
/-- Scalar root operations retain all native access checks. -/
theorem slot_load (args : List Register) (env : Env) (state : State) (reg id : Nat)
    (bits : BitVec 64) (saved : env reg = some (slot id))
    (read : Memory.load state (.pointer (.pointer true false usize) ⟨id, 0⟩) = .ok (WyhashLocal.word bits)) :
    (Prim.load (.local reg)).eval args env state = (.ok (number bits), state) := by
  apply eval_load _ _ _ _ (.pointer (.pointer true false usize) ⟨id, 0⟩) (number bits)
  · simp only [Ref.value, ref_local _ _ _ saved rfl, slot, bind, Except.bind]
  · change (Memory.load state (.pointer (.pointer true false usize) ⟨id, 0⟩)).map Register.value = _
    rw [read]; rfl

theorem slot_store (args : List Register) (env : Env) (state after : State) (reg value id : Nat)
    (bits : BitVec 64) (pointer : env reg = some (slot id)) (saved : env value = some (number bits))
    (written : Memory.store state (.pointer (.pointer true false usize) ⟨id, 0⟩) (WyhashLocal.word bits) = .ok after) :
    (Prim.store (.local reg) (.local value)).eval args env state = (.ok unit, after) := by
  apply eval_store _ _ _ _ _ _ (.pointer (.pointer true false usize) ⟨id, 0⟩) (number bits)
  · simp only [Ref.value, ref_local _ _ _ pointer rfl, slot, bind, Except.bind]
  · exact ref_local _ _ _ saved (number_valid bits)
  · exact written

theorem word_read (bits : BitVec 64) :
    Cells.read [(0, WyhashLocal.word bits)] usize 0 usize = .ok (WyhashLocal.word bits) := by
  simp [Cells.read, Cells.readLeaf, Cells.lookup, usize, leafType, Value.hasType,
    WyhashLocal.word_type, WyhashLocal.word_valid]

theorem word_frame_read {state : State} {id : Nat} (frame : CellFrame state id)
    (bits : BitVec 64) (typed : frame.cell.type = usize)
    (cells : frame.cell.cells = [(0, WyhashLocal.word bits)]) :
    Memory.load state (.pointer (.pointer true false usize) ⟨id, 0⟩) = .ok (WyhashLocal.word bits) := by
  have read := frame.load_current true false
  rw [typed, cells, word_read] at read
  exact read

theorem word_frame_store {state : State} {id : Nat} (frame : CellFrame state id)
    (bits : BitVec 64) (typed : frame.cell.type = usize) :
    Memory.store state (.pointer (.pointer true false usize) ⟨id, 0⟩) (WyhashLocal.word bits) =
      .ok (frame.install (frame.cell.cells.set 0 (WyhashLocal.word bits))) := by
  have written := frame.store_current (WyhashLocal.word bits) (typed ▸ WyhashLocal.word_typed bits)
  rw [typed] at written
  have cells := Cells.write_single frame.cell.cells usize 0 (WyhashLocal.word bits)
    (WyhashLocal.word_valid bits) (acceptsView_self usize)
    (by simp only [leafFits, WyhashLocal.word_type, WyhashLocal.word_valid, Bool.and_true]; rfl) rfl
  rw [cells] at written
  exact written

def mixedEnvAt (base : Nat) (env : Env) (a b : BitVec 64) : Env :=
  let p := WyhashLocal.product a b
  let env := env.set (base + 7) (number a)
  let env := env.set (base + 8) (number (a.zeroExtend 128))
  let env := env.set (base + 9) (number b)
  let env := env.set (base + 10) (number (b.zeroExtend 128))
  let env := env.set (base + 11) (number p)
  let env := env.set (base + 12) (number (WyhashLocal.lo p))
  let env := env.set (base + 13) unit
  let env := env.set (base + 14) (number (p >>> 64))
  let env := env.set (base + 15) (number (WyhashLocal.hi p))
  let env := env.set (base + 16) unit
  let env := env.set (base + 18) (number (WyhashLocal.lo p))
  let env := env.set (base + 19) (number (WyhashLocal.hi p))
  env.set (base + 20) (number (WyhashLocal.mix a b))

/-- The captured multiplication/xor sequence is shared by initialization and
every update lane. Only its SSA base and primitive embedding vary. -/
def mixCode {P : Type} {loops : Bool} (embed : AggregateAir.Prim → P) (base : Nat)
    (next : Control.Code Ty P Ref loops) : Control.Code Ty P Ref loops :=
  .bind (base + 7) usize (embed (.load (.local base))) $
  .bind (base + 8) (.scalar (.int false 128))
    (embed (.memory (.scalar (.cast .unchecked (.int false 128) (.local (base + 7)))))) $
  .bind (base + 9) usize (embed (.load (.local (base + 3)))) $
  .bind (base + 10) (.scalar (.int false 128))
    (embed (.memory (.scalar (.cast .unchecked (.int false 128) (.local (base + 9)))))) $
  .bind (base + 11) (.scalar (.int false 128))
    (embed (.memory (.scalar (.arithmetic .mul .wrapping (.local (base + 8)) (.local (base + 10)))))) $
  .bind (base + 12) usize (embed (.memory (.scalar (.cast .trunc (.int false 64) (.local (base + 11)))))) $
  .bind (base + 13) (.scalar .unit) (embed (.store (.local base) (.local (base + 12)))) $
  .bind (base + 14) (.scalar (.int false 128))
    (embed (.memory (.scalar (.shiftRight (.local (base + 11)) (.constant (.int false 7 64)))))) $
  .bind (base + 15) usize (embed (.memory (.scalar (.cast .trunc (.int false 64) (.local (base + 14)))))) $
  .bind (base + 16) (.scalar .unit) (embed (.store (.local (base + 3)) (.local (base + 15)))) $
  .bind (base + 18) usize (embed (.load (.local base))) $
  .bind (base + 19) usize (embed (.load (.local (base + 3)))) $
  .bind (base + 20) usize
    (embed (.memory (.scalar (.bitXor (.local (base + 18)) (.local (base + 19)))))) next

def mixedEnv (env : Env) (a b : BitVec 64) : Env := mixedEnvAt 8 env a b

/-- One preservation proof for the complete native mix sequence, usable with
both the finite initializer and the loop-capable update machine. Primitive
embedding changes no operation or typing check. -/
theorem mix_steps {P : Type} (sem : Control.Semantics Ty P Ref Register Fault State)
    (embed : AggregateAir.Prim → P) (typing : sem.hasType = Register.hasType)
    (primitives : ∀ op args env state, sem.evalPrim (embed op) args env state = op.eval args env state)
    (base : Nat) (args : List Register) (env : Env)
    (next : Control.Code Ty P Ref true) (frames : List (Control.Machine.Frame Ty P Ref))
    (state middle after : State) (left right : Nat) (a b : BitVec 64) (apart : left ≠ right)
    (leftReg : env base = some (slot left)) (rightReg : env (base + 3) = some (slot right))
    (readA : Memory.load state (.pointer (.pointer true false usize) ⟨left, 0⟩) = .ok (WyhashLocal.word a))
    (readB : Memory.load state (.pointer (.pointer true false usize) ⟨right, 0⟩) = .ok (WyhashLocal.word b))
    (storeA : Memory.store state (.pointer (.pointer true false usize) ⟨left, 0⟩)
      (WyhashLocal.word (WyhashLocal.lo (WyhashLocal.product a b))) = .ok middle)
    (storeB : Memory.store middle (.pointer (.pointer true false usize) ⟨right, 0⟩)
      (WyhashLocal.word (WyhashLocal.hi (WyhashLocal.product a b))) = .ok after) :
    Control.Machine.Steps sem args
      (.suspended ⟨mixCode embed base next, env, state, frames⟩)
      (.suspended ⟨next, mixedEnvAt base env a b, after, frames⟩) := by
  have step {reg : Nat} {type : Ty} {op : AggregateAir.Prim} {next : Control.Code Ty P Ref true}
      {env : Env} {before after : State} {value : Register}
      {last : Control.Machine.Execution Ty P Ref Register Fault State}
      (ran : op.eval args env before = (.ok value, after)) (typed : value.hasType type = true)
      (tail : Control.Machine.Steps sem args (.suspended ⟨next, env.set reg value, after, frames⟩) last) :
      Control.Machine.Steps sem args (.suspended ⟨.bind reg type (embed op) next, env, before, frames⟩) last :=
    Control.Machine.Steps.bind_ok sem args ((primitives op args env before).trans ran) (typing ▸ typed) tail
  have backA := Memory.load_after_store _ _ _ _ storeA
  have backB := Memory.load_after_store _ _ _ _ storeB
  have framed := Memory.load_other_after_store middle true false usize ⟨right, 0⟩ _ after
    true false usize ⟨left, 0⟩ storeB apart
  have finalA := framed.trans backA
  unfold mixCode
  apply step (slot_load args env state base left a leftReg readA) (number_typed a)
  apply step (eval_scalar _ args _ state _
    (scalar_extend _ _ _ a (by decide : 64 ≤ 128) (scalar_local _ (base + 7) a
      (by simp only [Control.Env.set]; repeat first | rfl | (split <;> try omega))))) (number_typed _)
  apply step (slot_load args _ state (base + 3) right b
    (by simpa [Control.Env.set] using rightReg) readB) (number_typed b)
  apply step (eval_scalar _ args _ state _
    (scalar_extend _ _ _ b (by decide : 64 ≤ 128) (scalar_local _ (base + 9) b
      (by simp only [Control.Env.set]; repeat first | rfl | (split <;> try omega))))) (number_typed _)
  apply step (eval_scalar _ args _ state _
    (scalar_mul _ _ _ _ (a.zeroExtend 128) (b.zeroExtend 128)
      (scalar_local _ (base + 8) _ (by simp only [Control.Env.set]; repeat first | rfl | (split <;> try omega)))
      (scalar_local _ (base + 10) _ (by simp only [Control.Env.set]; repeat first | rfl | (split <;> try omega))))) (number_typed _)
  apply step (eval_scalar _ args _ state _
    (scalar_trunc _ _ _ (WyhashLocal.product a b) (by decide : 64 ≤ 128)
      (scalar_local _ (base + 11) _ (by simp only [Control.Env.set]; repeat first | rfl | (split <;> try omega))))) (number_typed _)
  apply step (slot_store args _ state middle base (base + 12) left _
    (by simpa [Control.Env.set] using leftReg) (by simp only [Control.Env.set]; repeat first | rfl | (split <;> try omega)) storeA) (by rfl)
  apply step (eval_scalar _ args _ middle _
    (scalar_shift _ _ _ _ (WyhashLocal.product a b) 64 (by decide)
      (scalar_local _ (base + 11) _ (by simp only [Control.Env.set]; repeat first | rfl | (split <;> try omega))) (by rfl))) (number_typed _)
  apply step (eval_scalar _ args _ middle _
    (scalar_trunc _ _ _ (WyhashLocal.product a b >>> 64) (by decide : 64 ≤ 128)
      (scalar_local _ (base + 14) _ (by simp only [Control.Env.set]; repeat first | rfl | (split <;> try omega))))) (number_typed _)
  apply step (slot_store args _ middle after (base + 3) (base + 15) right _
    (by simpa [Control.Env.set] using rightReg) (by simp only [Control.Env.set]; repeat first | rfl | (split <;> try omega)) storeB) (by rfl)
  apply step (slot_load args _ after base left _
    (by simpa [Control.Env.set] using leftReg) finalA) (number_typed _)
  apply step (slot_load args _ after (base + 3) right _
    (by simpa [Control.Env.set] using rightReg) backB) (number_typed _)
  apply step (eval_scalar _ args _ after _
    (scalar_xor _ _ _ _ (WyhashLocal.lo (WyhashLocal.product a b)) (WyhashLocal.hi (WyhashLocal.product a b))
      (scalar_local _ (base + 18) _ (by
        simp only [Control.Env.set, Nat.add_left_cancel_iff, Nat.reduceEqDiff, ↓reduceIte]))
      (scalar_local _ (base + 19) _ (by simp only [Control.Env.set]; repeat first | rfl | (split <;> try omega))))) (number_typed _)
  exact .refl _

/-- All thirteen captured mix instructions, for arbitrary admitted slots and
operands. Readback and noninterference follow from the two native stores. -/
theorem mix_prefix (args : List Register) (env : Env) (next : Code) (state middle after : State)
    (left right : Nat) (a b : BitVec 64) (apart : left ≠ right)
    (leftReg : env 8 = some (slot left)) (rightReg : env 11 = some (slot right))
    (readA : Memory.load state (.pointer (.pointer true false usize) ⟨left, 0⟩) = .ok (WyhashLocal.word a))
    (readB : Memory.load state (.pointer (.pointer true false usize) ⟨right, 0⟩) = .ok (WyhashLocal.word b))
    (storeA : Memory.store state (.pointer (.pointer true false usize) ⟨left, 0⟩)
      (WyhashLocal.word (WyhashLocal.lo (WyhashLocal.product a b))) = .ok middle)
    (storeB : Memory.store middle (.pointer (.pointer true false usize) ⟨right, 0⟩)
      (WyhashLocal.word (WyhashLocal.hi (WyhashLocal.product a b))) = .ok after) :
    (segment 10 13 next).eval semantics args env state =
      next.eval semantics args (mixedEnv env a b) after := by
  have head := mix_steps semantics id rfl (by intros; rfl) 8 args env next.enableLoops []
    state middle after left right a b apart leftReg rightReg readA readB storeA storeB
  have tail := Control.Machine.finite_steps semantics args next (mixedEnv env a b) after []
  have terminal : Control.Machine.continueOutcome semantics
      (next.eval semantics args (mixedEnv env a b) after) [] =
      .finished (next.eval semantics args (mixedEnv env a b) after) := by
    cases next.eval semantics args (mixedEnv env a b) after <;> rfl
  rw [terminal] at tail
  have path := head.trans semantics args tail
  have generated : (segment 10 13 next).enableLoops = mixCode id 8 next.enableLoops := rfl
  rw [← generated] at path
  obtain ⟨fuel, done⟩ := (Control.Machine.steps_iff_fuel semantics args _ _).mp path
  exact (Control.Machine.finite_result semantics args (segment 10 13 next) env state fuel _ done).symm

@[simp] theorem object_native : objectType = WyhashLocal.objectType := rfl

def objectPointer (id : Nat) : Register := .value (.pointer (.pointer true false objectType) ⟨id, 0⟩)
def lanesPointer (id : Nat) : Register := .value (.pointer (.pointer true false (.array 3 usize)) ⟨id, 16⟩)
def lanePointer (id index : Nat) : Register := .value (.pointer (.pointer true false usize) ⟨id, 16 + index * 8⟩)

theorem object_frame_layout {state : State} {id : Nat} (frame : CellFrame state id)
    (typed : frame.cell.type = objectType) : frame.layout = ⟨104, 8⟩ := by
  have shaped := frame.shaped
  rw [typed] at shaped
  exact Option.some.inj (shaped.symm.trans object_layout)

theorem select_lanes {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (typed : frame.cell.type = objectType) :
    Memory.fieldPointer (frame.install cells) (.pointer (.pointer true false objectType) ⟨id, 0⟩) 16 =
      .ok (.pointer (.pointer true false (.array 3 usize)) ⟨id, 16⟩) := by
  have accessed := frame.field_read_access cells 0 frame.layout
    (by rw [object_frame_layout frame typed]; decide) (by simp) (by simp) (by simp)
  rw [object_frame_layout frame typed] at accessed
  exact fieldPointer_of_access _ _ _ objectType (.array 3 usize) ⟨104, 8⟩ 16 true false object_layout
    accessed (by simpa only [typed] using acceptsView_self objectType) lanes_declared

theorem select_lane {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (typed : frame.cell.type = objectType) (index : Fin 3) :
    AggregateAir.arrayElementPointer (frame.install cells)
      (.pointer (.pointer true false (.array 3 usize)) ⟨id, 16⟩) index.val =
      .ok (.pointer (.pointer true false usize) ⟨id, 16 + index.val * 8⟩) := by
  have shaped := object_frame_layout frame typed
  have full := frame.field_read_access cells 16 ⟨24, 8⟩ (by decide)
    (by rw [shaped]; decide) (by decide) (by rw [shaped]; decide)
  have first := access_narrow _ _ _ 0 false _ full (by decide)
  have last := frame.field_read_access cells (16 + index.val * 8) ⟨8, 8⟩ (by decide)
    (by rw [shaped]; have := index.isLt; dsimp; omega)
    (by simp [Nat.add_mod]) (by rw [shaped]; decide)
  exact array_element _ true usize 3 index.val ⟨id, 16⟩ ⟨24, 8⟩ ⟨8, 8⟩ _ index.isLt
    rfl rfl (by decide) full (typed ▸ lanes_view) first last

/-- The counter and buffered-length accesses use the same checked root frame
as the lanes. Undefined a/b fields are outside these selected offsets. -/
theorem object_word_read {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (typed : frame.cell.type = WyhashLocal.objectType) (offset : Nat) (member : offset ∈ [16, 24, 32, 40, 48])
    (bits : BitVec 64) (found : cells.lookup offset = some (WyhashLocal.word bits)) :
    Memory.load (frame.install cells) (.pointer (.pointer true false usize) ⟨id, offset⟩) =
      .ok (WyhashLocal.word bits) := by
  have region : offset + 8 ≤ 104 ∧ offset % 8 = 0 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
  rw [frame.load_eq cells offset usize ⟨8, 8⟩ rfl (by decide)
    (by rw [WyhashInit.object_frame_layout frame typed]; exact region.1) region.2
    (by rw [WyhashInit.object_frame_layout frame typed]; rfl), typed]
  have geometry := WyhashUpdate.word_geometry offset member
  have checked := WyhashLocal.word_typed bits
  simp only [usize] at geometry checked
  simp only [Cells.read, geometry.2, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    usize, Cells.readLeaf, geometry.1, ne_self_iff_false, found, checked]

theorem object_word_store {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (typed : frame.cell.type = WyhashLocal.objectType) (offset : Nat) (member : offset ∈ [16, 24, 32, 40, 48])
    (bits : BitVec 64) :
    Memory.store (frame.install cells) (.pointer (.pointer true false usize) ⟨id, offset⟩) (WyhashLocal.word bits) =
      .ok (frame.install (cells.set offset (WyhashLocal.word bits))) := by
  have region : offset + 8 ≤ 104 ∧ offset % 8 = 0 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
  have written := frame.store_eq cells offset (WyhashLocal.word bits) ⟨8, 8⟩
    (WyhashLocal.word_typed bits) rfl (by decide)
    (by rw [WyhashInit.object_frame_layout frame typed]; exact region.1) region.2
    (by rw [WyhashInit.object_frame_layout frame typed]; rfl)
  rw [typed] at written
  have copied := WyhashUpdate.store_eq cells offset bits member
  change cells.write WyhashLocal.objectType offset (WyhashLocal.word bits) = _ at copied
  rw [copied] at written
  exact written

theorem lane_read {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (typed : frame.cell.type = objectType) (index : Fin 3) (bits : BitVec 64)
    (found : cells.lookup (16 + index.val * 8) = some (WyhashLocal.word bits)) :
    Memory.load (frame.install cells) (.pointer (.pointer true false usize) ⟨id, 16 + index.val * 8⟩) =
      .ok (WyhashLocal.word bits) := by
  have member : 16 + index.val * 8 ∈ [16, 24, 32, 40, 48] := by
    have := index.isLt
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  exact object_word_read frame cells (typed.trans object_native) _ member bits found

theorem lane_store {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (typed : frame.cell.type = objectType) (index : Fin 3) (bits : BitVec 64) :
    Memory.store (frame.install cells) (.pointer (.pointer true false usize) ⟨id, 16 + index.val * 8⟩)
      (WyhashLocal.word bits) = .ok (frame.install (cells.set (16 + index.val * 8) (WyhashLocal.word bits))) := by
  have member : 16 + index.val * 8 ∈ [16, 24, 32, 40, 48] := by
    have := index.isLt
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  exact object_word_store frame cells (typed.trans object_native) _ member bits

end Compiler.ZigAir.WyhashInit
