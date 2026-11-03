/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.AggregateAir
import Compiler.ZigAir.MemoryCellFrame
import Compiler.ZigAir.BitwiseProofs

namespace Compiler.ZigAir.AggregateAir
open Memory

/-- Assigning a partial object replaces its initialization state, including
forgetting previously initialized destination leaves absent from the source. -/
theorem store_root {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (aggregate : aggregateType frame.cell.type = true)
    (valid : cells.valid frame.cell.type = true) :
    store state (.pointer (.pointer true false frame.cell.type) ⟨id, 0⟩)
      (.aggregate frame.cell.type cells) = .ok (frame.install cells) := by
  simp only [store, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ne_self_iff_false,
    aggregate, valid, or_self, frame.shaped, frame.admitted, bind, Except.bind, CellFrame.install]

/-- A by-value copy retains precisely the same sparse cells. It does not
convert absent leaves into scalar values, nor retain a pointer to the local. -/
theorem load_root (state : State) (id : Nat) (cell : Allocation) (layout : Layout)
    (shaped : cell.type.layout = some layout)
    (accessed : access state ⟨id, 0⟩ layout false = .ok cell)
    (aggregate : aggregateType cell.type = true) (valid : cell.cells.valid cell.type = true) :
    load state (.pointer (.pointer true false cell.type) ⟨id, 0⟩) = .ok (.aggregate cell.type cell.cells) := by
  simp only [load, aggregate, ↓reduceIte, shaped, accessed, bind, Except.bind,
    ne_self_iff_false, or_self, valid, Bool.not_true, Bool.false_eq_true]

theorem scalar_xor (left right : Scalar.Ref) (args : List Scalar.Value) (env : Scalar.Env)
    (a b : BitVec n)
    (first : left.eval env = .ok (.int false n a.toNat))
    (second : right.eval env = .ok (.int false n b.toNat)) :
    (Scalar.Prim.bitXor left right).eval args env = .ok (.int false n (a ^^^ b).toNat) := by
  simp [Scalar.Prim.eval, first, second, bind, Except.bind, BitVec.toNat_xor]

def number (bits : BitVec n) : Register := .value (.scalar (.int false n bits.toNat))

@[simp] theorem scalar_bitvec_valid (bits : BitVec n) :
    (Scalar.Value.int false n bits.toNat).valid = true :=
  Scalar.unsigned_nat_valid _ _ bits.isLt

@[simp] theorem bitvec_cells_valid (bits : BitVec n) :
    Cells.valid [(0, .scalar (.int false n bits.toNat))] (.scalar (.int false n)) = true := by
  simp [Cells.valid, leafFits, leafType, Value.type, Scalar.Value.type, Value.valid]

@[simp] theorem number_valid (bits : BitVec n) : (number bits).valid = true :=
  Scalar.unsigned_nat_valid _ _ bits.isLt

@[simp] theorem number_typed (bits : BitVec n) :
    (number bits).hasType (.scalar (.int false n)) = true := by
  simp only [Register.hasType, number, Register.type, Value.type, Scalar.Value.type, decide_true,
    Bool.true_and]
  exact number_valid bits

theorem scalar_extend (left : Scalar.Ref) (args : List Scalar.Value) (env : Scalar.Env)
    (a : BitVec n) (bound : n ≤ m) (first : left.eval env = .ok (.int false n a.toNat)) :
    (Scalar.Prim.cast .unchecked (.int false m) left).eval args env =
      .ok (.int false m (a.zeroExtend m).toNat) := by
  have range := Scalar.unsigned_nat_valid a.toNat m (Nat.lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by decide) bound))
  change (Scalar.Ty.int false m).contains a.toNat = true at range
  simp [Scalar.Prim.eval, first, bind, Except.bind, Scalar.integer, range,
    BitVec.zeroExtend, BitVec.toNat_setWidth_of_le bound]

theorem scalar_trunc (left : Scalar.Ref) (args : List Scalar.Value) (env : Scalar.Env)
    (a : BitVec n) (bound : m ≤ n) (first : left.eval env = .ok (.int false n a.toNat)) :
    (Scalar.Prim.cast .trunc (.int false m) left).eval args env =
      .ok (.int false m (a.truncate m).toNat) := by
  simp [Scalar.Prim.eval, first, bind, Except.bind, Scalar.integer, Scalar.normalize, bound,
    BitVec.truncate, BitVec.toNat_setWidth]

theorem scalar_mul (left right : Scalar.Ref) (args : List Scalar.Value) (env : Scalar.Env)
    (a b : BitVec n)
    (first : left.eval env = .ok (.int false n a.toNat))
    (second : right.eval env = .ok (.int false n b.toNat)) :
    (Scalar.Prim.arithmetic .mul .wrapping left right).eval args env =
      .ok (.int false n (a * b).toNat) := by
  simp [Scalar.Prim.eval, first, second, bind, Except.bind, Scalar.integer, Scalar.normalize,
    Scalar.Arithmetic.eval, BitVec.toNat_mul, Int.natCast_mul]

/-- Keep operand evaluation opaque when composing checked integer arithmetic.
Concrete constant references must not force kernel evaluation of the interpreter. -/
theorem scalar_arithmetic (operation : Scalar.Arithmetic) (mode : Scalar.Overflow)
    (left right : Scalar.Ref) (args : List Scalar.Value) (env : Scalar.Env)
    (signed : Bool) (width : Nat) (a b : Int)
    (first : left.eval env = .ok (.int signed width a))
    (second : right.eval env = .ok (.int signed width b)) :
    (Scalar.Prim.arithmetic operation mode left right).eval args env =
      Scalar.integer signed width (operation.eval a b) mode := by
  simp only [Scalar.Prim.eval, first, second, bind, Except.bind, and_self, ↓reduceIte]

theorem scalar_shift (left right : Scalar.Ref) (args : List Scalar.Value) (env : Scalar.Env)
    (a : BitVec n) (k : Nat) (bound : k < n)
    (first : left.eval env = .ok (.int false n a.toNat))
    (second : right.eval env = .ok (.int false (Scalar.shiftCountWidth n) k)) :
    (Scalar.Prim.shiftRight left right).eval args env = .ok (.int false n (a >>> k).toNat) := by
  rw [Scalar.shiftRight_eval _ _ _ _ _ _ _ first second bound]
  simp only [BitVec.toNat_ushiftRight]

theorem ref_local (env : Env) (id : Nat) (value : Register)
    (found : env id = some value) (valid : value.valid = true) :
    (Ref.local id).eval env = .ok value := by
  simp only [Ref.eval, found, valid, bind, Except.bind, ↓reduceIte]

theorem ref_constant (value : Register) (valid : value.valid = true) :
    (Ref.constant value).eval env = .ok value := by
  simp only [Ref.eval, valid, ↓reduceIte, bind, Except.bind]

theorem value_constant (value : Value) (valid : value.valid = true) :
    (Ref.constant (.value value)).value env = .ok value := by
  simp only [Ref.value, Ref.eval, Register.valid, valid, ↓reduceIte, bind, Except.bind]

theorem value_local (env : Env) (id : Nat) (value : Value)
    (found : env id = some (.value value)) (valid : value.valid = true) :
    (Ref.local id).value env = .ok value := by
  simp only [Ref.value, ref_local _ _ _ found valid, bind, Except.bind]

theorem scalar_local (env : Env) (id : Nat) (bits : BitVec n)
    (found : env id = some (number bits)) :
    (Scalar.Ref.local id).eval (MemoryAir.scalarEnv (values env)) = .ok (.int false n bits.toNat) := by
  have valid := Scalar.unsigned_nat_valid bits.toNat n bits.isLt
  simp only [Scalar.Ref.eval, MemoryAir.scalarEnv, values, found, number, valid, ↓reduceIte]

theorem bind_ok (id : Nat) (type : Ty) (prim : Prim) (next : Code)
    (args : List Register) (env : Env) (state after : State) (value : Register)
    (executed : prim.eval args env state = (.ok value, after)) (typed : value.hasType type = true) :
    (Control.Code.bind id type prim next).eval semantics args env state =
      next.eval semantics args (env.set id value) after := by
  simp only [Control.Code.eval, semantics, executed, typed, ↓reduceIte]

theorem ret_ok (ref : Ref) (args : List Register) (env : Env) (state : State) (value : Register)
    (read : ref.eval env = .ok value) :
    (Control.Code.ret ref).eval semantics args env state = .returned value state := by
  simp only [Control.Code.eval, semantics, read]

theorem eval_scalar (operation : Scalar.Prim) (args : List Register) (env : Env) (state : State)
    (value : Scalar.Value) (evaluated : operation.eval [] (MemoryAir.scalarEnv (values env)) = .ok value) :
    (Prim.memory (.scalar operation)).eval args env state = (.ok (.value (.scalar value)), state) := by
  simp only [Prim.eval, Prim.transition, MemoryAir.Prim.transition, evaluated, bind, Except.bind]

/-- Reuse the fully applied primitive equations without unfolding the memory
evaluator beneath function-valued environments in each aggregate client. -/
theorem eval_memory (operation : MemoryAir.Prim) (args : List Register) (env : Env) (state after : State)
    (value : Value) (evaluated : operation.eval [] (values env) state = (.ok value, after)) :
    (Prim.memory operation).eval args env state = (.ok (.value value), after) := by
  cases executed : operation.transition [] (values env) state with
  | error fault => simp only [MemoryAir.Prim.eval, executed] at evaluated; cases evaluated
  | ok pair =>
    obtain ⟨result, reached⟩ := pair
    simp only [MemoryAir.Prim.eval, executed, Prod.mk.injEq, Except.ok.injEq] at evaluated
    obtain ⟨rfl, rfl⟩ := evaluated
    simp only [Prim.eval, Prim.transition, executed, bind, Except.bind]

theorem eval_store (pointer value : Ref) (args : List Register) (env : Env) (state after : State)
    (address : Value) (operand : Register)
    (pointerRead : pointer.value env = .ok address) (valueRead : value.eval env = .ok operand)
    (written : AggregateAir.store state address operand = .ok after) :
    (Prim.store pointer value).eval args env state = (.ok (.value (.scalar .unit)), after) := by
  simp only [Prim.eval, Prim.transition, pointerRead, valueRead, written, bind, Except.bind]

theorem eval_load (pointer : Ref) (args : List Register) (env : Env) (state : State)
    (address : Value) (result : Register)
    (pointerRead : pointer.value env = .ok address) (read : AggregateAir.load state address = .ok result) :
    (Prim.load pointer).eval args env state = (.ok result, state) := by
  simp only [Prim.eval, Prim.transition, pointerRead, read, bind, Except.bind, pure, Except.pure]

theorem eval_alloc (child : Ty) (args : List Register) (env : Env) (state after : State) (value : Value)
    (allocated : Memory.allocate state child = .ok (value, after)) :
    (Prim.memory (.alloc child)).eval args env state = (.ok (.value value), after) := by
  simp only [Prim.eval, Prim.transition, MemoryAir.Prim.transition, allocated, bind, Except.bind]

theorem eval_field (pointer : Ref) (offset : Nat) (args : List Register) (env : Env) (state : State)
    (address result : Value) (pointerRead : pointer.value env = .ok address)
    (selected : Memory.fieldPointer state address offset = .ok result) :
    (Prim.fieldPointer pointer offset).eval args env state = (.ok (.value result), state) := by
  simp only [Prim.eval, Prim.transition, pointerRead, selected, bind, Except.bind, pure, Except.pure]

theorem eval_element (pointer index : Ref) (args : List Register) (env : Env) (state : State)
    (address result : Value) (number : Nat) (pointerRead : pointer.value env = .ok address)
    (indexRead : index.value env = .ok (.scalar (.int false 64 number)))
    (selected : AggregateAir.arrayElementPointer state address number = .ok result) :
    (Prim.arrayElementPointer pointer index).eval args env state = (.ok (.value result), state) := by
  simp only [Prim.eval, Prim.transition, pointerRead, indexRead, Int.toNat_natCast, selected,
    bind, Except.bind, pure, Except.pure]

/-- Array indexing discharges its retained parent bound before reusing the
original native pointer-arithmetic theorem. -/
theorem array_element (state : State) (writable : Bool) (child : Ty) (length index : Nat)
    (address : Address) (parent element : Layout) (cell : Allocation)
    (bound : index < length) (parentShape : (Ty.array length child).layout = some parent)
    (elementShape : child.layout = some element) (positive : 0 < element.bytes)
    (full : access state address parent false = .ok cell)
    (view : acceptsView cell.type address.offset (.array length child) = true)
    (start : access state address ⟨0, element.alignment⟩ false = .ok cell)
    (finish : access state ⟨address.allocation, address.offset + index * element.bytes⟩ element false = .ok cell) :
    AggregateAir.arrayElementPointer state (.pointer (.pointer writable false (.array length child)) address) index =
      .ok (.pointer (.pointer writable false child) ⟨address.allocation, address.offset + index * element.bytes⟩) := by
  have casted : Memory.pointerCast state (.pointer writable true child)
      (.pointer (.pointer writable false (.array length child)) address) =
        .ok (.pointer (.pointer writable true child) address) := by
    cases writable <;> simp [Memory.pointerCast, pointerCompatible, elementShape, start, bind, Except.bind]
  simp only [arrayElementPointer, Nat.not_le.mpr bound, ↓reduceIte, parentShape, full,
    bind, Except.bind, view, Bool.not_true, Bool.false_eq_true, casted]
  exact elementPointer_of_access state writable child address index element cell elementShape positive start finish

@[simp] theorem pointer_typed (child : Ty) (address : Address) :
    (Register.value (.pointer (.pointer true false child) address)).hasType (.pointer true false child) = true := by
  simp [Register.hasType, Register.type, Register.valid, Value.type, Value.valid]

/-- Exact two-instruction allocation/store composition, reusing the existing
scoped-creation outcome and cleanup machinery. The caller proves the concrete
store law once for the admitted register representation. -/
theorem create_bindings (owner : Ty) (layout : Layout) (cells : Cells) (value : Register)
    (reference : Ref) (allocationReg storeReg : Nat) (next : Code)
    (args : List Register) (env : Env) (state : State)
    (shaped : owner.layout = some layout) (positive : 0 < layout.bytes) (valid : cells.valid owner = true)
    (read : reference.eval (env.set allocationReg (.value (.pointer (.pointer true false owner) ⟨state.nextId, 0⟩))) = .ok value)
    (storeLaw : ∀ {allocated : State} (frame : CellFrame allocated state.nextId),
      frame.cell.type = owner → frame.cell.cells = [] →
      AggregateAir.store allocated (.pointer (.pointer true false owner) ⟨state.nextId, 0⟩) value = .ok (frame.install cells)) :
    (Control.Code.bind allocationReg (.pointer true false owner) (.memory (.alloc owner))
      (.bind storeReg (.scalar .unit) (.store (.local allocationReg) reference) next)).eval semantics args env state =
      match CellFrame.create state owner (fun _ => .ok ((), cells)) with
      | (.error fault, after) => .fault fault after
      | (.ok (_, id), after) => next.eval semantics args
          ((env.set allocationReg (.value (.pointer (.pointer true false owner) ⟨id, 0⟩))).set storeReg (.value (.scalar .unit))) after := by
  cases allocation : Memory.allocate state owner with
  | error fault =>
    simp only [Control.Code.eval, semantics, Prim.eval, Prim.transition, MemoryAir.Prim.transition,
      allocation, bind, Except.bind, CellFrame.create]
  | ok pair =>
    obtain ⟨pointer, allocated⟩ := pair
    obtain ⟨actual, base, _, pointerEq, _⟩ := allocate_shape state owner pointer allocated allocation
    obtain ⟨frame, type, empty, shape⟩ := CellFrame.allocated state owner layout pointer allocated shaped positive allocation
    have borrowed := frame.borrow_eq (fun _ => .ok ((), cells)) () cells rfl (type ▸ valid)
    rw [type] at borrowed
    have creation : CellFrame.create state owner (fun _ => .ok ((), cells)) =
        (.ok ((), state.nextId), frame.install cells) := by
      simp only [CellFrame.create, allocation, borrowed]
    rw [creation]
    have allocates := eval_alloc owner args env state allocated pointer allocation
    rw [pointerEq] at allocates
    refine (bind_ok _ _ _ _ _ _ _ _ _ allocates (pointer_typed _ _)).trans ?_
    apply bind_ok
    · exact eval_store _ _ _ _ _ _ _ _
        (value_local _ allocationReg _ (by simp [Control.Env.set]) rfl) read (storeLaw frame type empty)
    · rfl

theorem run_return (program : Program) (args : List Register) (state after : State) (value : Register)
    (checked : (state.valid && decide (args.length = program.parameters.length) &&
      (args.zip program.parameters).all (fun (value, type) => value.hasType type)) = true)
    (ran : program.body.eval semantics args (fun _ => none) state = .returned value after)
    (typed : value.hasType program.returnType = true) :
    program.run args state = (.ok value, cleanup state.nextId after) := by
  simp only [Program.run, checked, ↓reduceIte, ran, Program.finish, typed]

theorem run_fault (program : Program) (args : List Register) (state after : State) (fault : Fault)
    (checked : (state.valid && decide (args.length = program.parameters.length) &&
      (args.zip program.parameters).all (fun (value, type) => value.hasType type)) = true)
    (ran : program.body.eval semantics args (fun _ => none) state = .fault fault after) :
    program.run args state = (.error fault, cleanup state.nextId after) := by
  simp only [Program.run, checked, ↓reduceIte, ran, Program.finish]

end Compiler.ZigAir.AggregateAir
