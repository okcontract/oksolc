/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirLoopExecution

namespace Compiler.ZigAir.WyhashUpdateAir
open Memory AggregateAir Compiler.Extraction Control.Machine

/-- Native subtraction is justified before converting it to natural arithmetic;
underflow is not silently interpreted as a truncated slice index. -/
theorem size_sub (state : State) (args : List Register) (env : Env)
    (left right : Scalar.Ref) (a b : Nat) (bounded : a < addressLimit) (ordered : b ≤ a)
    (first : left.eval (MemoryAir.scalarEnv (values env)) = .ok (.int false 64 a))
    (second : right.eval (MemoryAir.scalarEnv (values env)) = .ok (.int false 64 b)) :
    (AggregateAir.Prim.memory (.scalar (.arithmetic .sub .unchecked left right))).eval args env state =
      (.ok (size (a - b)), state) := by
  apply eval_scalar
  rw [scalar_arithmetic _ _ _ _ _ _ false 64 a b first second]
  have contains := Scalar.unsigned_nat_valid (a - b) 64 (by omega : a - b < addressLimit)
  change (Scalar.Ty.int false 64).contains (a - b : Nat) = true at contains
  simp [Scalar.Arithmetic.eval, ← Int.natCast_sub ordered, Scalar.integer, contains]

theorem slice_valid (mutable : Bool) (address : Address) (count : Nat) (bound : count < addressLimit) :
    (Value.slice (.slice mutable ByteSlice.byte) address count).valid = true := by
  simpa only [Value.valid, decide_eq_true_eq] using bound

theorem size_comparison (state : State) (args : List Register) (env : Env)
    (operation : Scalar.Comparison) (left right : Scalar.Ref) (a b : Nat)
    (first : left.eval (MemoryAir.scalarEnv (values env)) = .ok (.int false 64 a))
    (second : right.eval (MemoryAir.scalarEnv (values env)) = .ok (.int false 64 b)) :
    (AggregateAir.Prim.memory (.scalar (.comparison operation left right))).eval args env state =
      (.ok (.value (.scalar (.bool (operation.eval a b)))), state) := by
  apply eval_scalar
  simp only [Scalar.Prim.eval, first, second, bind, Except.bind, and_self, ↓reduceIte]

theorem slice_pointer (state : State) (args : List Register) (env : Env)
    (reg : Nat) (mutable : Bool) (address : Address) (count : Nat) (bound : count < addressLimit)
    (found : env reg = some (.value (.slice (.slice mutable ByteSlice.byte) address count))) :
    (AggregateAir.Prim.memory (.slicePtr (.local reg))).eval args env state =
      (.ok (.value (.pointer (.pointer mutable true ByteSlice.byte) address)), state) := by
  apply eval_memory
  have data := SliceBytesAir.memory_local env reg _ found (slice_valid mutable address count bound)
  simp only [MemoryAir.Prim.eval, MemoryAir.Prim.transition, data, bind, Except.bind]

theorem slice_length (state : State) (args : List Register) (env : Env)
    (reg : Nat) (mutable : Bool) (address : Address) (count : Nat) (bound : count < addressLimit)
    (found : env reg = some (.value (.slice (.slice mutable ByteSlice.byte) address count))) :
    (AggregateAir.Prim.memory (.sliceLen (.local reg))).eval args env state = (.ok (size count), state) := by
  apply eval_memory
  have data := SliceBytesAir.memory_local env reg _ found (slice_valid mutable address count bound)
  simp only [MemoryAir.Prim.eval, MemoryAir.Prim.transition, data, bind, Except.bind]

/-- Keep slice construction opaque during instruction composition. The access
equation is supplied by the existing byte-window or hasher-buffer lemma. -/
theorem slice_construct (state : State) (args : List Register) (env : Env)
    (pointer countRef : MemoryAir.Ref) (mutable : Bool) (address : Address) (count : Nat)
    (data : pointer.eval (values env) = .ok (.pointer (.pointer mutable true ByteSlice.byte) address))
    (number : countRef.natural (values env) = .ok count)
    (made : makeSlice state (.slice mutable ByteSlice.byte)
      (.pointer (.pointer mutable true ByteSlice.byte) address) count =
        .ok (.slice (.slice mutable ByteSlice.byte) address count)) :
    (AggregateAir.Prim.memory (.slice (.slice mutable ByteSlice.byte) pointer countRef)).eval args env state =
      (.ok (.value (.slice (.slice mutable ByteSlice.byte) address count)), state) := by
  apply eval_memory
  simp only [MemoryAir.Prim.eval, MemoryAir.Prim.transition, data, number, made, bind, Except.bind]

theorem copy_bytes {state : State} {id : Nat} (frame : CellFrame state id)
    (typed : frame.cell.type = objectType) (address : Address) (source cells : Cells)
    (view : ByteSlice.View) (bytes : Nat → BitVec 8) (geometry : ByteSlice.Geometry view)
    (represented : ByteSlice.Represents source view bytes)
    (reads : ByteRange.Reads state address view.length bytes) (apart : address.allocation ≠ id)
    (total src dst count : Nat) (core : WyhashUpdate.Core cells total)
    (sourceBound : src + count ≤ view.length) (targetBound : dst + count ≤ 48)
    (args : List Register) (env : Env) (targetReg sourceReg : Nat)
    (targetFound : env targetReg = some (.value (.slice (.slice true ByteSlice.byte) ⟨id, 56 + dst⟩ count)))
    (sourceFound : env sourceReg = some (.value
      (.pointer (.pointer false true ByteSlice.byte) ⟨address.allocation, address.offset + src⟩))) :
    ∃ after, (AggregateCall.Prim.copyBytes (.local targetReg) (.local sourceReg)).eval args env (frame.install cells) =
        (.ok (.value (.scalar .unit)), frame.install after) ∧
      ByteSlice.copy source view (WyhashBuffer.buffer 0 48) src dst count cells = .ok after ∧
      WyhashUpdate.Core after total ∧
      (∀ i < count, WyhashUpdate.ByteAt after (56 + (dst + i))) ∧
      (∀ offset, offset < 56 + dst ∨ 56 + dst + count ≤ offset → after.lookup offset = cells.lookup offset) := by
  obtain ⟨after, native, model, nextCore, head, outside⟩ := copy_buffer frame typed address source cells
    view bytes geometry represented reads apart total src dst count core sourceBound targetBound
  refine ⟨after, ?_, model, nextCore, head, outside⟩
  have dest := value_local env targetReg _ targetFound
    (slice_valid true _ count (by
      have : 48 < addressLimit := by decide
      omega))
  have src := value_local env sourceReg _ sourceFound rfl
  simp only [AggregateCall.Prim.eval, dest, src, bind, Except.bind, pure, Except.pure, native]
  rfl

end Compiler.ZigAir.WyhashUpdateAir
