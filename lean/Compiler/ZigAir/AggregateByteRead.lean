/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.AggregateAirProofs
import Compiler.ZigAir.MemoryAirLaws
import Compiler.ZigAir.MemoryByteRangeRead

namespace Compiler.ZigAir.AggregateAir
open Memory

/-- Keep reference evaluation abstract while composing pointer arithmetic.
Unfolding a concrete integer reference can eagerly reduce its 64-bit bound. -/
theorem eval_offset (pointer count : MemoryAir.Ref) (args : List Register) (env : Env)
    (state : State) (address result : Value) (offset : Nat)
    (data : pointer.eval (values env) = .ok address)
    (size : count.natural (values env) = .ok offset)
    (advanced : Memory.offsetPointer state false address offset = .ok result) :
    (Prim.memory (.offsetPointer false pointer count)).eval args env state =
      (.ok (.value result), state) := by
  apply eval_memory
  simp only [MemoryAir.Prim.eval_offset, data, size, advanced, bind, Except.bind]

theorem eval_bounds (start finish : MemoryAir.Ref) (upper : MemoryAir.Bound)
    (args : List Register) (env : Env) (state : State) (a b : Nat) (limit : Option Nat)
    (first : start.natural (values env) = .ok a) (last : finish.natural (values env) = .ok b)
    (bound : upper.eval (values env) = .ok limit)
    (checked : checkSliceBounds a b limit = .ok ()) :
    (Prim.memory (.checkBounds start finish upper)).eval args env state =
      (.ok (.value (.scalar .unit)), state) := by
  apply eval_memory
  simp only [MemoryAir.Prim.eval, MemoryAir.Prim.transition, first, last, bound, checked, bind, Except.bind]

/-- Load original representation bytes, including bytes within integer leaves.
The pointer register alone is not evidence that those bytes are initialized. -/
theorem eval_load_bytes (state : State) (address : Address) (length offset count : Nat)
    (bytes : Nat → BitVec 8) (reads : ByteRange.Reads state address length bytes)
    (inside : offset + count ≤ length) (args : List Register) (env : Env) (reg : Nat)
    (pointer : env reg = some (.value (.pointer (.pointer false false (.array count ByteSlice.byte))
      ⟨address.allocation, address.offset + offset⟩))) :
    (Prim.loadBytes (.local reg)).eval args env state =
      (.ok (.bytes ((List.range count).map fun i => bytes (offset + i))), state) := by
  have selected := value_local env reg _ pointer rfl
  simp only [Prim.eval, Prim.transition, selected, ByteSlice.byte,
    reads.read_window offset count inside, bind, Except.bind, pure, Except.pure]

theorem eval_bytes_word (state : State) (bytes : Nat → BitVec 8) (offset : Nat)
    (args : List Register) (env : Env) (reg : Nat)
    (found : env reg = some (.bytes ((List.range 8).map fun i => bytes (offset + i)))) :
    (Prim.bytesToWord (.local reg)).eval args env state =
      (.ok (number (ByteSlice.decode bytes offset 8)), state) := by
  have selected := ref_local env reg _ found rfl
  simp only [Prim.eval, Prim.transition, selected, bind, Except.bind,
    List.length_map, List.length_range, ne_self_iff_false, ↓reduceIte, ByteRange.decode_window]
  rfl

end Compiler.ZigAir.AggregateAir
