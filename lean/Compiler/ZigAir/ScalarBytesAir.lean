/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.AggregateAirProofs
import Compiler.ZigAir.AggregateCall
import Compiler.ZigAir.MemoryStackPrefix

namespace Compiler.ZigAir.ScalarBytesAir
open Memory AggregateAir

def byte : Ty := .scalar (.int false 8)

/-- The complete three-instruction asBytes specialization: retain the argument,
cast its declared integer subobject, and return the same address. -/
def castProgram (source : Ty) (alignment count : Nat) : Program where
  parameters := [.pointer false false source]
  returnType := .pointer false false (.array count byte)
  body := .bind 0 (.pointer false false source) (.argument 0)
    (.bind 1 (.pointer false false (.array count byte)) (.scalarByteArray false alignment count (.local 0))
      (.ret (.local 1)))

theorem run_cast (state : State) (address : Address) (cell : Allocation)
    (signed : Bool) (bits alignment count : Nat) (shape : Layout)
    (valid : state.valid = true) (shaped : (Ty.scalar (.int signed bits)).layout = some shape)
    (positive : 0 < bits) (whole : bits % 8 = 0) (counted : count = bits / 8)
    (size : shape.bytes = count) (aligned : 0 < alignment ∧ shape.alignment % alignment = 0)
    (accessed : access state address shape false = .ok cell)
    (viewed : acceptsView cell.type address.offset (.scalar (.int signed bits)) = true) :
    (castProgram (.scalar (.int signed bits)) alignment count).run
      [.value (.pointer (.pointer false false (.scalar (.int signed bits))) address)] state =
      (.ok (.value (.pointer (.pointer false false (.array count byte)) address)), state) := by
  have casted := ScalarBytes.arrayCast_const state address cell signed false false bits alignment count shape
    shaped positive whole counted size aligned accessed viewed
  simp [castProgram, Program.run, valid, Program.finish, Register.hasType, Register.type,
    Register.valid, Value.type, Value.valid, byte, Control.Code.eval, semantics,
    Prim.eval, Prim.transition, Ref.eval, Ref.value, Control.Env.set, casted,
    bind, Except.bind, pure, Except.pure, cleanup_initial state valid]

/-- A caller fragment invokes that exact program and then performs the captured
array-to-slice conversion. Registers remain parameters for source-selected cuts. -/
def viewCode (program : Program) (pointer : AggregateAir.Ref) (callReg sliceReg : Nat)
    (count : Nat) (next : AggregateCall.Code) : AggregateCall.Code :=
  .bind callReg (.pointer false false (.array count byte)) (.invoke program [pointer])
    (.bind sliceReg (.slice false byte) (.primitive (.arrayToSlice (.local callReg))) next)


def slice (address : Address) (count : Nat) : Register :=
  .value (.slice (.slice false byte) address count)

theorem view_verified (state : State) (address : Address) (cell : Allocation)
    (signed : Bool) (bits alignment count callReg sliceReg : Nat) (shape : Layout)
    (pointer : Ref) (args : List Register) (env : Env) (next : AggregateCall.Code)
    (valid : state.valid = true) (bounded : count < addressLimit)
    (resolved : pointer.eval env = .ok (.value (.pointer (.pointer false false (.scalar (.int signed bits))) address)))
    (shaped : (Ty.scalar (.int signed bits)).layout = some shape)
    (positive : 0 < bits) (whole : bits % 8 = 0) (counted : count = bits / 8)
    (size : shape.bytes = count) (aligned : 0 < alignment ∧ shape.alignment % alignment = 0)
    (accessed : access state address shape false = .ok cell)
    (viewed : acceptsView cell.type address.offset (.scalar (.int signed bits)) = true) :
    (viewCode (castProgram (.scalar (.int signed bits)) alignment count) pointer callReg sliceReg count next).eval
      AggregateCall.semantics args env state =
      next.eval AggregateCall.semantics args
        ((env.set callReg (.value (.pointer (.pointer false false (.array count byte)) address))).set sliceReg (slice address count)) state := by
  have called := run_cast state address cell signed bits alignment count shape valid shaped positive whole counted size aligned accessed viewed
  have invoked : (AggregateCall.Prim.invoke (castProgram (.scalar (.int signed bits)) alignment count) [pointer]).eval args env state =
      (.ok (.value (.pointer (.pointer false false (.array count byte)) address)), state) := by
    simp only [AggregateCall.Prim.eval, List.mapM_cons, List.mapM_nil, resolved, bind, Except.bind, pure, Except.pure]
    exact called
  unfold viewCode
  rw [AggregateCall.bind_ok _ _ _ _ _ _ _ _ _ invoked
    (by simp [Register.hasType, Register.type, Register.valid, Value.type, Value.valid])]
  apply AggregateCall.bind_ok
  · simp [AggregateCall.Prim.eval, Prim.eval, Prim.transition, Ref.value, Ref.eval,
      Control.Env.set, ScalarBytes.arrayToSlice, Register.valid, Value.valid, bounded, slice,
      bind, Except.bind, pure, Except.pure]
  · simp [slice, Register.hasType, Register.type, Register.valid, Value.type, Value.valid, bounded]

end Compiler.ZigAir.ScalarBytesAir
