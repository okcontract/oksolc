/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryAirLaws

namespace Compiler.ZigAir.MemoryAir
open Memory

theorem Prim.eval_word_byte_cast (writable many : Bool) (alignment : Nat) (pointer : Ref)
    (args : List Value) (env : Env) (state : State) :
    (Prim.wordByteCast writable many alignment pointer).eval args env state =
      ((do ByteAccess.cast state writable many alignment (← pointer.eval env)), state) := by
  cases p : pointer.eval env with
  | error => simp [Prim.eval, Prim.transition, p, bind, Except.bind]
  | ok value =>
    cases result : ByteAccess.cast state writable many alignment value <;>
      simp [Prim.eval, Prim.transition, p, result, bind, Except.bind]

theorem Prim.eval_word_byte_load (order : WordBytes.Order) (pointer : Ref)
    (args : List Value) (env : Env) (state : State) :
    (Prim.wordByteLoad order pointer).eval args env state =
      ((do ByteAccess.read order state (← pointer.eval env)), state) := by
  cases p : pointer.eval env with
  | error => simp [Prim.eval, Prim.transition, p, bind, Except.bind]
  | ok value =>
    cases result : ByteAccess.read order state value <;>
      simp [Prim.eval, Prim.transition, p, result, bind, Except.bind]

theorem Prim.eval_word_byte_store (order : WordBytes.Order) (pointer value : Ref)
    (args : List Value) (env : Env) (state : State) :
    (Prim.wordByteStore order pointer value).eval args env state =
      match (do ByteAccess.write order state (← pointer.eval env) (← value.eval env)) with
      | .ok after => (.ok (.scalar .unit), after)
      | .error reason => (.error reason, state) := by
  cases p : pointer.eval env with
  | error => simp [Prim.eval, Prim.transition, p, bind, Except.bind]
  | ok destination =>
    cases v : value.eval env with
    | error => simp [Prim.eval, Prim.transition, p, v, bind, Except.bind]
    | ok contents =>
      cases result : ByteAccess.write order state destination contents <;>
        simp [Prim.eval, Prim.transition, p, v, result, bind, Except.bind]

end Compiler.ZigAir.MemoryAir
