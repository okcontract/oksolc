/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirRead

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Compiler.ZigAir.WyhashUpdateAir.Round
open Memory AggregateAir Control.Machine
abbrev Code := WordRead.Code

/-- The complete taken branches, including their original continuations. -/
def fillBody : Code := (do
  let body ← GeneratedWyhashUpdate.update.body.blockBody? 52
  let .branch _ yes _ := body.dropBindings 5 | none
  pure yes).getD (.ret (.constant (.value (.scalar .unit))))

def loopBody : Code := (do
  let body ← GeneratedWyhashUpdate.update.body.blockBody? 328
  let .branch _ yes _ := body.dropBindings 7 | none
  pure yes).getD (.ret (.constant (.value (.scalar .unit))))

theorem generated_fill_branch :
    (GeneratedWyhashUpdate.update.body.blockBody? 52).map (fun body => body.dropBindings 5) =
      some (.branch (.local 57) fillBody (.jump 52 (.constant (.value (.scalar .unit))))) := by
  decide +kernel

theorem generated_loop_branch :
    (GeneratedWyhashUpdate.update.body.blockBody? 328).map (fun body => body.dropBindings 7) =
      some (.branch (.local 335) loopBody (.jump 326 (.constant (.value (.scalar .unit))))) := by
  decide +kernel

def readSite (loop : Bool) (lane : Fin 3) (second : Bool) : Code :=
  (if loop then loopBody else fillBody).dropBindings
    ((if loop then 14 else 37) + 61 * lane.val + (if second then 17 else 0))

def readBase (loop : Bool) (lane : Fin 3) (second : Bool) : Nat :=
  94 + (if loop then 257 else 0) + 75 * lane.val + (if second then 21 else 0)

def readGuard (loop : Bool) (lane : Fin 3) (second : Bool) : Nat :=
  (if loop then 668 else 655) + 4 * lane.val + (if second then 2 else 0)

def readOffset (lane : Fin 3) (second : Bool) : Nat :=
  16 * lane.val + (if second then 8 else 0)

/-- Every read in both captured rounds reassembles from the one parameterized
sequence and its exact original continuation. No intervening instruction is
dropped, including allocation, assertion and the two source bounds. -/
theorem generated_read_sites : ∀ loop lane second,
    readSite loop lane second =
      WordRead.code (readBase loop lane second) (readGuard loop lane second)
        (if loop then 350 else 93) (readOffset lane second)
        ((readSite loop lane second).dropBindings 17) := by
  decide +kernel

theorem read_bounds (loop : Bool) (lane : Fin 3) (second : Bool) :
    readBase loop lane second + 16 < readGuard loop lane second ∧ readOffset lane second + 8 ≤ 48 := by
  have := lane.isLt
  cases loop <;> cases second <;> simp only [readBase, readGuard, readOffset,
    Bool.false_eq_true, ↓reduceIte] <;> omega

/-- Consume the shared execution theorem at every actual captured read site. -/
theorem read_steps (loop : Bool) (lane : Fin 3) (second : Bool)
    (frames : List (Frame Ty AggregateCall.Prim Ref))
    (state : State) (valid : state.valid = true) (address : Address) (bytes : Nat → BitVec 8)
    (reads : ByteRange.Reads state address 48 bytes) (savedId : Nat)
    (read : Memory.load state (slot false (WordRead.arrayPointer 48) savedId) =
      .ok (.pointer (WordRead.arrayPointer 48) address))
    (args : List Register) (env : Env)
    (found : env (if loop then 350 else 93) = some (.value (slot false (WordRead.arrayPointer 48) savedId))) :
    ∃ after, StackFrame state after ∧
      (Steps AggregateCall.semantics args
          (.suspended ⟨readSite loop lane second, env, state, frames⟩)
          (.finished (.fault .outOfMemory after)) ∨
       Steps AggregateCall.semantics args
          (.suspended ⟨readSite loop lane second, env, state, frames⟩)
          (.suspended ⟨(readSite loop lane second).dropBindings 17,
            WordRead.resultEnv env (readBase loop lane second) (readGuard loop lane second)
              state.nextId address (readOffset lane second) bytes, after, frames⟩)) := by
  have bounds := read_bounds loop lane second
  have path := WordRead.steps (readBase loop lane second) (readGuard loop lane second)
    (if loop then 350 else 93) (readOffset lane second) savedId bounds.1
    ((readSite loop lane second).dropBindings 17) frames state valid address bytes reads bounds.2 read args env found
  simpa only [← generated_read_sites loop lane second] using path

end Compiler.ZigAir.WyhashUpdateAir.Round
