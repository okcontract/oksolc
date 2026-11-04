/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Evm.Storage
import Contract.Evm.Frames

namespace Contract.Evm.Stateful
open Interaction (Word)

/-- Transaction-wide original values, access set and signed refund counter.
Calls in this subset cannot access other accounts. Entry may be warm or dirty;
the original values need not equal the current world at frame entry. -/
structure Transaction where
  original : Address → Slots
  warm : Address → Word → Bool := fun _ _ => false
  refund : Int := 0

def World.store (world : Evm.World) (target : Address) (storage : Slots) : Evm.World :=
  { world with storage := fun a => if a = target then storage else world.storage a }

def Transaction.commit (transaction : Transaction) (target : Address) (state : State) : Transaction :=
  { transaction with
    warm := fun a => if a = target then state.warm else transaction.warm a,
    refund := state.refund }

structure Frame extends Observation where
  transaction : Transaction

def initial (world : Evm.World) (transaction : Transaction) (target : Address) : State :=
  { storage := world.storage target, warm := transaction.warm target, refund := transaction.refund }

/-- Writes, warming and refunds commit together on return. Revert/exceptional
halt restore the complete pre-frame snapshot, including the access set. -/
def observe (world : Evm.World) (transaction : Transaction) (ctx : Contract.Context)
    (input : Input) : Guarded.Metered Result → Frame
  | .finished gas ⟨.returned bytes, state⟩ =>
    ⟨⟨.returned, bytes, (World.store world ctx.self state.storage).transfer ctx.caller ctx.self input.value, gas⟩,
      transaction.commit ctx.self state⟩
  | .finished gas ⟨.reverted bytes, _⟩ => ⟨⟨.reverted, bytes, world, gas⟩, transaction⟩
  | .exceptional => ⟨⟨.exceptional, [], world, 0⟩, transaction⟩
  | .unsupported _ => ⟨⟨.unsupported, [], world, 0⟩, transaction⟩
  | .exhausted => ⟨⟨.exhausted, [], world, 0⟩, transaction⟩

def executeCall (world : Evm.World) (transaction : Transaction) (ctx : Contract.Context)
    (input : Input) (isStatic : Bool) (fuel gas : Nat) : Frame :=
  observe world transaction ctx input
    (runMetered (world.code ctx.self) input ⟨transaction.original ctx.self, isStatic⟩
      fuel gas (initial world transaction ctx.self))

/-- Reuse the reviewed code-size/prefix/deposit policy. If code deposit fails,
storage, nonce preparation, warming and refunds all roll back. -/
def finishCreation (before prepared : Evm.World) (transaction : Transaction)
    (ctx : Contract.Context) (input : Input) : Guarded.Metered Result → Frame
  | .finished gas ⟨.returned bytes, state⟩ =>
    let result := finishDeployment before (World.store prepared ctx.self state.storage) ctx input
      (.finished gas (.returned bytes))
    ⟨result, if result.status = .returned then transaction.commit ctx.self state else transaction⟩
  | other => observe before transaction ctx input other

def executeCreation (code : List UInt8) (world : Evm.World) (transaction : Transaction)
    (ctx : Contract.Context) (_fresh : Fresh world ctx.self) (input : Input) (fuel gas : Nat) : Frame :=
  if code.length ≤ 49152 then
    finishCreation world (world.prepare ctx.self) transaction ctx input
      (runMetered code input ⟨transaction.original ctx.self, false⟩ fuel gas (initial world transaction ctx.self))
  else ⟨⟨.exceptional, [], world, 0⟩, transaction⟩

theorem store_other_account (world : Evm.World) (target other : Address) (storage : Slots)
    (different : other ≠ target) : (World.store world target storage).storage other = world.storage other := by
  simp [World.store, different]

theorem write_other_key (storage : Slots) (key other value : Word) (different : other ≠ key) :
    write storage key value other = storage other := by simp [write, different]

theorem revert_rolls_back (world transaction ctx input gas bytes state) :
    observe world transaction ctx input (.finished gas ⟨.reverted bytes, state⟩) =
      ⟨⟨.reverted, bytes, world, gas⟩, transaction⟩ := rfl

theorem exceptional_rolls_back (world transaction ctx input) :
    observe world transaction ctx input .exceptional = ⟨⟨.exceptional, [], world, 0⟩, transaction⟩ := rfl

end Contract.Evm.Stateful
