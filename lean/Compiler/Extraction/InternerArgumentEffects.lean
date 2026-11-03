/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerOwnedMemoryEffects
import Compiler.Extraction.InternerTemporaryTernary
import Compiler.Extraction.LocalArgumentsProgram

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
open Compiler.Algebraic Compiler.ZigAir.Memory.WordArray

namespace TemporaryArguments.EffectTransport
variable (project : σ → τ)

/-- Ordered literals retain every completed store, including a prefix followed
by a fault. Projection changes only private effects, never that reached memory. -/
theorem orderedStores
    (first : Except Compiler.ZigAir.Memory.Fault Compiler.ZigAir.Memory.State)
    (second : Compiler.ZigAir.Memory.State → Except Compiler.ZigAir.Memory.Fault Compiler.ZigAir.Memory.State)
    (source : View) (before : World σ) :
    TemporaryArguments.orderedStores first second source (before.mapEffects project) =
      ((TemporaryArguments.orderedStores first second source before).1,
       (TemporaryArguments.orderedStores first second source before).2.mapEffects project) := by
  unfold TemporaryArguments.orderedStores
  cases first with
  | error fault => rfl
  | ok written => dsimp only; cases second written <;> rfl

theorem writePair (source : View) (first second : NodeId) :
    Effect.Transport (World.mapEffects project)
      (TemporaryArguments.writePair source first second) (TemporaryArguments.writePair source first second) :=
  fun before => orderedStores project _ _ source before

theorem prepare (first second : NodeId) :
    Effect.Transport (World.mapEffects project)
      (TemporaryArguments.prepare first second) (TemporaryArguments.prepare first second) := by
  intro before
  unfold TemporaryArguments.prepare
  simp only [show (before.mapEffects project).memory.memory = before.memory.memory from rfl]
  cases Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) with
  | error fault => rfl
  | ok allocated =>
    rcases allocated with ⟨pointer, memory⟩
    dsimp only
    exact writePair project ⟨before.memory.memory.nextId, 0, 2⟩ first second
      { before with memory := { before.memory with memory } }

theorem unwind (mark : Nat) (ran : Except Fault NodeId × State σ) :
    TemporaryArguments.unwind mark (ran.1, ran.2.mapEffects project) =
      ((TemporaryArguments.unwind mark ran).1, (TemporaryArguments.unwind mark ran).2.mapEffects project) := by
  unfold TemporaryArguments.unwind
  cases ordinary ran.1 <;> rfl

end TemporaryArguments.EffectTransport

namespace TemporaryUnary.EffectTransport
variable (project : σ → τ)

theorem writeOne (source : View) (value : NodeId) :
    Effect.Transport (World.mapEffects project)
      (TemporaryUnary.writeOne source value) (TemporaryUnary.writeOne source value) :=
  fun before => TemporaryArguments.EffectTransport.orderedStores project _ _ source before

theorem prepare (value : NodeId) :
    Effect.Transport (World.mapEffects project)
      (TemporaryUnary.prepare value) (TemporaryUnary.prepare value) := by
  intro before
  unfold TemporaryUnary.prepare
  simp only [show (before.mapEffects project).memory.memory = before.memory.memory from rfl]
  cases Compiler.ZigAir.Memory.allocate before.memory.memory (.array 1 word) with
  | error fault => rfl
  | ok allocated =>
    rcases allocated with ⟨pointer, memory⟩
    dsimp only
    exact writeOne project ⟨before.memory.memory.nextId, 0, 1⟩ value
      { before with memory := { before.memory with memory } }

end TemporaryUnary.EffectTransport

namespace TemporaryTernary.EffectTransport
variable (project : σ → τ)

theorem writeTriple (source : View) (first second third : NodeId) :
    Effect.Transport (World.mapEffects project)
      (TemporaryTernary.writeTriple source first second third) (TemporaryTernary.writeTriple source first second third) :=
  Effect.Transport.bind _ (TemporaryArguments.EffectTransport.writePair project source first second)
    (fun _ => Effect.Transport.bind _ (TemporaryUnary.EffectTransport.writeOne project _ third)
      (fun _ => Effect.Transport.pure _ source))

theorem prepare (first second third : NodeId) :
    Effect.Transport (World.mapEffects project)
      (TemporaryTernary.prepare first second third) (TemporaryTernary.prepare first second third) := by
  intro before
  unfold TemporaryTernary.prepare
  simp only [show (before.mapEffects project).memory.memory = before.memory.memory from rfl]
  cases Compiler.ZigAir.Memory.allocate before.memory.memory (.array 3 word) with
  | error fault => rfl
  | ok allocated =>
    rcases allocated with ⟨pointer, memory⟩
    dsimp only
    exact writeTriple project ⟨before.memory.memory.nextId, 0, 3⟩ first second third
      { before with memory := { before.memory with memory } }

end TemporaryTernary.EffectTransport

namespace LocalArguments.EffectTransport
variable (project : σ → τ)

/-- Unlike ordered literals, the named aggregate commits both stores at once.
Use the actual helper so its rollback on either store fault is retained. -/
theorem initPair (target : View) (left right : NodeId) :
    Effect.Transport (World.mapEffects project)
      (LocalArguments.initPair target left right) (LocalArguments.initPair target left right) := by
  intro before
  unfold LocalArguments.initPair
  rw [TemporaryArguments.EffectTransport.writePair project]
  cases TemporaryArguments.writePair target left right before with
  | mk result reached => cases result <;> rfl

theorem copy (source : View) :
    Effect.Transport (World.mapEffects project) (LocalArguments.copy source) (LocalArguments.copy source) := by
  intro before
  unfold LocalArguments.copy
  simp only [show (before.mapEffects project).memory.memory = before.memory.memory from rfl]
  split
  · rfl
  · cases Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) with
    | error fault => rfl
    | ok allocated =>
      rcases allocated with ⟨pointer, memory⟩
      dsimp only
      cases LocalArguments.readId memory source 0 with
      | error fault => rfl
      | ok left =>
        dsimp only
        cases LocalArguments.readId memory source 1 with
        | error fault => rfl
        | ok right =>
          dsimp only
          exact initPair project ⟨before.memory.memory.nextId, 0, 2⟩ left right
            { before with memory := { before.memory with memory } }

theorem overwrite (source : View) (index : Nat) (value : NodeId) :
    Effect.Transport (World.mapEffects project)
      (LocalArguments.overwrite source index value) (LocalArguments.overwrite source index value) :=
  fun before => TemporaryArguments.EffectTransport.orderedStores project _ _ source before

theorem zigLocal (source : View) (selected : Nat) (repeated : NodeId) (first : Bool) :
    Effect.Transport (World.mapEffects project)
      (LocalArguments.zigLocal source selected repeated first) (LocalArguments.zigLocal source selected repeated first) := by
  intro before
  unfold LocalArguments.zigLocal
  rw [copy project]
  cases LocalArguments.copy source before with
  | mk result reached =>
    cases result with
    | error fault => rfl
    | ok target =>
      cases first with
      | false => rfl
      | true => exact overwrite project target selected repeated reached

end LocalArguments.EffectTransport
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
