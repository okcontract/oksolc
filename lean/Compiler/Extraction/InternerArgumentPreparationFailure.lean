/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerViewInput

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray

/-- Literal preparation either builds its typed source array or rejects the
memory observation/unsupported shape. It cannot manufacture ordinary native OOM. -/
theorem Arguments.error_nonordinary {before : World σ} (values : List NodeId) (initial : Valid before.memory)
    (reached : World σ) (fault : Fault)
    (failed : Arguments.prepare values before = (.error fault, reached)) :
    ordinary (.error fault : Except Fault NodeId) = false := by
  rcases values with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, tail⟩⟩⟩⟩
  · cases (congrArg Prod.fst failed)
  · cases allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 1 word) with
    | error error =>
      simp only [Arguments.prepare, TemporaryUnary.prepare, allocated, Prod.mk.injEq, Except.error.injEq] at failed
      rw [← failed.1]
      rfl
    | ok pair =>
      obtain ⟨after, ran, _⟩ := TemporaryUnary.prepare_verified a before pair.1 pair.2 initial allocated
      have impossible := congrArg Prod.fst (ran.symm.trans failed)
      cases impossible
  · cases allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) with
    | error error =>
      simp only [Arguments.prepare, TemporaryArguments.prepare, allocated, Prod.mk.injEq, Except.error.injEq] at failed
      rw [← failed.1]
      rfl
    | ok pair =>
      obtain ⟨after, ran, _⟩ := TemporaryArguments.prepare_verified a b before pair.1 pair.2 initial allocated
      have impossible := congrArg Prod.fst (ran.symm.trans failed)
      cases impossible
  · cases allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 3 word) with
    | error error =>
      simp only [Arguments.prepare, TemporaryTernary.prepare, allocated, Prod.mk.injEq, Except.error.injEq] at failed
      rw [← failed.1]
      rfl
    | ok pair =>
      obtain ⟨after, ran, _⟩ := TemporaryTernary.prepare_verified a b c before pair.1 pair.2 initial allocated
      have impossible := congrArg Prod.fst (ran.symm.trans failed)
      cases impossible
  · have same := Except.error.inj (congrArg Prod.fst failed)
    rw [← same]
    rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray

/-- Valid copied words and the guarded selected index discharge every store.
The unused index remains unrestricted when the optional overwrite is skipped. -/
theorem LocalArguments.error_nonordinary {source : View} {before : World σ} (left right repeated : NodeId) (selected : Nat) (first : Bool)
    (good : Good source [left, right] before) (inside : first = true → selected < 2)
    (reached : World σ) (fault : Fault)
    (failed : LocalArguments.zigLocal source selected repeated first before = (.error fault, reached)) :
    ordinary (.error fault : Except Fault NodeId) = false := by
  have safeIndex : (if first then selected else 0) < 2 := by cases first <;> simp_all
  have same : LocalArguments.zigLocal source selected repeated first before =
      LocalArguments.zigLocal source (if first then selected else 0) repeated first before := by
    cases first <;> simp only [LocalArguments.zigLocal, Bool.false_eq_true, ↓reduceIte]
  rw [same] at failed
  cases allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) with
  | error error =>
    have length : source.length = 2 := good.2.1.symm
    simp only [LocalArguments.zigLocal, LocalArguments.copy, length, bne_self_eq_false,
      Bool.false_eq_true, ↓reduceIte, allocated, Prod.mk.injEq, Except.error.injEq] at failed
    rw [← failed.1]
    rfl
  | ok pair =>
    obtain ⟨after, ran, _⟩ := LocalArguments.prepare_verified source left right repeated
      (if first then selected else 0) first before pair.1 pair.2 good.1 good.2 safeIndex allocated
    have impossible := congrArg Prod.fst (ran.symm.trans failed)
    cases impossible

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
