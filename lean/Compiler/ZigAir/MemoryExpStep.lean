/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryExpWords
import Compiler.ZigAir.MemoryEffects

/-! One ordered exponentiation iteration, including every failed write's
preceding effects. Distinct allocation identities frame the three scratch
words; readable slots are not assumed to be writable. -/
namespace Compiler.ZigAir.MemoryExp
open Memory MemoryAir

def Locals (env : Env) (baseSlot exponentSlot resultSlot : Address) : Prop :=
  env 2 = some (slot baseSlot) ∧ env 5 = some (slot exponentSlot) ∧ env 8 = some (slot resultSlot)

def Reads (state : State) (baseSlot exponentSlot resultSlot : Address) (base exponent result : Word) : Prop :=
  load state (slot baseSlot) = .ok (number base) ∧
  load state (slot exponentSlot) = .ok (number exponent) ∧
  load state (slot resultSlot) = .ok (number result)

def Separate (baseSlot exponentSlot resultSlot : Address) : Prop :=
  baseSlot.allocation ≠ exponentSlot.allocation ∧ baseSlot.allocation ≠ resultSlot.allocation ∧
    exponentSlot.allocation ≠ resultSlot.allocation

abbrev Effect := Except Fault Unit × State

def finishWrite (state : State) : Except Fault State → Effect
  | .error fault => (.error fault, state)
  | .ok after => (.ok (), after)

def halve (state : State) (exponentSlot : Address) (exponent : Word) : Effect :=
  finishWrite state (store state (slot exponentSlot) (number (exponent >>> 1)))

def afterSquare (state : State) (exponentSlot : Address) (exponent : Word) : Except Fault State → Effect
  | .error fault => (.error fault, state)
  | .ok after => halve after exponentSlot exponent

def square (state : State) (baseSlot exponentSlot : Address) (base exponent : Word) : Effect :=
  afterSquare state exponentSlot exponent (store state (slot baseSlot) (number (base * base)))

def afterResult (state : State) (baseSlot exponentSlot : Address) (base exponent : Word) : Except Fault State → Effect
  | .error fault => (.error fault, state)
  | .ok after => square after baseSlot exponentSlot base exponent

def step (state : State) (baseSlot exponentSlot resultSlot : Address) (base exponent result : Word) : Effect :=
  if exponent &&& 1 ≠ 0 then
    afterResult state baseSlot exponentSlot base exponent (store state (slot resultSlot) (number (result * base)))
  else square state baseSlot exponentSlot base exponent

def select (state : State) (resultSlot : Address) (base exponent result : Word) : Effect :=
  if exponent &&& 1 ≠ 0 then finishWrite state (store state (slot resultSlot) (number (result * base)))
  else (.ok (), state)

def afterSelect (baseSlot exponentSlot : Address) (base exponent : Word) : Effect → Effect
  | (.error fault, after) => (.error fault, after)
  | (.ok (), after) => square after baseSlot exponentSlot base exponent

theorem step_select (state : State) (baseSlot exponentSlot resultSlot : Address) (base exponent result : Word) :
    step state baseSlot exponentSlot resultSlot base exponent result =
      afterSelect baseSlot exponentSlot base exponent (select state resultSlot base exponent result) := by
  unfold step select
  split
  · cases store state (slot resultSlot) (number (result * base)) <;> rfl
  · rfl

theorem slot_frame (state after : State) (written read : Address) (value : Word)
    (stored : store state (slot written) (number value) = .ok after)
    (apart : read.allocation ≠ written.allocation) :
    load after (slot read) = load state (slot read) :=
  load_other_after_store state true false wordType written (number value) after
    true false wordType read stored apart

theorem finishWrite_success (state after : State) (result : Except Fault State)
    (success : finishWrite state result = (.ok (), after)) : result = .ok after := by
  cases result <;> simp_all [finishWrite]

theorem afterSquare_success (state after : State) (exponentSlot : Address) (exponent : Word)
    (result : Except Fault State) (success : afterSquare state exponentSlot exponent result = (.ok (), after)) :
    ∃ middle, result = .ok middle ∧ halve middle exponentSlot exponent = (.ok (), after) := by
  cases result with
  | error fault => simp [afterSquare] at success
  | ok middle => exact ⟨middle, rfl, success⟩

theorem afterResult_success (state after : State) (baseSlot exponentSlot : Address) (base exponent : Word)
    (result : Except Fault State) (success : afterResult state baseSlot exponentSlot base exponent result = (.ok (), after)) :
    ∃ middle, result = .ok middle ∧ square middle baseSlot exponentSlot base exponent = (.ok (), after) := by
  cases result with
  | error fault => simp [afterResult] at success
  | ok middle => exact ⟨middle, rfl, success⟩

theorem slot_readback (state after : State) (address : Address) (value : Word)
    (stored : store state (slot address) (number value) = .ok after) :
    load after (slot address) = .ok (number value) :=
  load_after_store state (slot address) (number value) after stored

theorem select_reads (state after : State) (baseSlot exponentSlot resultSlot : Address)
    (base exponent result : Word) (reads : Reads state baseSlot exponentSlot resultSlot base exponent result)
    (separate : Separate baseSlot exponentSlot resultSlot)
    (success : select state resultSlot base exponent result = (.ok (), after)) :
    Reads after baseSlot exponentSlot resultSlot base exponent (nextResult base exponent result) := by
  by_cases odd : exponent &&& 1 ≠ 0
  · rw [select, if_pos odd] at success
    have stored := finishWrite_success state after _ success
    rw [nextResult, if_pos odd]
    exact ⟨(slot_frame state after resultSlot baseSlot _ stored separate.2.1).trans reads.1,
      (slot_frame state after resultSlot exponentSlot _ stored separate.2.2).trans reads.2.1,
      slot_readback state after resultSlot _ stored⟩
  · rw [select, if_neg odd] at success
    have same : state = after := congrArg Prod.snd success
    subst after
    simpa only [nextResult, if_neg odd] using reads

theorem halve_reads (state after : State) (baseSlot exponentSlot resultSlot : Address)
    (base exponent result : Word) (reads : Reads state baseSlot exponentSlot resultSlot base exponent result)
    (separate : Separate baseSlot exponentSlot resultSlot)
    (success : halve state exponentSlot exponent = (.ok (), after)) :
    Reads after baseSlot exponentSlot resultSlot base (exponent >>> 1) result := by
  have stored := finishWrite_success state after _ success
  exact ⟨(slot_frame state after exponentSlot baseSlot _ stored separate.1).trans reads.1,
    slot_readback state after exponentSlot _ stored,
    (slot_frame state after exponentSlot resultSlot _ stored separate.2.2.symm).trans reads.2.2⟩

theorem square_reads (state after : State) (baseSlot exponentSlot resultSlot : Address)
    (base exponent result : Word) (reads : Reads state baseSlot exponentSlot resultSlot base exponent result)
    (separate : Separate baseSlot exponentSlot resultSlot)
    (success : square state baseSlot exponentSlot base exponent = (.ok (), after)) :
    Reads after baseSlot exponentSlot resultSlot (base * base) (exponent >>> 1) result := by
  obtain ⟨next, stored, halved⟩ := afterSquare_success state after exponentSlot exponent _ success
  have nextReads : Reads next baseSlot exponentSlot resultSlot (base * base) exponent result :=
    ⟨slot_readback state next baseSlot _ stored,
      (slot_frame state next baseSlot exponentSlot _ stored separate.1.symm).trans reads.2.1,
      (slot_frame state next baseSlot resultSlot _ stored separate.2.1.symm).trans reads.2.2⟩
  exact halve_reads next after baseSlot exponentSlot resultSlot _ exponent result nextReads separate halved

theorem step_reads (state after : State) (baseSlot exponentSlot resultSlot : Address)
    (base exponent result : Word) (reads : Reads state baseSlot exponentSlot resultSlot base exponent result)
    (separate : Separate baseSlot exponentSlot resultSlot)
    (success : step state baseSlot exponentSlot resultSlot base exponent result = (.ok (), after)) :
    Reads after baseSlot exponentSlot resultSlot (base * base) (exponent >>> 1) (nextResult base exponent result) := by
  by_cases odd : exponent &&& 1 ≠ 0
  · rw [step, if_pos odd] at success
    obtain ⟨next, stored, squared⟩ := afterResult_success state after baseSlot exponentSlot base exponent _ success
    have nextReads : Reads next baseSlot exponentSlot resultSlot base exponent (result * base) :=
      ⟨(slot_frame state next resultSlot baseSlot _ stored separate.2.1).trans reads.1,
        (slot_frame state next resultSlot exponentSlot _ stored separate.2.2).trans reads.2.1,
        slot_readback state next resultSlot _ stored⟩
    rw [nextResult, if_pos odd]
    exact square_reads next after baseSlot exponentSlot resultSlot base exponent (result * base) nextReads separate squared
  · rw [step, if_neg odd] at success
    rw [nextResult, if_neg odd]
    exact square_reads state after baseSlot exponentSlot resultSlot base exponent result reads separate success

end Compiler.ZigAir.MemoryExp
