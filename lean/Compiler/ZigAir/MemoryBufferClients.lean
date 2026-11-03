/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryPointers
import Compiler.ZigAir.MemoryAirLaws
import Compiler.ZigAir.GeneratedMemoryCells

/-! A functional specification of the captured two-write buffer function.
Preparation and write failures remain explicit, including the first write's
effects when the second write fails. This is an AIR-model result, not a proof
that Zig's source/native memory requirements have been discharged. -/
namespace Compiler.ZigAir.MemoryBufferClients
open Memory MemoryAir GeneratedMemory

private abbrev word : Ty := .scalar (.int false 32)
private abbrev pointer (many : Bool) (address : Address) : Value :=
  .pointer (.pointer true many word) address
private abbrev arguments (address : Address) (indexValue : Value) (first second : Scalar.Value) : List Value :=
  [pointer true address, indexValue, .scalar first, .scalar second]

/-- A checked pair of writes, returning the value selected by aliasing. It
describes all primitive failures and final states, without assuming a successful
complete run or reading the result back as part of the specification. -/
def bufferAliasEffects (state : State) (address : Address) (index : Nat) (first second : Scalar.Value) :
    Control.Outcome Value Fault State :=
  match pointerCast state (.pointer true false word) (pointer true address) with
  | .error fault => .fault fault state
  | .ok left =>
    match offsetPointer state false (pointer true address) index with
    | .error fault => .fault fault state
    | .ok moved =>
      match pointerCast state (.pointer true false word) moved with
      | .error fault => .fault fault state
      | .ok right =>
        match store state left (.scalar first) with
        | .error fault => .fault fault state
        | .ok middle =>
          match store middle right (.scalar second) with
          | .error fault => .fault fault middle
          | .ok after => .returned (.scalar (if index = 0 then second else first)) after

def bufferAliasSpec (state : State) (address : Address) (index : Nat) (first second : Scalar.Value) :
    Except Fault Value × State :=
  match bufferAliasEffects state address index first second with
  | .returned value after => (.ok value, cleanup state.nextId after)
  | .fault fault after => (.error fault, cleanup state.nextId after)
  | .jumped _ _ _ after => (.error .malformed, cleanup state.nextId after)

private theorem returned_typed (state : State) (address : Address) (index : Nat) (first second : Scalar.Value)
    (value : Value) (after : State) (firstTyped : (Value.scalar first).hasType word = true)
    (secondTyped : (Value.scalar second).hasType word = true)
    (returned : bufferAliasEffects state address index first second = .returned value after) :
    value.hasType word = true := by
  unfold bufferAliasEffects at returned
  repeat' first | contradiction | split at returned
  all_goals cases returned <;> assumption

private theorem pointer_typed (many : Bool) (address : Address) :
    (pointer many address).hasType (.pointer true many word) = true := by
  cases many <;> rfl

private theorem pointer_valid (many : Bool) (address : Address) :
    (pointer many address).valid = true := rfl

-- These equations simplify applied instructions without unfolding the entire
-- evaluator through function-valued arguments.
attribute [local simp] Code.eval_bind Code.eval_ret Prim.eval_argument Prim.eval_cast
  Prim.eval_offset Prim.eval_store Prim.eval_load Ref.eval_local Ref.natural_eq
  Control.Env.set pointer_typed pointer_valid

theorem buffer_alias_body (state : State) (address : Address) (index : Nat) (indexValue : Value) (first second : Scalar.Value)
    (indexTyped : indexValue.hasType (.scalar (.int false 64)) = true)
    (decoded : (Ref.constant indexValue).natural (fun _ => none) = .ok index)
    (firstTyped : (Value.scalar first).hasType word = true)
    (secondTyped : (Value.scalar second).hasType word = true) :
    fn_buffer_alias.body.eval semantics (arguments address indexValue first second) (fun _ => none) state =
      bufferAliasEffects state address index first second := by
  have indexValid := value_valid_of_hasType _ _ indexTyped
  simp only [Ref.natural_eq, Ref.eval_constant, indexValid, ↓reduceIte] at decoded
  have firstValid := value_valid_of_hasType _ _ firstTyped
  have secondValid := value_valid_of_hasType _ _ secondTyped
  have unitTyped : (Value.scalar .unit).hasType (.scalar .unit) = true := rfl
  cases leftCast : pointerCast state (.pointer true false word) (pointer true address) with
  | error fault =>
    simp [fn_buffer_alias, arguments, indexTyped, firstTyped, secondTyped,
      leftCast, bufferAliasEffects, bind, Except.bind]
  | ok left =>
    have leftAddress := pointerCast_address state _ true true word address left leftCast
    subst left
    cases moved : offsetPointer state false (pointer true address) index with
    | error fault =>
      simp [fn_buffer_alias, arguments, indexTyped, firstTyped, secondTyped,
        indexValid, decoded, leftCast, moved, bufferAliasEffects, bind, Except.bind]
    | ok advanced =>
      rcases offsetPointer_add_address state true word address index advanced moved with ⟨layout, shaped, _, position⟩
      have shape : layout = ⟨4, 4⟩ := by simpa [word, Ty.layout] using shaped.symm
      subst layout
      subst advanced
      cases rightCast : pointerCast state (.pointer true false word)
          (pointer true { address with offset := address.offset + index * 4 }) with
      | error fault =>
        simp [fn_buffer_alias, arguments, indexTyped, firstTyped, secondTyped,
          indexValid, decoded, leftCast, moved, rightCast, bufferAliasEffects, bind, Except.bind]
      | ok right =>
        have rightAddress := pointerCast_address state _ true true word _ right rightCast
        subst right
        cases firstWrite : store state (pointer false address) (.scalar first) with
        | error fault =>
          simp [fn_buffer_alias, arguments, indexTyped, firstTyped, secondTyped,
            indexValid, decoded, firstValid, leftCast, moved, rightCast, firstWrite,
            bufferAliasEffects, bind, Except.bind]
        | ok middle =>
          cases secondWrite : store middle (pointer false { address with offset := address.offset + index * 4 })
              (.scalar second) with
          | error fault =>
            simp [fn_buffer_alias, arguments, indexTyped, firstTyped, secondTyped,
              indexValid, decoded, firstValid, secondValid, unitTyped,
              leftCast, moved, rightCast, firstWrite, secondWrite, bufferAliasEffects, bind, Except.bind]
          | ok after =>
            have readback := load_after_two_scalar_stores state middle after (.int false 32)
              address.allocation address.offset (address.offset + index * 4) first second firstWrite secondWrite
            have alias : address.offset = address.offset + index * 4 ↔ index = 0 := by omega
            simp only [alias] at readback
            have chosenTyped : (Value.scalar (if index = 0 then second else first)).hasType word = true := by
              split
              · exact secondTyped
              · exact firstTyped
            have chosenValid : (Value.scalar (if index = 0 then second else first)).valid = true := by
              split
              · exact secondValid
              · exact firstValid
            simp [fn_buffer_alias, arguments, indexTyped, firstTyped, secondTyped,
              indexValid, decoded, firstValid, secondValid, unitTyped, chosenTyped, chosenValid,
              leftCast, moved, rightCast, firstWrite, secondWrite, readback, bufferAliasEffects, bind, Except.bind]

theorem buffer_alias_run_decoded (state : State) (address : Address) (index : Nat) (indexValue : Value) (first second : Scalar.Value)
    (initial : state.valid = true)
    (indexTyped : indexValue.hasType (.scalar (.int false 64)) = true)
    (decoded : (Ref.constant indexValue).natural (fun _ => none) = .ok index)
    (firstTyped : (Value.scalar first).hasType word = true)
    (secondTyped : (Value.scalar second).hasType word = true) :
    fn_buffer_alias.run (arguments address indexValue first second) state =
      bufferAliasSpec state address index first second := by
  have inputsTyped : ((arguments address indexValue first second).zip fn_buffer_alias.parameters).all
      (fun (value, type) => value.hasType type) = true := by
    simp [arguments, fn_buffer_alias, indexTyped, firstTyped, secondTyped]
  rw [Program.run_of_valid_inputs _ _ _ initial rfl inputsTyped,
    buffer_alias_body state address index _ first second indexTyped decoded firstTyped secondTyped]
  unfold bufferAliasSpec
  cases outcome : bufferAliasEffects state address index first second with
  | returned value after =>
    have typed := returned_typed state address index first second value after firstTyped secondTyped outcome
    simp only [fn_buffer_alias, typed, ↓reduceIte]
  | fault => rfl
  | jumped => rfl

/-- The complete invocation specification for every valid heap, usize index and
typed pair of words. There is no successful-operation or decoded-input premise. -/
theorem buffer_alias_run (state : State) (address : Address) (index : Nat) (first second : Scalar.Value)
    (initial : state.valid = true)
    (indexTyped : (Value.scalar (.int false 64 index)).hasType (.scalar (.int false 64)) = true)
    (firstTyped : (Value.scalar first).hasType word = true)
    (secondTyped : (Value.scalar second).hasType word = true) :
    fn_buffer_alias.run (arguments address (.scalar (.int false 64 index)) first second) state =
      bufferAliasSpec state address index first second := by
  have indexValid := value_valid_of_hasType _ _ indexTyped
  have decoded := Ref.natural_of_eval (.constant (.scalar (.int false 64 index))) (fun _ => none) (index : Int)
    (Ref.eval_constant_of_valid _ _ indexValid)
  exact buffer_alias_run_decoded state address index _ first second initial indexTyped decoded firstTyped secondTyped

end Compiler.ZigAir.MemoryBufferClients
