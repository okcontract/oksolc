/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Check.Axioms
import Contract.Primitives
import Contract.Yul.Expression
import Contract.Evm.Guarded
import Contract.Evm.Machine
import Contract.Evm.World
import Compiler.Validation.Normalize
import Compiler.Validation.Solidity

/-! Soundness-proved bytecode validator and universal artifact certification over
`Contract.Evm.Machine` and `Contract.Evm.World`.

1. Proves the concrete universal deployment and runtime theorems
   (`previewDeployment_certified` and `publicPreviewIdentity_certified`) for
   `Identity.identity(uint256)` (`examples/verification/{Function.sol,response.json}`)
   over ALL `World`, `Transaction`, `Context`, `Input` (`calldata.length < 2^64`),
   and execution gas budgets `gas : Nat`, plus `corruptedPreviewIdentity_rejected`
   proving the negative control (`RETURN -> REVERT`) violates the runtime spec.
2. Provides `validateContractArtifact` + `validateContractArtifact_sound`
   comparing compiled creation/runtime bytecode and selectors directly against
   `Solidity.ContractSpec` parsed in-kernel from `.sol` source, establishing
   `spec.wellFormed = true`, Cancun EIP-3860/170/3541 bounds, Keccak-256 selector
   soundness, and concrete `Contract.Evm.run` behavioral equivalence with
   `Solidity.evalDeployment` and `Solidity.evalRuntime` on every checked probe. -/
namespace Compiler.Validation.Bytecode

open Contract
open Contract.Yul
open Contract.Evm

def previewCreationBytes : List UInt8 :=
  [0x60, 0x80, 0x80, 0x60, 0x40, 0x52, 0x34, 0x60, 0x13, 0x57,
   0x60, 0x40, 0x90, 0x81, 0x60, 0x18, 0x82, 0x39, 0xf3, 0x5b,
   0x5f, 0x80, 0xfd, 0xfe,
   0x60, 0x80, 0x80, 0x60, 0x40, 0x52, 0x60, 0x04, 0x36, 0x10,
   0x15, 0x60, 0x11, 0x57, 0x5f, 0x80, 0xfd, 0x5b, 0x5f, 0x35,
   0x60, 0xe0, 0x1c, 0x63, 0xac, 0x37, 0xee, 0xbb, 0x14, 0x60,
   0x23, 0x57, 0x5f, 0x80, 0xfd, 0x5b, 0x34, 0x60, 0x3c, 0x57,
   0x60, 0x20, 0x36, 0x60, 0x03, 0x19, 0x01, 0x12, 0x60, 0x3c,
   0x57, 0x60, 0x20, 0x90, 0x60, 0x04, 0x35, 0x81, 0x52, 0xf3,
   0x5b, 0x5f, 0x80, 0xfd]

def previewRuntimeBytes : List UInt8 :=
  [0x60, 0x80, 0x80, 0x60, 0x40, 0x52, 0x60, 0x04, 0x36, 0x10,
   0x15, 0x60, 0x11, 0x57, 0x5f, 0x80, 0xfd, 0x5b, 0x5f, 0x35,
   0x60, 0xe0, 0x1c, 0x63, 0xac, 0x37, 0xee, 0xbb, 0x14, 0x60,
   0x23, 0x57, 0x5f, 0x80, 0xfd, 0x5b, 0x34, 0x60, 0x3c, 0x57,
   0x60, 0x20, 0x36, 0x60, 0x03, 0x19, 0x01, 0x12, 0x60, 0x3c,
   0x57, 0x60, 0x20, 0x90, 0x60, 0x04, 0x35, 0x81, 0x52, 0xf3,
   0x5b, 0x5f, 0x80, 0xfd]

def corruptedRuntimeBytes : List UInt8 :=
  [0x60, 0x80, 0x80, 0x60, 0x40, 0x52, 0x60, 0x04, 0x36, 0x10,
   0x15, 0x60, 0x11, 0x57, 0x5f, 0x80, 0xfd, 0x5b, 0x5f, 0x35,
   0x60, 0xe0, 0x1c, 0x63, 0xac, 0x37, 0xee, 0xbb, 0x14, 0x60,
   0x23, 0x57, 0x5f, 0x80, 0xfd, 0x5b, 0x34, 0x60, 0x3c, 0x57,
   0x60, 0x20, 0x36, 0x60, 0x03, 0x19, 0x01, 0x12, 0x60, 0x3c,
   0x57, 0x60, 0x20, 0x90, 0x60, 0x04, 0x35, 0x81, 0x52, 0xfd,
   0x5b, 0x5f, 0x80, 0xfd]

def previewSource : String :=
  "// SPDX-License-Identifier: GPL-3.0\npragma solidity ^0.8.0;\n\ncontract Identity {\n    function identity(uint256 x) external pure returns (uint256) {\n        return x;\n    }\n}\n"

set_option maxRecDepth 200000 in
/-- Kernel proof that `Solidity.parseSource` parses `previewSource` to `Identity.identity(uint256)`
and `Contract.Export.Keccak` derives exact selector `0xac37eebb`. -/
theorem previewSource_parsed_selector :
    (match Solidity.parseSource previewSource with
     | some spec =>
       spec.name == "Identity" &&
       spec.wellFormed &&
       match spec.functions with
       | [fn] =>
         fn.signature == "identity(uint256)" &&
         fn.selectorBytes == [0xac, 0x37, 0xee, 0xbb] &&
         fn.selectorWord == 0xac37eebb#256
       | _ => false
     | none => false) = true := by decide

private theorem jumpDestinations_previewCreation :
    jumpDestinations previewCreationBytes = [0x13, 0x29, 0x3b, 0x54] := by decide

private theorem jumpDestinations_previewRuntime :
    jumpDestinations previewRuntimeBytes = [0x11, 0x23, 0x3c] := by decide

private theorem previewCreation_slice :
    padded previewCreationBytes 0x18 0x40 = previewRuntimeBytes := by decide

private theorem step_word_at (code : List UInt8) (input : Input) (env : Environment)
    (pc : Nat) (stk stk' : List Word) (mem : Memory) (mw : Nat)
    (storage : Slots) (warm : Word → Bool) (refund : Int)
    (op : WordOp) (width cost : Nat)
    (hd : decodeWordOpAt code pc = some (op, width))
    (hop : ∀ ctx, op.evalStack ctx stk = some stk')
    (hcost : op.gasCost stk = cost) :
    step code input env
      { machine := { pc := pc, stack := stk, memory := mem, memoryWords := mw },
        storage := storage, warm := warm, refund := refund } =
      .next cost 0
        { machine := { pc := pc + width, stack := stk', memory := mem, memoryWords := mw },
          storage := storage, warm := warm, refund := refund } := by
  have h := decodeWordOpAt_step_append code [] pc op width input env
    { machine := { pc := pc, stack := stk, memory := mem, memoryWords := mw },
      storage := storage, warm := warm, refund := refund }
    stk' rfl hd (hop env.ctx)
  simpa [List.append_nil, hcost] using h

private theorem step_callvalue_at (code : List UInt8) (input : Input) (env : Environment)
    (pc : Nat) (stk : List Word) (mem : Memory) (mw : Nat)
    (storage : Slots) (warm : Word → Bool) (refund : Int)
    (hd : decodeWordOp code pc (code[pc]?.getD 0) = none)
    (hop : (code[pc]?.getD 0).toNat = 0x34)
    (hlen : stk.length < 1024) :
    step code input env
      { machine := { pc := pc, stack := stk, memory := mem, memoryWords := mw },
        storage := storage, warm := warm, refund := refund } =
      .next 2 0
        { machine := { pc := pc + 1, stack := input.value :: stk, memory := mem, memoryWords := mw },
          storage := storage, warm := warm, refund := refund } := by
  unfold step push
  dsimp only
  rw [hd, hop]
  simp [hlen]

private theorem step_calldatasize_at (code : List UInt8) (input : Input) (env : Environment)
    (pc : Nat) (stk : List Word) (mem : Memory) (mw : Nat)
    (storage : Slots) (warm : Word → Bool) (refund : Int)
    (hd : decodeWordOp code pc (code[pc]?.getD 0) = none)
    (hop : (code[pc]?.getD 0).toNat = 0x36)
    (hlen : stk.length < 1024) :
    step code input env
      { machine := { pc := pc, stack := stk, memory := mem, memoryWords := mw },
        storage := storage, warm := warm, refund := refund } =
      .next 2 0
        { machine := { pc := pc + 1, stack := BitVec.ofNat 256 input.calldata.length :: stk,
                       memory := mem, memoryWords := mw },
          storage := storage, warm := warm, refund := refund } := by
  unfold step push
  dsimp only
  rw [hd, hop]
  simp [hlen]

private theorem step_jumpdest_at (code : List UInt8) (input : Input) (env : Environment)
    (pc : Nat) (stk : List Word) (mem : Memory) (mw : Nat)
    (storage : Slots) (warm : Word → Bool) (refund : Int)
    (hd : decodeWordOp code pc (code[pc]?.getD 0) = none)
    (hop : (code[pc]?.getD 0).toNat = 0x5b) :
    step code input env
      { machine := { pc := pc, stack := stk, memory := mem, memoryWords := mw },
        storage := storage, warm := warm, refund := refund } =
      .next 1 0
        { machine := { pc := pc + 1, stack := stk, memory := mem, memoryWords := mw },
          storage := storage, warm := warm, refund := refund } := by
  unfold step
  dsimp only
  rw [hd, hop]

private theorem step_swap1_at (code : List UInt8) (input : Input) (env : Environment)
    (pc : Nat) (a b : Word) (rest : List Word) (mem : Memory) (mw : Nat)
    (storage : Slots) (warm : Word → Bool) (refund : Int)
    (hd : decodeWordOp code pc (code[pc]?.getD 0) = some (.swap 0)) :
    step code input env
      { machine := { pc := pc, stack := a :: b :: rest, memory := mem, memoryWords := mw },
        storage := storage, warm := warm, refund := refund } =
      .next 3 0
        { machine := { pc := pc + 1, stack := b :: a :: rest, memory := mem, memoryWords := mw },
          storage := storage, warm := warm, refund := refund } := by
  unfold step
  dsimp only
  rw [hd]
  rfl

private theorem step_jumpi_zero_at (code : List UInt8) (input : Input) (env : Environment)
    (pc : Nat) (dest : Word) (rest : List Word) (mem : Memory) (mw : Nat)
    (storage : Slots) (warm : Word → Bool) (refund : Int)
    (hd : decodeWordOp code pc (code[pc]?.getD 0) = none)
    (hop : (code[pc]?.getD 0).toNat = 0x57) :
    step code input env
      { machine := { pc := pc, stack := dest :: 0#256 :: rest, memory := mem, memoryWords := mw },
        storage := storage, warm := warm, refund := refund } =
      .next 10 0
        { machine := { pc := pc + 1, stack := rest, memory := mem, memoryWords := mw },
          storage := storage, warm := warm, refund := refund } := by
  unfold step
  dsimp only
  rw [hd]
  simp [hop]

private theorem step_jumpi_nonzero_at (code : List UInt8) (input : Input) (env : Environment)
    (pc : Nat) (dest cond : Word) (rest : List Word) (mem : Memory) (mw : Nat)
    (storage : Slots) (warm : Word → Bool) (refund : Int)
    (hd : decodeWordOp code pc (code[pc]?.getD 0) = none)
    (hop : (code[pc]?.getD 0).toNat = 0x57)
    (hcond : cond ≠ 0#256)
    (hdest : dest.toNat ∈ jumpDestinations code) :
    step code input env
      { machine := { pc := pc, stack := dest :: cond :: rest, memory := mem, memoryWords := mw },
        storage := storage, warm := warm, refund := refund } =
      .next 10 0
        { machine := { pc := dest.toNat, stack := rest, memory := mem, memoryWords := mw },
          storage := storage, warm := warm, refund := refund } := by
  unfold step
  dsimp only
  rw [hd]
  simp [hop, hcond, hdest]

private theorem step_mstore_at (code : List UInt8) (input : Input) (env : Environment)
    (pc : Nat) (off val : Word) (rest : List Word) (mem : Memory) (mw : Nat)
    (storage : Slots) (warm : Word → Bool) (refund : Int)
    (hd : decodeWordOp code pc (code[pc]?.getD 0) = none)
    (hop : (code[pc]?.getD 0).toNat = 0x52) :
    step code input env
      { machine := { pc := pc, stack := off :: val :: rest, memory := mem, memoryWords := mw },
        storage := storage, warm := warm, refund := refund } =
      .next (3 + expansionCost mw off.toNat 32) 0
        { machine := { pc := pc + 1, stack := rest,
                       memory := mem.write off.toNat (wordBytes val),
                       memoryWords := expandedWords mw off.toNat 32 },
          storage := storage, warm := warm, refund := refund } := by
  unfold step
  dsimp only
  rw [hd, hop]

private theorem step_calldataload_at (code : List UInt8) (input : Input) (env : Environment)
    (pc : Nat) (off : Word) (rest : List Word) (mem : Memory) (mw : Nat)
    (storage : Slots) (warm : Word → Bool) (refund : Int)
    (hd : decodeWordOp code pc (code[pc]?.getD 0) = none)
    (hop : (code[pc]?.getD 0).toNat = 0x35) :
    step code input env
      { machine := { pc := pc, stack := off :: rest, memory := mem, memoryWords := mw },
        storage := storage, warm := warm, refund := refund } =
      .next 3 0
        { machine := { pc := pc + 1, stack := loadWord input.calldata off.toNat :: rest,
                       memory := mem, memoryWords := mw },
          storage := storage, warm := warm, refund := refund } := by
  unfold step
  dsimp only
  rw [hd, hop]

private theorem step_revert_zero_at (code : List UInt8) (input : Input) (env : Environment)
    (pc : Nat) (rest : List Word) (mem : Memory) (mw : Nat)
    (storage : Slots) (warm : Word → Bool) (refund : Int)
    (hd : decodeWordOp code pc (code[pc]?.getD 0) = none)
    (hop : code[pc]?.getD 0 = 0xfd) :
    step code input env
      { machine := { pc := pc, stack := 0#256 :: 0#256 :: rest, memory := mem, memoryWords := mw },
        storage := storage, warm := warm, refund := refund } =
      .halt 0 ⟨.reverted [],
        { machine := { pc := pc, stack := 0#256 :: 0#256 :: rest, memory := mem,
                       memoryWords := expandedWords mw 0 0 },
          storage := storage, warm := warm, refund := refund }⟩ := by
  unfold step
  dsimp only
  rw [hd, hop]
  have hn : (0xfd : UInt8).toNat = 0xfd := rfl
  have h0 : (0#256).toNat = 0 := by decide
  have hexp : expansionCost mw 0 0 = 0 := by
    simp [expansionCost, expandedWords]
  have hread : mem.read 0 0 = [] := by simp [Memory.read]
  simp [hn, h0, hexp, hread]

private theorem guarded_run_next {σ α : Type} (f : σ → Guarded.Step σ α)
    (fuel : Nat) (s s' : σ) (cost extra : Nat)
    (hstep : f s = .next cost extra s') :
    Guarded.run f (fuel + 1) s =
      (Guarded.run f fuel s').charge cost extra := by
  simp [Guarded.run, hstep]

private theorem guarded_run_halt {σ α : Type} (f : σ → Guarded.Step σ α)
    (fuel : Nat) (s : σ) (cost : Nat) (res : α)
    (hstep : f s = .halt cost res) :
    Guarded.run f (fuel + 1) s = .finished cost cost res := by
  simp [Guarded.run, hstep]

private theorem trace_charge_zero {α : Type} (cost used : Nat) (res : α) :
    Guarded.Trace.charge cost 0 (Guarded.Trace.finished used used res) =
      Guarded.Trace.finished (cost + used) (cost + used) res := by
  simp [Guarded.Trace.charge]

/-- Universal creation-bytecode theorem for `previewCreationBytes`:
- When `input.value = 0`, `Contract.Evm.run` halts with `Halt.returned previewRuntimeBytes`,
  preserving storage, warm slots, and refunds, using exact execution gas `69`.
- When `input.value ≠ 0`, `Contract.Evm.run` halts with `Halt.reverted []`,
  using exact execution gas `42`. -/
theorem previewCreation_run_exact (input : Input) (env : Environment)
    (storage : Slots) (warm : Word → Bool) (refund : Int) :
    let init : State := { storage := storage, warm := warm, refund := refund }
    if input.value = 0#256 then
      ∃ m',
        Contract.Evm.run previewCreationBytes input env 20 init =
          .finished 69 69 ⟨.returned previewRuntimeBytes,
            { machine := m', storage := storage, warm := warm, refund := refund }⟩
    else
      ∃ m',
        Contract.Evm.run previewCreationBytes input env 20 init =
          .finished 42 42 ⟨.reverted [],
            { machine := m', storage := storage, warm := warm, refund := refund }⟩ := by
  dsimp only
  let mem0 : Memory := fun _ => 0
  let mem1 : Memory := Memory.write mem0 64 (wordBytes 128#256)
  have hs0 : step previewCreationBytes input env
      { machine := { pc := 0, stack := [], memory := mem0, memoryWords := 0 },
        storage := storage, warm := warm, refund := refund } =
      .next 3 0
        { machine := { pc := 2, stack := [128#256], memory := mem0, memoryWords := 0 },
          storage := storage, warm := warm, refund := refund } :=
    step_word_at _ _ _ 0 [] [128#256] mem0 0 storage warm refund (.push 1 128#256) 2 3 (by decide) (fun _ => rfl) rfl
  have hs1 : step previewCreationBytes input env
      { machine := { pc := 2, stack := [128#256], memory := mem0, memoryWords := 0 },
        storage := storage, warm := warm, refund := refund } =
      .next 3 0
        { machine := { pc := 3, stack := [128#256, 128#256], memory := mem0, memoryWords := 0 },
          storage := storage, warm := warm, refund := refund } :=
    step_word_at _ _ _ 2 [128#256] [128#256, 128#256] mem0 0 storage warm refund (.dup 0) 1 3 (by decide) (fun _ => rfl) rfl
  have hs2 : step previewCreationBytes input env
      { machine := { pc := 3, stack := [128#256, 128#256], memory := mem0, memoryWords := 0 },
        storage := storage, warm := warm, refund := refund } =
      .next 3 0
        { machine := { pc := 5, stack := [64#256, 128#256, 128#256], memory := mem0, memoryWords := 0 },
          storage := storage, warm := warm, refund := refund } :=
    step_word_at _ _ _ 3 [128#256, 128#256] [64#256, 128#256, 128#256] mem0 0 storage warm refund (.push 1 64#256) 2 3 (by decide) (fun _ => rfl) rfl
  have hs3 : step previewCreationBytes input env
      { machine := { pc := 5, stack := [64#256, 128#256, 128#256], memory := mem0, memoryWords := 0 },
        storage := storage, warm := warm, refund := refund } =
      .next 12 0
        { machine := { pc := 6, stack := [128#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } := by
    simpa [mem1, mem0, expansionCost, expandedWords, memoryCost] using
      step_mstore_at previewCreationBytes input env 5 64#256 128#256 [128#256] mem0 0 storage warm refund (by decide) (by decide)
  have hs4 : step previewCreationBytes input env
      { machine := { pc := 6, stack := [128#256], memory := mem1, memoryWords := 3 },
        storage := storage, warm := warm, refund := refund } =
      .next 2 0
        { machine := { pc := 7, stack := [input.value, 128#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } :=
    step_callvalue_at _ _ _ 6 [128#256] mem1 3 storage warm refund (by decide) (by decide) (by decide)
  have hs5 : step previewCreationBytes input env
      { machine := { pc := 7, stack := [input.value, 128#256], memory := mem1, memoryWords := 3 },
        storage := storage, warm := warm, refund := refund } =
      .next 3 0
        { machine := { pc := 9, stack := [19#256, input.value, 128#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } :=
    step_word_at _ _ _ 7 [input.value, 128#256] [19#256, input.value, 128#256] mem1 3 storage warm refund (.push 1 19#256) 2 3 (by decide) (fun _ => by simp [WordOp.evalStack]) rfl
  by_cases hval : input.value = 0#256
  · simp only [hval, ↓reduceIte]
    have hs6 : step previewCreationBytes input env
        { machine := { pc := 9, stack := [19#256, 0#256, 128#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } =
        .next 10 0
          { machine := { pc := 10, stack := [128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } :=
      step_jumpi_zero_at _ _ _ 9 19#256 [128#256] mem1 3 storage warm refund (by decide) (by decide)
    have hs7 : step previewCreationBytes input env
        { machine := { pc := 10, stack := [128#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } =
        .next 3 0
          { machine := { pc := 12, stack := [64#256, 128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } :=
      step_word_at _ _ _ 10 [128#256] [64#256, 128#256] mem1 3 storage warm refund (.push 1 64#256) 2 3 (by decide) (fun _ => rfl) rfl
    have hs8 : step previewCreationBytes input env
        { machine := { pc := 12, stack := [64#256, 128#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } =
        .next 3 0
          { machine := { pc := 13, stack := [128#256, 64#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } :=
      step_swap1_at _ _ _ 12 64#256 128#256 [] mem1 3 storage warm refund (by decide)
    have hs9 : step previewCreationBytes input env
        { machine := { pc := 13, stack := [128#256, 64#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } =
        .next 3 0
          { machine := { pc := 14, stack := [64#256, 128#256, 64#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } :=
      step_word_at _ _ _ 13 [128#256, 64#256] [64#256, 128#256, 64#256] mem1 3 storage warm refund (.dup 1) 1 3 (by decide) (fun _ => rfl) rfl
    have hs10 : step previewCreationBytes input env
        { machine := { pc := 14, stack := [64#256, 128#256, 64#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } =
        .next 3 0
          { machine := { pc := 16, stack := [24#256, 64#256, 128#256, 64#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } :=
      step_word_at _ _ _ 14 [64#256, 128#256, 64#256] [24#256, 64#256, 128#256, 64#256] mem1 3 storage warm refund (.push 1 24#256) 2 3 (by decide) (fun _ => rfl) rfl
    have hs11 : step previewCreationBytes input env
        { machine := { pc := 16, stack := [24#256, 64#256, 128#256, 64#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } =
        .next 3 0
          { machine := { pc := 17, stack := [128#256, 24#256, 64#256, 128#256, 64#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } :=
      step_word_at _ _ _ 16 [24#256, 64#256, 128#256, 64#256] [128#256, 24#256, 64#256, 128#256, 64#256] mem1 3 storage warm refund (.dup 2) 1 3 (by decide) (fun _ => rfl) rfl
    let mem2 : Memory := mem1.write 128 previewRuntimeBytes
    have hs12 : step previewCreationBytes input env
        { machine := { pc := 17, stack := [128#256, 24#256, 64#256, 128#256, 64#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } =
        .next 18 0
          { machine := { pc := 18, stack := [128#256, 64#256], memory := mem2, memoryWords := 6 },
            storage := storage, warm := warm, refund := refund } := by
      have hslice : padded previewCreationBytes 24 64 = previewRuntimeBytes := previewCreation_slice
      unfold step
      dsimp only [expansionCost, expandedWords, memoryCost, mem2]
      have hd : decodeWordOp previewCreationBytes 17 (previewCreationBytes[17]?.getD 0) = none := by decide
      have hop : (previewCreationBytes[17]?.getD 0).toNat = 0x39 := by decide
      rw [hd, hop]
      have h128 : (128#256).toNat = 128 := by decide
      have h24 : (24#256).toNat = 24 := by decide
      have h64 : (64#256).toNat = 64 := by decide
      rw [h128, h24, h64, hslice]
      rfl
    have hs13 : step previewCreationBytes input env
        { machine := { pc := 18, stack := [128#256, 64#256], memory := mem2, memoryWords := 6 },
          storage := storage, warm := warm, refund := refund } =
        .halt 0 ⟨.returned previewRuntimeBytes,
          { machine := { pc := 18, stack := [128#256, 64#256], memory := mem2, memoryWords := 6 },
            storage := storage, warm := warm, refund := refund }⟩ := by
      have hlen : previewRuntimeBytes.length = 64 := by decide
      have hrw := Memory.read_write_same mem1 128 previewRuntimeBytes
      have hread : mem2.read 128 64 = previewRuntimeBytes := by simpa [mem2, hlen] using hrw
      unfold step
      dsimp only [expansionCost, expandedWords, memoryCost]
      have hd : decodeWordOp previewCreationBytes 18 (previewCreationBytes[18]?.getD 0) = none := by decide
      have hop : previewCreationBytes[18]?.getD 0 = 0xf3 := by decide
      rw [hd, hop]
      have h128 : (128#256).toNat = 128 := by decide
      have h64 : (64#256).toNat = 64 := by decide
      rw [h128, h64, hread]
      rfl
    refine ⟨{ pc := 18, stack := [128#256, 64#256], memory := mem2, memoryWords := 6 }, ?_⟩
    unfold Contract.Evm.run
    rw [guarded_run_next _ 19 _ _ _ _ hs0,
        guarded_run_next _ 18 _ _ _ _ hs1,
        guarded_run_next _ 17 _ _ _ _ hs2,
        guarded_run_next _ 16 _ _ _ _ hs3,
        guarded_run_next _ 15 _ _ _ _ hs4,
        guarded_run_next _ 14 _ _ _ _ hs5]
    rw [hval]
    rw [guarded_run_next _ 13 _ _ _ _ hs6,
        guarded_run_next _ 12 _ _ _ _ hs7,
        guarded_run_next _ 11 _ _ _ _ hs8,
        guarded_run_next _ 10 _ _ _ _ hs9,
        guarded_run_next _ 9 _ _ _ _ hs10,
        guarded_run_next _ 8 _ _ _ _ hs11,
        guarded_run_next _ 7 _ _ _ _ hs12,
        guarded_run_halt _ 6 _ _ _ hs13]
    rfl
  · simp only [hval, ↓reduceIte]
    have hs6 : step previewCreationBytes input env
        { machine := { pc := 9, stack := [19#256, input.value, 128#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } =
        .next 10 0
          { machine := { pc := 19, stack := [128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } :=
      step_jumpi_nonzero_at _ _ _ 9 19#256 input.value [128#256] mem1 3 storage warm refund
        (by decide) (by decide) hval (by rw [jumpDestinations_previewCreation]; decide)
    have hs7 : step previewCreationBytes input env
        { machine := { pc := 19, stack := [128#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } =
        .next 1 0
          { machine := { pc := 20, stack := [128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } :=
      step_jumpdest_at _ _ _ 19 [128#256] mem1 3 storage warm refund (by decide) (by decide)
    have hs8 : step previewCreationBytes input env
        { machine := { pc := 20, stack := [128#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } =
        .next 2 0
          { machine := { pc := 21, stack := [0#256, 128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } :=
      step_word_at _ _ _ 20 [128#256] [0#256, 128#256] mem1 3 storage warm refund (.push 0 0#256) 1 2 (by decide) (fun _ => rfl) rfl
    have hs9 : step previewCreationBytes input env
        { machine := { pc := 21, stack := [0#256, 128#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } =
        .next 3 0
          { machine := { pc := 22, stack := [0#256, 0#256, 128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } :=
      step_word_at _ _ _ 21 [0#256, 128#256] [0#256, 0#256, 128#256] mem1 3 storage warm refund (.dup 0) 1 3 (by decide) (fun _ => rfl) rfl
    have hs10 : step previewCreationBytes input env
        { machine := { pc := 22, stack := [0#256, 0#256, 128#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } =
        .halt 0 ⟨.reverted [],
          { machine := { pc := 22, stack := [0#256, 0#256, 128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund }⟩ := by
      simpa [expandedWords] using
        step_revert_zero_at previewCreationBytes input env 22 [128#256] mem1 3 storage warm refund (by decide) (by decide)
    refine ⟨{ pc := 22, stack := [0#256, 0#256, 128#256], memory := mem1, memoryWords := 3 }, ?_⟩
    unfold Contract.Evm.run
    rw [guarded_run_next _ 19 _ _ _ _ hs0,
        guarded_run_next _ 18 _ _ _ _ hs1,
        guarded_run_next _ 17 _ _ _ _ hs2,
        guarded_run_next _ 16 _ _ _ _ hs3,
        guarded_run_next _ 15 _ _ _ _ hs4,
        guarded_run_next _ 14 _ _ _ _ hs5,
        guarded_run_next _ 13 _ _ _ _ hs6,
        guarded_run_next _ 12 _ _ _ _ hs7,
        guarded_run_next _ 11 _ _ _ _ hs8,
        guarded_run_next _ 10 _ _ _ _ hs9,
        guarded_run_halt _ 9 _ _ _ hs10]
    rfl

/-- World-level deployment certificate for `previewCreationBytes`:
For any fresh contract address `ctx.self`, caller with sufficient balance, and gas budget `gas`:
- If `input.value = 0`: deployment installs `previewRuntimeBytes` at `ctx.self` with nonce `1`
  whenever `69 + 200 * 64 ≤ gas` (`12869 ≤ gas`), and faults cleanly (rolling back world state)
  if gas is insufficient.
- If `input.value ≠ 0`: nonpayable constructor reverts cleanly (`42 ≤ gas`) or faults (`gas < 42`),
  rolling back `world` and `tx` in both cases. -/
theorem previewDeployment_certified (world : World) (tx : Transaction) (ctx : Context)
    (hfresh : Fresh world ctx.self) (input : Input) (gas : Nat)
    (hbal : input.value.toNat ≤ world.balances ctx.caller) :
    let frame := executeCreation previewCreationBytes world tx ctx input 20 gas
    if input.value = 0#256 then
      if 12869 ≤ gas then
        frame.status = .returned ∧
        frame.bytes = previewRuntimeBytes ∧
        frame.world.code ctx.self = previewRuntimeBytes ∧
        frame.world.nonces ctx.self = 1 ∧
        frame.gasRemaining = gas - 12869
      else
        frame.status = .exceptional ∧ frame.world = world
    else
      if 42 ≤ gas then
        frame.status = .reverted ∧ frame.bytes = [] ∧ frame.world = world
      else
        frame.status = .exceptional ∧ frame.world = world := by
  dsimp only
  have hlen_init : previewCreationBytes.length ≤ 49152 := by decide
  have hcan : canCreateAt world ctx.self = true := canCreateAt_of_fresh hfresh
  have hlen_rt : previewRuntimeBytes.length = 64 := by decide
  have hhead_rt : previewRuntimeBytes.head? ≠ some 0xef := by decide
  have hbal_prep : input.value.toNat ≤ (world.prepare ctx.self).balances ctx.caller := hbal
  unfold executeCreation
  simp only [hlen_init, hcan, decide_true, Bool.true_and, ↓reduceIte]
  have htr_some : ∃ staged, (world.prepare ctx.self).transfer ctx.caller ctx.self input.value = some staged := by
    unfold World.transfer
    simp only [hbal_prep, ↓reduceIte]
    split <;> exact ⟨_, rfl⟩
  rcases htr_some with ⟨staged, htr⟩
  rw [htr]
  dsimp only
  have hrun := previewCreation_run_exact input ⟨ctx, tx.original ctx.self, false⟩
    (staged.storage ctx.self) (tx.warm ctx.self) tx.refund
  by_cases hval : input.value = 0#256
  · simp only [hval, ↓reduceIte] at hrun ⊢
    rcases hrun with ⟨m', hrun_eq⟩
    have hmet := Guarded.metered_of_run
      (step previewCreationBytes input ⟨ctx, tx.original ctx.self, false⟩)
      20 (initialState staged tx ctx.self) 69 69
      ⟨.returned previewRuntimeBytes,
        { machine := m', storage := staged.storage ctx.self, warm := tx.warm ctx.self, refund := tx.refund }⟩
      gas hrun_eq
    unfold runMetered
    rw [hmet]
    have hstaged_eq : staged = world.prepare ctx.self := by
      unfold World.transfer at htr
      simp [hval] at htr
      exact htr.symm
    by_cases hgas12869 : 12869 ≤ gas
    · have hgas69 : 69 ≤ gas := by omega
      have hcond_ok : previewRuntimeBytes.length ≤ 24576 ∧
          previewRuntimeBytes.head? ≠ some 0xef ∧
          200 * previewRuntimeBytes.length ≤ gas - 69 := by
        refine ⟨by rw [hlen_rt]; omega, hhead_rt, by rw [hlen_rt]; omega⟩
      simp only [hgas12869, hgas69, ↓reduceIte, finishCreation]
      rw [if_pos hcond_ok]
      dsimp only
      refine ⟨rfl, rfl, ?_, ?_, by rw [hlen_rt]; omega⟩
      · simp [World.install]
      · rw [hstaged_eq]
        simp [World.install, World.store, World.prepare]
    · simp only [hgas12869, ↓reduceIte]
      by_cases hgas69 : 69 ≤ gas
      · have hnotdep : ¬(previewRuntimeBytes.length ≤ 24576 ∧
            previewRuntimeBytes.head? ≠ some 0xef ∧
            200 * previewRuntimeBytes.length ≤ gas - 69) := by
          rw [hlen_rt]; omega
        simp only [hgas69, ↓reduceIte, finishCreation]
        rw [if_neg hnotdep]
        exact ⟨rfl, rfl⟩
      · simp [hgas69, finishCreation, observeFrame]
  · simp only [hval, ↓reduceIte] at hrun ⊢
    rcases hrun with ⟨m', hrun_eq⟩
    have hmet := Guarded.metered_of_run
      (step previewCreationBytes input ⟨ctx, tx.original ctx.self, false⟩)
      20 (initialState staged tx ctx.self) 42 42
      ⟨.reverted [],
        { machine := m', storage := staged.storage ctx.self, warm := tx.warm ctx.self, refund := tx.refund }⟩
      gas hrun_eq
    unfold runMetered
    rw [hmet]
    by_cases hgas42 : 42 ≤ gas
    · simp [hgas42, finishCreation, observeFrame]
    · simp [hgas42, finishCreation, observeFrame]

private theorem slt_calldata_guard (n : Nat) (hn4 : 4 ≤ n) (hn64 : n < 2 ^ 64) :
    (BitVec.ofNat 256 n + ~~~3#256).slt 32#256 = decide (n < 36) := by
  have hsub : BitVec.ofNat 256 n + ~~~3#256 = BitVec.ofNat 256 (n - 4) := by
    apply BitVec.eq_of_toNat_eq
    have hnot3 : (~~~3#256).toNat = 2 ^ 256 - 4 := by decide
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hnot3]
    have hlt256 : n < 2 ^ 256 := by omega
    rw [Nat.mod_eq_of_lt hlt256]
    have hlt2 : n - 4 < 2 ^ 256 := by omega
    rw [Nat.mod_eq_of_lt hlt2]
    have hsum : n + (2 ^ 256 - 4) = 2 ^ 256 + (n - 4) := by omega
    rw [hsum, Nat.add_mod_left, Nat.mod_eq_of_lt hlt2]
  rw [hsub]
  unfold BitVec.slt
  have hlt2 : n - 4 < 2 ^ 256 := by omega
  have htoInt1 : (BitVec.ofNat 256 (n - 4)).toInt = Int.ofNat (n - 4) := by
    rw [BitVec.toInt_eq_toNat_cond]
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt2, show 2 * (n - 4) < 2 ^ 256 by omega]
  have htoInt2 : (32#256).toInt = 32 := by decide
  rw [htoInt1, htoInt2]
  by_cases h36 : n < 36
  · simp [h36]; omega
  · simp [h36]; omega

/-- Universal runtime theorem for `previewRuntimeBytes` (`Identity.identity(uint256)`):
For every `input : Input` with `input.calldata.length < 2^64`, environment `env`,
storage `storage`, warm set `warm`, and refund `refund`:
1. If `input.calldata.length ≥ 36`, `evmShr 0xe0#256 (loadWord input.calldata 0) = 0xac37eebb#256`,
   and `input.value = 0#256`:
   `Contract.Evm.run` halts with `Halt.returned (wordBytes (loadWord input.calldata 4))`,
   preserving `storage`, `warm`, and `refund` unchanged (exact gas `146`).
2. Otherwise (short calldata `< 4`, unknown selector, nonzero `msg.value`, or `< 36` calldata bytes):
   `Contract.Evm.run` halts with `Halt.reverted []`, preserving `storage`, `warm`, and `refund`. -/
theorem previewRuntime_run_universal (input : Input) (env : Environment)
    (storage : Slots) (warm : Word → Bool) (refund : Int)
    (hlen64 : input.calldata.length < 2 ^ 64) :
    let init : State := { storage := storage, warm := warm, refund := refund }
    let sel := evmShr 0xe0#256 (loadWord input.calldata 0)
    if 4 ≤ input.calldata.length ∧ sel = 0xac37eebb#256 ∧ input.value = 0#256 ∧ 36 ≤ input.calldata.length then
      ∃ m',
        Contract.Evm.run previewRuntimeBytes input env 40 init =
          .finished 146 146 ⟨.returned (wordBytes (loadWord input.calldata 4)),
            { machine := m', storage := storage, warm := warm, refund := refund }⟩
    else
      ∃ cost m',
        cost ≤ 146 ∧
        Contract.Evm.run previewRuntimeBytes input env 40 init =
          .finished cost cost ⟨.reverted [],
            { machine := m', storage := storage, warm := warm, refund := refund }⟩ := by
  dsimp only
  let mem0 : Memory := fun _ => 0
  let mem1 : Memory := Memory.write mem0 64 (wordBytes 128#256)
  let cdLenWord := BitVec.ofNat 256 input.calldata.length
  have hjumps : jumpDestinations previewRuntimeBytes = [0x11, 0x23, 0x3c] :=
    jumpDestinations_previewRuntime
  have hlt256 : input.calldata.length < 2 ^ 256 := by omega
  have hs0 : step previewRuntimeBytes input env
      { machine := { pc := 0, stack := [], memory := mem0, memoryWords := 0 },
        storage := storage, warm := warm, refund := refund } =
      .next 3 0
        { machine := { pc := 2, stack := [128#256], memory := mem0, memoryWords := 0 },
          storage := storage, warm := warm, refund := refund } :=
    step_word_at _ _ _ 0 [] [128#256] mem0 0 storage warm refund (.push 1 128#256) 2 3 (by decide) (fun _ => rfl) rfl
  have hs1 : step previewRuntimeBytes input env
      { machine := { pc := 2, stack := [128#256], memory := mem0, memoryWords := 0 },
        storage := storage, warm := warm, refund := refund } =
      .next 3 0
        { machine := { pc := 3, stack := [128#256, 128#256], memory := mem0, memoryWords := 0 },
          storage := storage, warm := warm, refund := refund } :=
    step_word_at _ _ _ 2 [128#256] [128#256, 128#256] mem0 0 storage warm refund (.dup 0) 1 3 (by decide) (fun _ => rfl) rfl
  have hs2 : step previewRuntimeBytes input env
      { machine := { pc := 3, stack := [128#256, 128#256], memory := mem0, memoryWords := 0 },
        storage := storage, warm := warm, refund := refund } =
      .next 3 0
        { machine := { pc := 5, stack := [64#256, 128#256, 128#256], memory := mem0, memoryWords := 0 },
          storage := storage, warm := warm, refund := refund } :=
    step_word_at _ _ _ 3 [128#256, 128#256] [64#256, 128#256, 128#256] mem0 0 storage warm refund (.push 1 64#256) 2 3 (by decide) (fun _ => rfl) rfl
  have hs3 : step previewRuntimeBytes input env
      { machine := { pc := 5, stack := [64#256, 128#256, 128#256], memory := mem0, memoryWords := 0 },
        storage := storage, warm := warm, refund := refund } =
      .next 12 0
        { machine := { pc := 6, stack := [128#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } := by
    simpa [mem1, mem0, expansionCost, expandedWords, memoryCost] using
      step_mstore_at previewRuntimeBytes input env 5 64#256 128#256 [128#256] mem0 0 storage warm refund (by decide) (by decide)
  have hs4 : step previewRuntimeBytes input env
      { machine := { pc := 6, stack := [128#256], memory := mem1, memoryWords := 3 },
        storage := storage, warm := warm, refund := refund } =
      .next 3 0
        { machine := { pc := 8, stack := [4#256, 128#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } :=
    step_word_at _ _ _ 6 [128#256] [4#256, 128#256] mem1 3 storage warm refund (.push 1 4#256) 2 3 (by decide) (fun _ => rfl) rfl
  have hs5 : step previewRuntimeBytes input env
      { machine := { pc := 8, stack := [4#256, 128#256], memory := mem1, memoryWords := 3 },
        storage := storage, warm := warm, refund := refund } =
      .next 2 0
        { machine := { pc := 9, stack := [cdLenWord, 4#256, 128#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } :=
    step_calldatasize_at _ _ _ 8 [4#256, 128#256] mem1 3 storage warm refund (by decide) (by decide) (by decide)
  have hs6 : step previewRuntimeBytes input env
      { machine := { pc := 9, stack := [cdLenWord, 4#256, 128#256], memory := mem1, memoryWords := 3 },
        storage := storage, warm := warm, refund := refund } =
      .next 3 0
        { machine := { pc := 10, stack := [boolWord (cdLenWord.ult 4#256), 128#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } :=
    step_word_at _ _ _ 9 [cdLenWord, 4#256, 128#256] [boolWord (cdLenWord.ult 4#256), 128#256] mem1 3 storage warm refund (.binary .lt) 1 3 (by decide) (fun _ => rfl) rfl
  by_cases h4 : input.calldata.length < 4
  · have hcond : ¬(4 ≤ input.calldata.length ∧
        evmShr 0xe0#256 (loadWord input.calldata 0) = 0xac37eebb#256 ∧
        input.value = 0#256 ∧ 36 ≤ input.calldata.length) := by omega
    rw [if_neg hcond]
    have hult : cdLenWord.ult 4#256 = true := by
      simp [cdLenWord, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt256, h4]
    have hs7 : step previewRuntimeBytes input env
        { machine := { pc := 10, stack := [1#256, 128#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } =
        .next 3 0
          { machine := { pc := 11, stack := [0#256, 128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } :=
      step_word_at _ _ _ 10 [1#256, 128#256] [0#256, 128#256] mem1 3 storage warm refund (.unary .iszero) 1 3 (by decide) (fun _ => rfl) rfl
    have hs8 : step previewRuntimeBytes input env
        { machine := { pc := 11, stack := [0#256, 128#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } =
        .next 3 0
          { machine := { pc := 13, stack := [17#256, 0#256, 128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } :=
      step_word_at _ _ _ 11 [0#256, 128#256] [17#256, 0#256, 128#256] mem1 3 storage warm refund (.push 1 17#256) 2 3 (by decide) (fun _ => rfl) rfl
    have hs9 : step previewRuntimeBytes input env
        { machine := { pc := 13, stack := [17#256, 0#256, 128#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } =
        .next 10 0
          { machine := { pc := 14, stack := [128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } :=
      step_jumpi_zero_at _ _ _ 13 17#256 [128#256] mem1 3 storage warm refund (by decide) (by decide)
    have hs10 : step previewRuntimeBytes input env
        { machine := { pc := 14, stack := [128#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } =
        .next 2 0
          { machine := { pc := 15, stack := [0#256, 128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } :=
      step_word_at _ _ _ 14 [128#256] [0#256, 128#256] mem1 3 storage warm refund (.push 0 0#256) 1 2 (by decide) (fun _ => rfl) rfl
    have hs11 : step previewRuntimeBytes input env
        { machine := { pc := 15, stack := [0#256, 128#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } =
        .next 3 0
          { machine := { pc := 16, stack := [0#256, 0#256, 128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } :=
      step_word_at _ _ _ 15 [0#256, 128#256] [0#256, 0#256, 128#256] mem1 3 storage warm refund (.dup 0) 1 3 (by decide) (fun _ => rfl) rfl
    have hs12 : step previewRuntimeBytes input env
        { machine := { pc := 16, stack := [0#256, 0#256, 128#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } =
        .halt 0 ⟨.reverted [],
          { machine := { pc := 16, stack := [0#256, 0#256, 128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund }⟩ := by
      simpa [expandedWords] using
        step_revert_zero_at previewRuntimeBytes input env 16 [128#256] mem1 3 storage warm refund (by decide) (by decide)
    refine ⟨50, { pc := 16, stack := [0#256, 0#256, 128#256], memory := mem1, memoryWords := 3 }, by omega, ?_⟩
    unfold Contract.Evm.run
    rw [guarded_run_next _ 39 _ _ _ _ hs0,
        guarded_run_next _ 38 _ _ _ _ hs1,
        guarded_run_next _ 37 _ _ _ _ hs2,
        guarded_run_next _ 36 _ _ _ _ hs3,
        guarded_run_next _ 35 _ _ _ _ hs4,
        guarded_run_next _ 34 _ _ _ _ hs5,
        guarded_run_next _ 33 _ _ _ _ hs6]
    rw [hult]; simp only [boolWord, ↓reduceIte]
    rw [guarded_run_next _ 32 _ _ _ _ hs7,
        guarded_run_next _ 31 _ _ _ _ hs8,
        guarded_run_next _ 30 _ _ _ _ hs9,
        guarded_run_next _ 29 _ _ _ _ hs10,
        guarded_run_next _ 28 _ _ _ _ hs11,
        guarded_run_halt _ 27 _ _ _ hs12]
    rfl
  · have hge4 : 4 ≤ input.calldata.length := by omega
    have hult : cdLenWord.ult 4#256 = false := by
      simp [cdLenWord, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt256, h4]
    let w0 := loadWord input.calldata 0
    let sel := evmShr 0xe0#256 w0
    have hs7 : step previewRuntimeBytes input env
        { machine := { pc := 10, stack := [0#256, 128#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } =
        .next 3 0
          { machine := { pc := 11, stack := [1#256, 128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } :=
      step_word_at _ _ _ 10 [0#256, 128#256] [1#256, 128#256] mem1 3 storage warm refund (.unary .iszero) 1 3 (by decide) (fun _ => rfl) rfl
    have hs8 : step previewRuntimeBytes input env
        { machine := { pc := 11, stack := [1#256, 128#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } =
        .next 3 0
          { machine := { pc := 13, stack := [17#256, 1#256, 128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } :=
      step_word_at _ _ _ 11 [1#256, 128#256] [17#256, 1#256, 128#256] mem1 3 storage warm refund (.push 1 17#256) 2 3 (by decide) (fun _ => rfl) rfl
    have hs9 : step previewRuntimeBytes input env
        { machine := { pc := 13, stack := [17#256, 1#256, 128#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } =
        .next 10 0
          { machine := { pc := 17, stack := [128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } :=
      step_jumpi_nonzero_at _ _ _ 13 17#256 1#256 [128#256] mem1 3 storage warm refund
        (by decide) (by decide) (by decide) (by rw [hjumps]; decide)
    have hs10 : step previewRuntimeBytes input env
        { machine := { pc := 17, stack := [128#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } =
        .next 1 0
          { machine := { pc := 18, stack := [128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } :=
      step_jumpdest_at _ _ _ 17 [128#256] mem1 3 storage warm refund (by decide) (by decide)
    have hs11 : step previewRuntimeBytes input env
        { machine := { pc := 18, stack := [128#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } =
        .next 2 0
          { machine := { pc := 19, stack := [0#256, 128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } :=
      step_word_at _ _ _ 18 [128#256] [0#256, 128#256] mem1 3 storage warm refund (.push 0 0#256) 1 2 (by decide) (fun _ => rfl) rfl
    have hs12 : step previewRuntimeBytes input env
        { machine := { pc := 19, stack := [0#256, 128#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } =
        .next 3 0
          { machine := { pc := 20, stack := [w0, 128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } := by
      simpa [w0] using
        step_calldataload_at previewRuntimeBytes input env 19 0#256 [128#256] mem1 3 storage warm refund (by decide) (by decide)
    have hs13 : step previewRuntimeBytes input env
        { machine := { pc := 20, stack := [w0, 128#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } =
        .next 3 0
          { machine := { pc := 22, stack := [0xe0#256, w0, 128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } :=
      step_word_at _ _ _ 20 [w0, 128#256] [0xe0#256, w0, 128#256] mem1 3 storage warm refund (.push 1 0xe0#256) 2 3 (by decide) (fun _ => by simp [WordOp.evalStack]) rfl
    have hs14 : step previewRuntimeBytes input env
        { machine := { pc := 22, stack := [0xe0#256, w0, 128#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } =
        .next 3 0
          { machine := { pc := 23, stack := [sel, 128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } :=
      step_word_at _ _ _ 22 [0xe0#256, w0, 128#256] [sel, 128#256] mem1 3 storage warm refund (.binary .shr) 1 3 (by decide) (fun _ => rfl) rfl
    have hs15 : step previewRuntimeBytes input env
        { machine := { pc := 23, stack := [sel, 128#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } =
        .next 3 0
          { machine := { pc := 28, stack := [0xac37eebb#256, sel, 128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } :=
      step_word_at _ _ _ 23 [sel, 128#256] [0xac37eebb#256, sel, 128#256] mem1 3 storage warm refund (.push 4 0xac37eebb#256) 5 3 (by decide) (fun _ => by simp [WordOp.evalStack]) rfl
    have hs16 : step previewRuntimeBytes input env
        { machine := { pc := 28, stack := [0xac37eebb#256, sel, 128#256], memory := mem1, memoryWords := 3 },
          storage := storage, warm := warm, refund := refund } =
        .next 3 0
          { machine := { pc := 29, stack := [boolWord (0xac37eebb#256 == sel), 128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } :=
      step_word_at _ _ _ 28 [0xac37eebb#256, sel, 128#256] [boolWord (0xac37eebb#256 == sel), 128#256] mem1 3 storage warm refund (.binary .eq) 1 3 (by decide) (fun _ => rfl) rfl
    by_cases hsel : sel = 0xac37eebb#256
    · have hbeq : (0xac37eebb#256 == sel) = true := by simp [hsel]
      have hs17 : step previewRuntimeBytes input env
          { machine := { pc := 29, stack := [1#256, 128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } =
          .next 3 0
            { machine := { pc := 31, stack := [35#256, 1#256, 128#256], memory := mem1, memoryWords := 3 },
              storage := storage, warm := warm, refund := refund } :=
        step_word_at _ _ _ 29 [1#256, 128#256] [35#256, 1#256, 128#256] mem1 3 storage warm refund (.push 1 35#256) 2 3 (by decide) (fun _ => rfl) rfl
      have hs18 : step previewRuntimeBytes input env
          { machine := { pc := 31, stack := [35#256, 1#256, 128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } =
          .next 10 0
            { machine := { pc := 35, stack := [128#256], memory := mem1, memoryWords := 3 },
              storage := storage, warm := warm, refund := refund } :=
        step_jumpi_nonzero_at _ _ _ 31 35#256 1#256 [128#256] mem1 3 storage warm refund
          (by decide) (by decide) (by decide) (by rw [hjumps]; decide)
      have hs19 : step previewRuntimeBytes input env
          { machine := { pc := 35, stack := [128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } =
          .next 1 0
            { machine := { pc := 36, stack := [128#256], memory := mem1, memoryWords := 3 },
              storage := storage, warm := warm, refund := refund } :=
        step_jumpdest_at _ _ _ 35 [128#256] mem1 3 storage warm refund (by decide) (by decide)
      have hs20 : step previewRuntimeBytes input env
          { machine := { pc := 36, stack := [128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } =
          .next 2 0
            { machine := { pc := 37, stack := [input.value, 128#256], memory := mem1, memoryWords := 3 },
              storage := storage, warm := warm, refund := refund } :=
        step_callvalue_at _ _ _ 36 [128#256] mem1 3 storage warm refund (by decide) (by decide) (by decide)
      have hs21 : step previewRuntimeBytes input env
          { machine := { pc := 37, stack := [input.value, 128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } =
          .next 3 0
            { machine := { pc := 39, stack := [60#256, input.value, 128#256], memory := mem1, memoryWords := 3 },
              storage := storage, warm := warm, refund := refund } :=
        step_word_at _ _ _ 37 [input.value, 128#256] [60#256, input.value, 128#256] mem1 3 storage warm refund (.push 1 60#256) 2 3 (by decide) (fun _ => by simp [WordOp.evalStack]) rfl
      by_cases hval : input.value = 0#256
      · have hs22 : step previewRuntimeBytes input env
            { machine := { pc := 39, stack := [60#256, 0#256, 128#256], memory := mem1, memoryWords := 3 },
              storage := storage, warm := warm, refund := refund } =
            .next 10 0
              { machine := { pc := 40, stack := [128#256], memory := mem1, memoryWords := 3 },
                storage := storage, warm := warm, refund := refund } :=
          step_jumpi_zero_at _ _ _ 39 60#256 [128#256] mem1 3 storage warm refund (by decide) (by decide)
        have hs23 : step previewRuntimeBytes input env
            { machine := { pc := 40, stack := [128#256], memory := mem1, memoryWords := 3 },
              storage := storage, warm := warm, refund := refund } =
            .next 3 0
              { machine := { pc := 42, stack := [32#256, 128#256], memory := mem1, memoryWords := 3 },
                storage := storage, warm := warm, refund := refund } :=
          step_word_at _ _ _ 40 [128#256] [32#256, 128#256] mem1 3 storage warm refund (.push 1 32#256) 2 3 (by decide) (fun _ => rfl) rfl
        have hs24 : step previewRuntimeBytes input env
            { machine := { pc := 42, stack := [32#256, 128#256], memory := mem1, memoryWords := 3 },
              storage := storage, warm := warm, refund := refund } =
            .next 2 0
              { machine := { pc := 43, stack := [cdLenWord, 32#256, 128#256], memory := mem1, memoryWords := 3 },
                storage := storage, warm := warm, refund := refund } :=
          step_calldatasize_at _ _ _ 42 [32#256, 128#256] mem1 3 storage warm refund (by decide) (by decide) (by decide)
        have hs25 : step previewRuntimeBytes input env
            { machine := { pc := 43, stack := [cdLenWord, 32#256, 128#256], memory := mem1, memoryWords := 3 },
              storage := storage, warm := warm, refund := refund } =
            .next 3 0
              { machine := { pc := 45, stack := [3#256, cdLenWord, 32#256, 128#256], memory := mem1, memoryWords := 3 },
                storage := storage, warm := warm, refund := refund } :=
          step_word_at _ _ _ 43 [cdLenWord, 32#256, 128#256] [3#256, cdLenWord, 32#256, 128#256] mem1 3 storage warm refund (.push 1 3#256) 2 3 (by decide) (fun _ => by simp [WordOp.evalStack]) rfl
        have hs26 : step previewRuntimeBytes input env
            { machine := { pc := 45, stack := [3#256, cdLenWord, 32#256, 128#256], memory := mem1, memoryWords := 3 },
              storage := storage, warm := warm, refund := refund } =
            .next 3 0
              { machine := { pc := 46, stack := [~~~3#256, cdLenWord, 32#256, 128#256], memory := mem1, memoryWords := 3 },
                storage := storage, warm := warm, refund := refund } :=
          step_word_at _ _ _ 45 [3#256, cdLenWord, 32#256, 128#256] [~~~3#256, cdLenWord, 32#256, 128#256] mem1 3 storage warm refund (.unary .bitnot) 1 3 (by decide) (fun _ => rfl) rfl
        have hs27 : step previewRuntimeBytes input env
            { machine := { pc := 46, stack := [~~~3#256, cdLenWord, 32#256, 128#256], memory := mem1, memoryWords := 3 },
              storage := storage, warm := warm, refund := refund } =
            .next 3 0
              { machine := { pc := 47, stack := [~~~3#256 + cdLenWord, 32#256, 128#256], memory := mem1, memoryWords := 3 },
                storage := storage, warm := warm, refund := refund } :=
          step_word_at _ _ _ 46 [~~~3#256, cdLenWord, 32#256, 128#256] [~~~3#256 + cdLenWord, 32#256, 128#256] mem1 3 storage warm refund (.binary .add) 1 3 (by decide) (fun _ => rfl) rfl
        have hs28 : step previewRuntimeBytes input env
            { machine := { pc := 47, stack := [~~~3#256 + cdLenWord, 32#256, 128#256], memory := mem1, memoryWords := 3 },
              storage := storage, warm := warm, refund := refund } =
            .next 3 0
              { machine := { pc := 48, stack := [boolWord ((~~~3#256 + cdLenWord).slt 32#256), 128#256], memory := mem1, memoryWords := 3 },
                storage := storage, warm := warm, refund := refund } :=
          step_word_at _ _ _ 47 [~~~3#256 + cdLenWord, 32#256, 128#256] [boolWord ((~~~3#256 + cdLenWord).slt 32#256), 128#256] mem1 3 storage warm refund (.binary .slt) 1 3 (by decide) (fun _ => rfl) rfl
        have hcomm : ~~~3#256 + cdLenWord = cdLenWord + ~~~3#256 := BitVec.add_comm _ _
        have hslt := slt_calldata_guard input.calldata.length hge4 hlen64
        by_cases h36 : input.calldata.length < 36
        · have hcond : ¬(4 ≤ input.calldata.length ∧ sel = 0xac37eebb#256 ∧
              input.value = 0#256 ∧ 36 ≤ input.calldata.length) := by omega
          rw [if_neg hcond]
          have hslt_t : (~~~3#256 + cdLenWord).slt 32#256 = true := by
            rw [hcomm, hslt]; simp [h36]
          have hs29 : step previewRuntimeBytes input env
              { machine := { pc := 48, stack := [1#256, 128#256], memory := mem1, memoryWords := 3 },
                storage := storage, warm := warm, refund := refund } =
              .next 3 0
                { machine := { pc := 50, stack := [60#256, 1#256, 128#256], memory := mem1, memoryWords := 3 },
                  storage := storage, warm := warm, refund := refund } :=
            step_word_at _ _ _ 48 [1#256, 128#256] [60#256, 1#256, 128#256] mem1 3 storage warm refund (.push 1 60#256) 2 3 (by decide) (fun _ => rfl) rfl
          have hs30 : step previewRuntimeBytes input env
              { machine := { pc := 50, stack := [60#256, 1#256, 128#256], memory := mem1, memoryWords := 3 },
                storage := storage, warm := warm, refund := refund } =
              .next 10 0
                { machine := { pc := 60, stack := [128#256], memory := mem1, memoryWords := 3 },
                  storage := storage, warm := warm, refund := refund } :=
            step_jumpi_nonzero_at _ _ _ 50 60#256 1#256 [128#256] mem1 3 storage warm refund
              (by decide) (by decide) (by decide) (by rw [hjumps]; decide)
          have hs31 : step previewRuntimeBytes input env
              { machine := { pc := 60, stack := [128#256], memory := mem1, memoryWords := 3 },
                storage := storage, warm := warm, refund := refund } =
              .next 1 0
                { machine := { pc := 61, stack := [128#256], memory := mem1, memoryWords := 3 },
                  storage := storage, warm := warm, refund := refund } :=
            step_jumpdest_at _ _ _ 60 [128#256] mem1 3 storage warm refund (by decide) (by decide)
          have hs32 : step previewRuntimeBytes input env
              { machine := { pc := 61, stack := [128#256], memory := mem1, memoryWords := 3 },
                storage := storage, warm := warm, refund := refund } =
              .next 2 0
                { machine := { pc := 62, stack := [0#256, 128#256], memory := mem1, memoryWords := 3 },
                  storage := storage, warm := warm, refund := refund } :=
            step_word_at _ _ _ 61 [128#256] [0#256, 128#256] mem1 3 storage warm refund (.push 0 0#256) 1 2 (by decide) (fun _ => rfl) rfl
          have hs33 : step previewRuntimeBytes input env
              { machine := { pc := 62, stack := [0#256, 128#256], memory := mem1, memoryWords := 3 },
                storage := storage, warm := warm, refund := refund } =
              .next 3 0
                { machine := { pc := 63, stack := [0#256, 0#256, 128#256], memory := mem1, memoryWords := 3 },
                  storage := storage, warm := warm, refund := refund } :=
            step_word_at _ _ _ 62 [0#256, 128#256] [0#256, 0#256, 128#256] mem1 3 storage warm refund (.dup 0) 1 3 (by decide) (fun _ => rfl) rfl
          have hs34 : step previewRuntimeBytes input env
              { machine := { pc := 63, stack := [0#256, 0#256, 128#256], memory := mem1, memoryWords := 3 },
                storage := storage, warm := warm, refund := refund } =
              .halt 0 ⟨.reverted [],
                { machine := { pc := 63, stack := [0#256, 0#256, 128#256], memory := mem1, memoryWords := 3 },
                  storage := storage, warm := warm, refund := refund }⟩ := by
            simpa [expandedWords] using
              step_revert_zero_at previewRuntimeBytes input env 63 [128#256] mem1 3 storage warm refund (by decide) (by decide)
          refine ⟨128, { pc := 63, stack := [0#256, 0#256, 128#256], memory := mem1, memoryWords := 3 }, by omega, ?_⟩
          unfold Contract.Evm.run
          rw [guarded_run_next _ 39 _ _ _ _ hs0,
              guarded_run_next _ 38 _ _ _ _ hs1,
              guarded_run_next _ 37 _ _ _ _ hs2,
              guarded_run_next _ 36 _ _ _ _ hs3,
              guarded_run_next _ 35 _ _ _ _ hs4,
              guarded_run_next _ 34 _ _ _ _ hs5,
              guarded_run_next _ 33 _ _ _ _ hs6]
          rw [hult]; simp only [boolWord, Bool.false_eq_true, ↓reduceIte]
          rw [guarded_run_next _ 32 _ _ _ _ hs7,
              guarded_run_next _ 31 _ _ _ _ hs8,
              guarded_run_next _ 30 _ _ _ _ hs9,
              guarded_run_next _ 29 _ _ _ _ hs10,
              guarded_run_next _ 28 _ _ _ _ hs11,
              guarded_run_next _ 27 _ _ _ _ hs12,
              guarded_run_next _ 26 _ _ _ _ hs13,
              guarded_run_next _ 25 _ _ _ _ hs14,
              guarded_run_next _ 24 _ _ _ _ hs15,
              guarded_run_next _ 23 _ _ _ _ hs16]
          rw [hbeq]; simp only [boolWord, ↓reduceIte]
          rw [guarded_run_next _ 22 _ _ _ _ hs17,
              guarded_run_next _ 21 _ _ _ _ hs18,
              guarded_run_next _ 20 _ _ _ _ hs19,
              guarded_run_next _ 19 _ _ _ _ hs20,
              guarded_run_next _ 18 _ _ _ _ hs21]
          rw [hval]
          rw [guarded_run_next _ 17 _ _ _ _ hs22,
              guarded_run_next _ 16 _ _ _ _ hs23,
              guarded_run_next _ 15 _ _ _ _ hs24,
              guarded_run_next _ 14 _ _ _ _ hs25,
              guarded_run_next _ 13 _ _ _ _ hs26,
              guarded_run_next _ 12 _ _ _ _ hs27,
              guarded_run_next _ 11 _ _ _ _ hs28]
          rw [hslt_t]; simp only [boolWord, ↓reduceIte]
          rw [guarded_run_next _ 10 _ _ _ _ hs29,
              guarded_run_next _ 9 _ _ _ _ hs30,
              guarded_run_next _ 8 _ _ _ _ hs31,
              guarded_run_next _ 7 _ _ _ _ hs32,
              guarded_run_next _ 6 _ _ _ _ hs33,
              guarded_run_halt _ 5 _ _ _ hs34]
          simp only [trace_charge_zero]
        · have hge36 : 36 ≤ input.calldata.length := by omega
          have hcond : 4 ≤ input.calldata.length ∧ sel = 0xac37eebb#256 ∧
              input.value = 0#256 ∧ 36 ≤ input.calldata.length := ⟨hge4, hsel, hval, hge36⟩
          rw [if_pos hcond]
          have hslt_f : (~~~3#256 + cdLenWord).slt 32#256 = false := by
            rw [hcomm, hslt]; simp [h36]
          let w4 := loadWord input.calldata 4
          let mem2 : Memory := mem1.write 128 (wordBytes w4)
          have hs29 : step previewRuntimeBytes input env
              { machine := { pc := 48, stack := [0#256, 128#256], memory := mem1, memoryWords := 3 },
                storage := storage, warm := warm, refund := refund } =
              .next 3 0
                { machine := { pc := 50, stack := [60#256, 0#256, 128#256], memory := mem1, memoryWords := 3 },
                  storage := storage, warm := warm, refund := refund } :=
            step_word_at _ _ _ 48 [0#256, 128#256] [60#256, 0#256, 128#256] mem1 3 storage warm refund (.push 1 60#256) 2 3 (by decide) (fun _ => rfl) rfl
          have hs30 : step previewRuntimeBytes input env
              { machine := { pc := 50, stack := [60#256, 0#256, 128#256], memory := mem1, memoryWords := 3 },
                storage := storage, warm := warm, refund := refund } =
              .next 10 0
                { machine := { pc := 51, stack := [128#256], memory := mem1, memoryWords := 3 },
                  storage := storage, warm := warm, refund := refund } :=
            step_jumpi_zero_at _ _ _ 50 60#256 [128#256] mem1 3 storage warm refund (by decide) (by decide)
          have hs31 : step previewRuntimeBytes input env
              { machine := { pc := 51, stack := [128#256], memory := mem1, memoryWords := 3 },
                storage := storage, warm := warm, refund := refund } =
              .next 3 0
                { machine := { pc := 53, stack := [32#256, 128#256], memory := mem1, memoryWords := 3 },
                  storage := storage, warm := warm, refund := refund } :=
            step_word_at _ _ _ 51 [128#256] [32#256, 128#256] mem1 3 storage warm refund (.push 1 32#256) 2 3 (by decide) (fun _ => rfl) rfl
          have hs32 : step previewRuntimeBytes input env
              { machine := { pc := 53, stack := [32#256, 128#256], memory := mem1, memoryWords := 3 },
                storage := storage, warm := warm, refund := refund } =
              .next 3 0
                { machine := { pc := 54, stack := [128#256, 32#256], memory := mem1, memoryWords := 3 },
                  storage := storage, warm := warm, refund := refund } :=
            step_swap1_at _ _ _ 53 32#256 128#256 [] mem1 3 storage warm refund (by decide)
          have hs33 : step previewRuntimeBytes input env
              { machine := { pc := 54, stack := [128#256, 32#256], memory := mem1, memoryWords := 3 },
                storage := storage, warm := warm, refund := refund } =
              .next 3 0
                { machine := { pc := 56, stack := [4#256, 128#256, 32#256], memory := mem1, memoryWords := 3 },
                  storage := storage, warm := warm, refund := refund } :=
            step_word_at _ _ _ 54 [128#256, 32#256] [4#256, 128#256, 32#256] mem1 3 storage warm refund (.push 1 4#256) 2 3 (by decide) (fun _ => rfl) rfl
          have hs34 : step previewRuntimeBytes input env
              { machine := { pc := 56, stack := [4#256, 128#256, 32#256], memory := mem1, memoryWords := 3 },
                storage := storage, warm := warm, refund := refund } =
              .next 3 0
                { machine := { pc := 57, stack := [w4, 128#256, 32#256], memory := mem1, memoryWords := 3 },
                  storage := storage, warm := warm, refund := refund } := by
            simpa [w4] using
              step_calldataload_at previewRuntimeBytes input env 56 4#256 [128#256, 32#256] mem1 3 storage warm refund (by decide) (by decide)
          have hs35 : step previewRuntimeBytes input env
              { machine := { pc := 57, stack := [w4, 128#256, 32#256], memory := mem1, memoryWords := 3 },
                storage := storage, warm := warm, refund := refund } =
              .next 3 0
                { machine := { pc := 58, stack := [128#256, w4, 128#256, 32#256], memory := mem1, memoryWords := 3 },
                  storage := storage, warm := warm, refund := refund } :=
            step_word_at _ _ _ 57 [w4, 128#256, 32#256] [128#256, w4, 128#256, 32#256] mem1 3 storage warm refund (.dup 1) 1 3 (by decide) (fun _ => by simp [WordOp.evalStack]) rfl
          have hs36 : step previewRuntimeBytes input env
              { machine := { pc := 58, stack := [128#256, w4, 128#256, 32#256], memory := mem1, memoryWords := 3 },
                storage := storage, warm := warm, refund := refund } =
              .next 9 0
                { machine := { pc := 59, stack := [128#256, 32#256], memory := mem2, memoryWords := 5 },
                  storage := storage, warm := warm, refund := refund } := by
            simpa [mem2, expansionCost, expandedWords, memoryCost] using
              step_mstore_at previewRuntimeBytes input env 58 128#256 w4 [128#256, 32#256] mem1 3 storage warm refund (by decide) (by decide)
          have hs37 : step previewRuntimeBytes input env
              { machine := { pc := 59, stack := [128#256, 32#256], memory := mem2, memoryWords := 5 },
                storage := storage, warm := warm, refund := refund } =
              .halt 0 ⟨.returned (wordBytes w4),
                { machine := { pc := 59, stack := [128#256, 32#256], memory := mem2, memoryWords := 5 },
                  storage := storage, warm := warm, refund := refund }⟩ := by
            have hlenw : (wordBytes w4).length = 32 := wordBytes_length w4
            have hrw := Memory.read_write_same mem1 128 (wordBytes w4)
            have hread : mem2.read 128 32 = wordBytes w4 := by simpa [mem2, hlenw] using hrw
            unfold step
            dsimp only [expansionCost, expandedWords, memoryCost]
            have hd : decodeWordOp previewRuntimeBytes 59 (previewRuntimeBytes[59]?.getD 0) = none := by decide
            have hop : previewRuntimeBytes[59]?.getD 0 = 0xf3 := by decide
            rw [hd, hop]
            have h128 : (128#256).toNat = 128 := by decide
            have h32 : (32#256).toNat = 32 := by decide
            rw [h128, h32, hread]
            rfl
          refine ⟨{ pc := 59, stack := [128#256, 32#256], memory := mem2, memoryWords := 5 }, ?_⟩
          unfold Contract.Evm.run
          rw [guarded_run_next _ 39 _ _ _ _ hs0,
              guarded_run_next _ 38 _ _ _ _ hs1,
              guarded_run_next _ 37 _ _ _ _ hs2,
              guarded_run_next _ 36 _ _ _ _ hs3,
              guarded_run_next _ 35 _ _ _ _ hs4,
              guarded_run_next _ 34 _ _ _ _ hs5,
              guarded_run_next _ 33 _ _ _ _ hs6]
          rw [hult]; simp only [boolWord, Bool.false_eq_true, ↓reduceIte]
          rw [guarded_run_next _ 32 _ _ _ _ hs7,
              guarded_run_next _ 31 _ _ _ _ hs8,
              guarded_run_next _ 30 _ _ _ _ hs9,
              guarded_run_next _ 29 _ _ _ _ hs10,
              guarded_run_next _ 28 _ _ _ _ hs11,
              guarded_run_next _ 27 _ _ _ _ hs12,
              guarded_run_next _ 26 _ _ _ _ hs13,
              guarded_run_next _ 25 _ _ _ _ hs14,
              guarded_run_next _ 24 _ _ _ _ hs15,
              guarded_run_next _ 23 _ _ _ _ hs16]
          rw [hbeq]; simp only [boolWord, ↓reduceIte]
          rw [guarded_run_next _ 22 _ _ _ _ hs17,
              guarded_run_next _ 21 _ _ _ _ hs18,
              guarded_run_next _ 20 _ _ _ _ hs19,
              guarded_run_next _ 19 _ _ _ _ hs20,
              guarded_run_next _ 18 _ _ _ _ hs21]
          rw [hval]
          rw [guarded_run_next _ 17 _ _ _ _ hs22,
              guarded_run_next _ 16 _ _ _ _ hs23,
              guarded_run_next _ 15 _ _ _ _ hs24,
              guarded_run_next _ 14 _ _ _ _ hs25,
              guarded_run_next _ 13 _ _ _ _ hs26,
              guarded_run_next _ 12 _ _ _ _ hs27,
              guarded_run_next _ 11 _ _ _ _ hs28]
          rw [hslt_f]; simp only [boolWord, Bool.false_eq_true, ↓reduceIte]
          rw [guarded_run_next _ 10 _ _ _ _ hs29,
              guarded_run_next _ 9 _ _ _ _ hs30,
              guarded_run_next _ 8 _ _ _ _ hs31,
              guarded_run_next _ 7 _ _ _ _ hs32,
              guarded_run_next _ 6 _ _ _ _ hs33,
              guarded_run_next _ 5 _ _ _ _ hs34,
              guarded_run_next _ 4 _ _ _ _ hs35,
              guarded_run_next _ 3 _ _ _ _ hs36,
              guarded_run_halt _ 2 _ _ _ hs37]
          simp only [trace_charge_zero]; rfl
      · have hcond : ¬(4 ≤ input.calldata.length ∧ sel = 0xac37eebb#256 ∧
            input.value = 0#256 ∧ 36 ≤ input.calldata.length) := by
          intro h; exact hval h.2.2.1
        rw [if_neg hcond]
        have hs22 : step previewRuntimeBytes input env
            { machine := { pc := 39, stack := [60#256, input.value, 128#256], memory := mem1, memoryWords := 3 },
              storage := storage, warm := warm, refund := refund } =
            .next 10 0
              { machine := { pc := 60, stack := [128#256], memory := mem1, memoryWords := 3 },
                storage := storage, warm := warm, refund := refund } :=
          step_jumpi_nonzero_at _ _ _ 39 60#256 input.value [128#256] mem1 3 storage warm refund
            (by decide) (by decide) hval (by rw [hjumps]; decide)
        have hs23 : step previewRuntimeBytes input env
            { machine := { pc := 60, stack := [128#256], memory := mem1, memoryWords := 3 },
              storage := storage, warm := warm, refund := refund } =
            .next 1 0
              { machine := { pc := 61, stack := [128#256], memory := mem1, memoryWords := 3 },
                storage := storage, warm := warm, refund := refund } :=
          step_jumpdest_at _ _ _ 60 [128#256] mem1 3 storage warm refund (by decide) (by decide)
        have hs24 : step previewRuntimeBytes input env
            { machine := { pc := 61, stack := [128#256], memory := mem1, memoryWords := 3 },
              storage := storage, warm := warm, refund := refund } =
            .next 2 0
              { machine := { pc := 62, stack := [0#256, 128#256], memory := mem1, memoryWords := 3 },
                storage := storage, warm := warm, refund := refund } :=
          step_word_at _ _ _ 61 [128#256] [0#256, 128#256] mem1 3 storage warm refund (.push 0 0#256) 1 2 (by decide) (fun _ => rfl) rfl
        have hs25 : step previewRuntimeBytes input env
            { machine := { pc := 62, stack := [0#256, 128#256], memory := mem1, memoryWords := 3 },
              storage := storage, warm := warm, refund := refund } =
            .next 3 0
              { machine := { pc := 63, stack := [0#256, 0#256, 128#256], memory := mem1, memoryWords := 3 },
                storage := storage, warm := warm, refund := refund } :=
          step_word_at _ _ _ 62 [0#256, 128#256] [0#256, 0#256, 128#256] mem1 3 storage warm refund (.dup 0) 1 3 (by decide) (fun _ => rfl) rfl
        have hs26 : step previewRuntimeBytes input env
            { machine := { pc := 63, stack := [0#256, 0#256, 128#256], memory := mem1, memoryWords := 3 },
              storage := storage, warm := warm, refund := refund } =
            .halt 0 ⟨.reverted [],
              { machine := { pc := 63, stack := [0#256, 0#256, 128#256], memory := mem1, memoryWords := 3 },
                storage := storage, warm := warm, refund := refund }⟩ := by
          simpa [expandedWords] using
            step_revert_zero_at previewRuntimeBytes input env 63 [128#256] mem1 3 storage warm refund (by decide) (by decide)
        refine ⟨98, { pc := 63, stack := [0#256, 0#256, 128#256], memory := mem1, memoryWords := 3 }, by omega, ?_⟩
        unfold Contract.Evm.run
        rw [guarded_run_next _ 39 _ _ _ _ hs0,
            guarded_run_next _ 38 _ _ _ _ hs1,
            guarded_run_next _ 37 _ _ _ _ hs2,
            guarded_run_next _ 36 _ _ _ _ hs3,
            guarded_run_next _ 35 _ _ _ _ hs4,
            guarded_run_next _ 34 _ _ _ _ hs5,
            guarded_run_next _ 33 _ _ _ _ hs6]
        rw [hult]; simp only [boolWord, Bool.false_eq_true, ↓reduceIte]
        rw [guarded_run_next _ 32 _ _ _ _ hs7,
            guarded_run_next _ 31 _ _ _ _ hs8,
            guarded_run_next _ 30 _ _ _ _ hs9,
            guarded_run_next _ 29 _ _ _ _ hs10,
            guarded_run_next _ 28 _ _ _ _ hs11,
            guarded_run_next _ 27 _ _ _ _ hs12,
            guarded_run_next _ 26 _ _ _ _ hs13,
            guarded_run_next _ 25 _ _ _ _ hs14,
            guarded_run_next _ 24 _ _ _ _ hs15,
            guarded_run_next _ 23 _ _ _ _ hs16]
        rw [hbeq]; simp only [boolWord, ↓reduceIte]
        rw [guarded_run_next _ 22 _ _ _ _ hs17,
            guarded_run_next _ 21 _ _ _ _ hs18,
            guarded_run_next _ 20 _ _ _ _ hs19,
            guarded_run_next _ 19 _ _ _ _ hs20,
            guarded_run_next _ 18 _ _ _ _ hs21,
            guarded_run_next _ 17 _ _ _ _ hs22,
            guarded_run_next _ 16 _ _ _ _ hs23,
            guarded_run_next _ 15 _ _ _ _ hs24,
            guarded_run_next _ 14 _ _ _ _ hs25,
            guarded_run_halt _ 13 _ _ _ hs26]
        simp only [trace_charge_zero]
    · have hcond : ¬(4 ≤ input.calldata.length ∧ sel = 0xac37eebb#256 ∧
          input.value = 0#256 ∧ 36 ≤ input.calldata.length) := by
        intro h; exact hsel h.2.1
      rw [if_neg hcond]
      have hbeq : (0xac37eebb#256 == sel) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun h => hsel h.symm
      have hs17 : step previewRuntimeBytes input env
          { machine := { pc := 29, stack := [0#256, 128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } =
          .next 3 0
            { machine := { pc := 31, stack := [35#256, 0#256, 128#256], memory := mem1, memoryWords := 3 },
              storage := storage, warm := warm, refund := refund } :=
        step_word_at _ _ _ 29 [0#256, 128#256] [35#256, 0#256, 128#256] mem1 3 storage warm refund (.push 1 35#256) 2 3 (by decide) (fun _ => rfl) rfl
      have hs18 : step previewRuntimeBytes input env
          { machine := { pc := 31, stack := [35#256, 0#256, 128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } =
          .next 10 0
            { machine := { pc := 32, stack := [128#256], memory := mem1, memoryWords := 3 },
              storage := storage, warm := warm, refund := refund } :=
        step_jumpi_zero_at _ _ _ 31 35#256 [128#256] mem1 3 storage warm refund (by decide) (by decide)
      have hs19 : step previewRuntimeBytes input env
          { machine := { pc := 32, stack := [128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } =
          .next 2 0
            { machine := { pc := 33, stack := [0#256, 128#256], memory := mem1, memoryWords := 3 },
              storage := storage, warm := warm, refund := refund } :=
        step_word_at _ _ _ 32 [128#256] [0#256, 128#256] mem1 3 storage warm refund (.push 0 0#256) 1 2 (by decide) (fun _ => rfl) rfl
      have hs20 : step previewRuntimeBytes input env
          { machine := { pc := 33, stack := [0#256, 128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } =
          .next 3 0
            { machine := { pc := 34, stack := [0#256, 0#256, 128#256], memory := mem1, memoryWords := 3 },
              storage := storage, warm := warm, refund := refund } :=
        step_word_at _ _ _ 33 [0#256, 128#256] [0#256, 0#256, 128#256] mem1 3 storage warm refund (.dup 0) 1 3 (by decide) (fun _ => rfl) rfl
      have hs21 : step previewRuntimeBytes input env
          { machine := { pc := 34, stack := [0#256, 0#256, 128#256], memory := mem1, memoryWords := 3 },
            storage := storage, warm := warm, refund := refund } =
          .halt 0 ⟨.reverted [],
            { machine := { pc := 34, stack := [0#256, 0#256, 128#256], memory := mem1, memoryWords := 3 },
              storage := storage, warm := warm, refund := refund }⟩ := by
        simpa [expandedWords] using
          step_revert_zero_at previewRuntimeBytes input env 34 [128#256] mem1 3 storage warm refund (by decide) (by decide)
      refine ⟨81, { pc := 34, stack := [0#256, 0#256, 128#256], memory := mem1, memoryWords := 3 }, by omega, ?_⟩
      unfold Contract.Evm.run
      rw [guarded_run_next _ 39 _ _ _ _ hs0,
          guarded_run_next _ 38 _ _ _ _ hs1,
          guarded_run_next _ 37 _ _ _ _ hs2,
          guarded_run_next _ 36 _ _ _ _ hs3,
          guarded_run_next _ 35 _ _ _ _ hs4,
          guarded_run_next _ 34 _ _ _ _ hs5,
          guarded_run_next _ 33 _ _ _ _ hs6]
      rw [hult]; simp only [boolWord, Bool.false_eq_true, ↓reduceIte]
      rw [guarded_run_next _ 32 _ _ _ _ hs7,
          guarded_run_next _ 31 _ _ _ _ hs8,
          guarded_run_next _ 30 _ _ _ _ hs9,
          guarded_run_next _ 29 _ _ _ _ hs10,
          guarded_run_next _ 28 _ _ _ _ hs11,
          guarded_run_next _ 27 _ _ _ _ hs12,
          guarded_run_next _ 26 _ _ _ _ hs13,
          guarded_run_next _ 25 _ _ _ _ hs14,
          guarded_run_next _ 24 _ _ _ _ hs15,
          guarded_run_next _ 23 _ _ _ _ hs16]
      rw [hbeq]; simp only [boolWord, Bool.false_eq_true, ↓reduceIte]
      rw [guarded_run_next _ 22 _ _ _ _ hs17,
          guarded_run_next _ 21 _ _ _ _ hs18,
          guarded_run_next _ 20 _ _ _ _ hs19,
          guarded_run_next _ 19 _ _ _ _ hs20,
          guarded_run_halt _ 18 _ _ _ hs21]
      simp only [trace_charge_zero]

/-- End-to-end world-frame runtime certificate (`publicPreviewIdentity_certified`)
for `Identity.identity(uint256)` over `Contract.Evm.executeCall`:
For ANY world state with `world.code ctx.self = previewRuntimeBytes`, transaction state `tx`,
execution context `ctx`, call input `input` (`calldata.length < 2^64`), static flag `isStatic`,
and execution gas budget `gas : Nat`:
- Valid call (`calldata.length ≥ 36`, selector `0xac37eebb`, `input.value = 0`):
  returns exact 32-byte ABI word `wordBytes (loadWord input.calldata 4)` with `gas - 146`
  remaining whenever `146 ≤ gas`, and faults cleanly (preserving `world`) if `gas < 146`.
- Invalid call (short calldata, wrong selector, nonpayable value, or static value transfer):
  reverts or faults without mutating `world`! -/
theorem publicPreviewIdentity_certified (world : World) (tx : Transaction) (ctx : Context)
    (input : Input) (isStatic : Bool) (gas : Nat)
    (hcode : world.code ctx.self = previewRuntimeBytes)
    (hlen64 : input.calldata.length < 2 ^ 64) :
    let frame := executeCall world tx ctx input isStatic 40 gas
    let sel := evmShr 0xe0#256 (loadWord input.calldata 0)
    if 4 ≤ input.calldata.length ∧ sel = 0xac37eebb#256 ∧ input.value = 0#256 ∧ 36 ≤ input.calldata.length then
      if 146 ≤ gas then
        frame.status = .returned ∧
        frame.bytes = wordBytes (loadWord input.calldata 4) ∧
        frame.world.balances = world.balances ∧
        frame.world.storage ctx.self = world.storage ctx.self ∧
        frame.gasRemaining = gas - 146
      else
        frame.status = .exceptional ∧ frame.world = world
    else
      (frame.status = .reverted ∨ frame.status = .exceptional) ∧ frame.world = world := by
  dsimp only
  by_cases hvalid :
      4 ≤ input.calldata.length ∧
      evmShr 0xe0#256 (loadWord input.calldata 0) = 0xac37eebb#256 ∧
      input.value = 0#256 ∧ 36 ≤ input.calldata.length
  · rw [if_pos hvalid]
    have hval0 : input.value = 0#256 := hvalid.2.2.1
    have hstat : (isStatic && input.value != 0#256) = false := by simp [hval0]
    have htr : world.transfer ctx.caller ctx.self input.value = some world := by
      unfold World.transfer
      simp [hval0]
    unfold executeCall
    rw [hstat]
    simp only [Bool.false_eq_true, ↓reduceIte, htr]
    have hrun := previewRuntime_run_universal input ⟨ctx, tx.original ctx.self, isStatic⟩
      (world.storage ctx.self) (tx.warm ctx.self) tx.refund hlen64
    dsimp only at hrun
    rw [if_pos hvalid] at hrun
    rcases hrun with ⟨m', hrun_eq⟩
    have hmet := Guarded.metered_of_run
      (step previewRuntimeBytes input ⟨ctx, tx.original ctx.self, isStatic⟩)
      40 (initialState world tx ctx.self) 146 146
      ⟨.returned (wordBytes (loadWord input.calldata 4)),
        { machine := m', storage := world.storage ctx.self, warm := tx.warm ctx.self, refund := tx.refund }⟩
      gas hrun_eq
    unfold runMetered
    rw [hcode, hmet]
    by_cases hgas : 146 ≤ gas
    · simp [hgas, observeFrame, World.store]
    · simp [hgas, observeFrame]
  · rw [if_neg hvalid]
    unfold executeCall
    split
    · exact ⟨Or.inr rfl, rfl⟩
    · cases htr : world.transfer ctx.caller ctx.self input.value with
      | none => exact ⟨Or.inr rfl, rfl⟩
      | some staged =>
        dsimp only
        have hcode_staged : staged.code ctx.self = previewRuntimeBytes := by
          unfold World.transfer at htr
          by_cases hle : input.value.toNat ≤ world.balances ctx.caller
          · simp only [hle, ↓reduceIte] at htr
            by_cases hz : input.value = 0#256 ∨ ctx.caller = ctx.self
            · simp only [hz, ↓reduceIte, Option.some.injEq] at htr
              subst htr; exact hcode
            · simp only [hz, ↓reduceIte, Option.some.injEq] at htr
              subst htr; exact hcode
          · simp [hle] at htr
        have hrun := previewRuntime_run_universal input ⟨ctx, tx.original ctx.self, isStatic⟩
          (staged.storage ctx.self) (tx.warm ctx.self) tx.refund hlen64
        dsimp only at hrun
        rw [if_neg hvalid] at hrun
        rcases hrun with ⟨cost, m', _, hrun_eq⟩
        have hmet := Guarded.metered_of_run
          (step previewRuntimeBytes input ⟨ctx, tx.original ctx.self, isStatic⟩)
          40 (initialState staged tx ctx.self) cost cost
          ⟨.reverted [],
            { machine := m', storage := staged.storage ctx.self, warm := tx.warm ctx.self, refund := tx.refund }⟩
          gas hrun_eq
        unfold runMetered
        rw [hcode_staged, hmet]
        by_cases hgas : cost ≤ gas
        · simp [hgas, observeFrame]
        · simp [hgas, observeFrame]

set_option maxRecDepth 200000 in
/-- Negative-control theorem (`preview_return_changed_to_revert`):
The mutated runtime bytecode `corruptedRuntimeBytes` (where `0xf3` `RETURN` at offset `0x3b`
was mutated to `0xfd` `REVERT`) reverts on valid `identity(42)` call input instead of returning `42`. -/
theorem corruptedPreviewIdentity_rejected :
    let validCalldata : List UInt8 := [0xac, 0x37, 0xee, 0xbb] ++ wordBytes 42#256
    let input : Input := { calldata := validCalldata, value := 0#256 }
    let world : World := { code := fun _ => corruptedRuntimeBytes }
    let frame := executeCall world {} {} input false 40 1000
    frame.status = .reverted ∧ frame.status ≠ .returned := by decide

/-! ## General In-Kernel Artifact Validator Against Parsed Solidity Specs -/

def mkCalldata (selBytes : List UInt8) (args : List Word) : List UInt8 :=
  selBytes ++ (args.map wordBytes).flatten

def probeWords : List Word :=
  [ 0#256,
    1#256,
    2#256,
    7#256,
    42#256,
    255#256,
    256#256,
    0x1234#256,
    addressMask,
    BitVec.ofNat 256 ((1 <<< 255) - 1),
    BitVec.ofNat 256 (1 <<< 255),
    maxWord - 1#256,
    maxWord ]

def validProbesFor : Solidity.Ty → List Word
  | .uint256 | .bytes32 => probeWords
  | .address =>
    [ 0#256, 1#256, 42#256,
      BitVec.ofNat 256 0x9999999999999999999999999999999999999999,
      addressMask ]
  | .bool => [0#256, 1#256]

def invalidProbeFor : Solidity.Ty → Option Word
  | .uint256 | .bytes32 => none
  | .address => some (BitVec.ofNat 256 (1 <<< 160))
  | .bool => some 2#256

def enumerateWithIdx {α : Type} : Nat → List α → List (Nat × α)
  | _, [] => []
  | i, x :: xs => (i, x) :: enumerateWithIdx (i + 1) xs

def buildArgVectors : List Solidity.Param → List (List Word)
  | [] => [[]]
  | [p] => (validProbesFor p.ty).map (fun w => [w])
  | [p1, p2] =>
    let v1 := validProbesFor p1.ty
    let v2 := validProbesFor p2.ty
    (v1.map (fun a => (v2.take 6).map (fun b => [a, b]))).flatten ++
    (v2.map (fun b => [0#256, b])) ++
    (v1.map (fun a => [a, 1#256]))
  | p1 :: p2 :: p3 :: rest =>
    let base1 := (validProbesFor p1.ty).take 4
    let base2 := (validProbesFor p2.ty).take 4
    let base3 := (validProbesFor p3.ty).take 4
    let indexed := enumerateWithIdx 0 rest
    let tailDefaults : List Word := indexed.map (fun (i, p) =>
      match p.ty with
      | .bool => BitVec.ofNat 256 (i % 2)
      | _ => BitVec.ofNat 256 (i + 10))
    let tailAlt : List Word := indexed.map (fun (i, p) =>
      match p.ty with
      | .bool => BitVec.ofNat 256 ((i + 1) % 2)
      | _ => BitVec.ofNat 256 (1000 + 37 * i))
    (base1.map (fun a =>
      (base2.map (fun b =>
        (base3.map (fun c =>
          [a, b, c] ++ tailDefaults)))).flatten)).flatten ++
    [[validProbesFor p1.ty |>.headD 0#256,
      validProbesFor p2.ty |>.headD 0#256,
      validProbesFor p3.ty |>.headD 0#256] ++ tailAlt]

def slotsEqualOn (numSlots : Nat) (s1 s2 : Slots) : Bool :=
  (List.range (numSlots + 2)).all fun idx =>
    let k := BitVec.ofNat 256 idx
    s1 k == s2 k

theorem slotsEqualOn_sound {numSlots : Nat} {s1 s2 : Slots}
    (h : slotsEqualOn numSlots s1 s2 = true) :
    ∀ idx < numSlots + 2, s1 (BitVec.ofNat 256 idx) = s2 (BitVec.ofNat 256 idx) := by
  unfold slotsEqualOn at h
  rw [List.all_eq_true] at h
  intro idx hlt
  have hm : idx ∈ List.range (numSlots + 2) := List.mem_range.mpr hlt
  simpa [beq_iff_eq] using h idx hm

/-- Construct a packed storage configuration assigning non-zero, distinct bitfields to
every packed `StorageEntry` so bitfield reads/writes detect accidental neighbor clobbering. -/
def mkPackedSampleSlots (layout : List Solidity.StorageEntry) (seed : Nat) : Slots :=
  (enumerateWithIdx 0 layout).foldl
    (fun acc (idx, entry) =>
      let val : Word :=
        match entry.ty with
        | .bool => BitVec.ofNat 256 ((idx + seed + 1) % 2)
        | .address =>
          if (idx + seed) % 2 == 0 then addressMask
          else BitVec.ofNat 256 (0x1000000000000000000000000000000000000001 + idx + seed)
        | .uint256 | .bytes32 =>
          if (idx + seed) % 2 == 0 then maxWord - BitVec.ofNat 256 idx
          else BitVec.ofNat 256 (100 + 37 * idx + seed)
      Solidity.writePackedVar acc entry val)
    (fun _ => 0#256)

def sampleContexts : List Context :=
  [ { self := 0x1111111111111111111111111111111111111111#160,
      caller := 0x2222222222222222222222222222222222222222#160,
      origin := 0x3333333333333333333333333333333333333333#160,
      coinbase := 0x4444444444444444444444444444444444444444#160 },
    { self := 0#160,
      caller := BitVec.ofNat 160 ((1 <<< 160) - 1),
      origin := 1#160,
      coinbase := 2#160 } ]

def sampleStoragesFor (spec : Solidity.ContractSpec) : List Slots :=
  let numSlots := spec.storageSlotCount
  if numSlots == 0 then
    [fun _ => 0#256]
  else
    [ fun _ => 0#256,
      mkPackedSampleSlots spec.storageLayout 0,
      mkPackedSampleSlots spec.storageLayout 1 ]

def runtimeFuel (runtimeBytes : List UInt8) : Nat :=
  4 * runtimeBytes.length + 64

def creationFuel (creationBytes : List UInt8) : Nat :=
  4 * creationBytes.length + 64

/-- Semantic agreement predicate between `Contract.Evm.run runtimeBytes` and
`Solidity.evalRuntime` on `(ctx, initSlots, input)`. -/
def RuntimeMatchesOn (runtimeBytes : List UInt8) (spec : Solidity.ContractSpec)
    (ctx : Context) (initSlots : Slots) (input : Input) : Prop :=
  ∃ expectedHalt expectedSlots used minGas finalState,
    Solidity.evalRuntime spec ctx input initSlots = some (expectedHalt, expectedSlots) ∧
    Contract.Evm.run runtimeBytes input
      { ctx := ctx, original := initSlots, isStatic := false }
      (runtimeFuel runtimeBytes) { storage := initSlots } =
      .finished used minGas ⟨expectedHalt, finalState⟩ ∧
    (∀ retBytes, expectedHalt = .returned retBytes →
      ∀ idx < spec.storageSlotCount + 2,
        finalState.storage (BitVec.ofNat 256 idx) = expectedSlots (BitVec.ofNat 256 idx))

/-- Semantic agreement predicate between `Contract.Evm.run creationBytes` and
`Solidity.evalDeployment` on `(ctx, baseSlots, input)`. -/
def CreationMatchesOn (creationBytes runtimeBytes : List UInt8) (spec : Solidity.ContractSpec)
    (ctx : Context) (baseSlots : Slots) (input : Input) : Prop :=
  ∃ expectedHalt expectedSlots used minGas finalState,
    Solidity.evalDeployment spec runtimeBytes ctx input baseSlots =
      some (expectedHalt, expectedSlots) ∧
    Contract.Evm.run creationBytes input
      { ctx := ctx, original := baseSlots, isStatic := false }
      (creationFuel creationBytes) { storage := baseSlots } =
      .finished used minGas ⟨expectedHalt, finalState⟩ ∧
    (∀ retBytes, expectedHalt = .returned retBytes →
      ∀ idx < spec.storageSlotCount + 2,
        finalState.storage (BitVec.ofNat 256 idx) = expectedSlots (BitVec.ofNat 256 idx))

def checkSingleCall (runtimeBytes : List UInt8) (spec : Solidity.ContractSpec)
    (ctx : Context) (initSlots : Slots) (input : Input) : Bool :=
  match Solidity.evalRuntime spec ctx input initSlots with
  | none => false
  | some (expectedHalt, expectedSlots) =>
    let env : Environment := { ctx := ctx, original := initSlots, isStatic := false }
    let initState : State := { storage := initSlots }
    match Contract.Evm.run runtimeBytes input env (runtimeFuel runtimeBytes) initState with
    | .finished _ _ ⟨actualHalt, finalState⟩ =>
      actualHalt == expectedHalt &&
      match actualHalt with
      | .returned _ => slotsEqualOn spec.storageSlotCount finalState.storage expectedSlots
      | .reverted _ => true
    | _ => false

theorem checkSingleCall_sound {runtimeBytes : List UInt8} {spec : Solidity.ContractSpec}
    {ctx : Context} {initSlots : Slots} {input : Input}
    (hok : checkSingleCall runtimeBytes spec ctx initSlots input = true) :
    RuntimeMatchesOn runtimeBytes spec ctx initSlots input := by
  unfold checkSingleCall at hok
  cases heval : Solidity.evalRuntime spec ctx input initSlots with
  | none => simp [heval] at hok
  | some pair =>
    rcases pair with ⟨expHalt, expSlots⟩
    simp only [heval] at hok
    cases hrun : Contract.Evm.run runtimeBytes input
        { ctx := ctx, original := initSlots, isStatic := false }
        (runtimeFuel runtimeBytes) { storage := initSlots } with
    | exhausted => simp [hrun] at hok
    | fault => simp [hrun] at hok
    | unsupported op => simp [hrun] at hok
    | finished used minGas res =>
      rcases res with ⟨actHalt, finalState⟩
      simp only [hrun, Bool.and_eq_true, beq_iff_eq] at hok
      rcases hok with ⟨hhalt, hslots⟩
      subst hhalt
      refine ⟨actHalt, expSlots, used, minGas, finalState, heval, hrun, ?_⟩
      intro retBytes hret
      subst hret
      exact slotsEqualOn_sound hslots

def creationProbeInputs : List Input :=
  [ { calldata := [], value := 0#256 },
    { calldata := [], value := 1#256 } ]

def emptyStorage : Slots := fun _ => 0#256

def checkCreationMatches (creationBytes runtimeBytes : List UInt8)
    (spec : Solidity.ContractSpec) : Bool :=
  creationBytes.length ≤ 49152 &&
  runtimeBytes.length ≤ 24576 &&
  (runtimeBytes.head? != some 0xef) &&
  sampleContexts.all fun ctx =>
    creationProbeInputs.all fun input =>
      match Solidity.evalDeployment spec runtimeBytes ctx input emptyStorage with
      | none => false
      | some (expHalt, expSlots) =>
        let env : Environment := { ctx := ctx, original := emptyStorage, isStatic := false }
        match Contract.Evm.run creationBytes input env (creationFuel creationBytes) { storage := emptyStorage } with
        | .finished _ _ ⟨actHalt, st'⟩ =>
          actHalt == expHalt &&
          match actHalt with
          | .returned _ => slotsEqualOn spec.storageSlotCount st'.storage expSlots
          | .reverted _ => true
        | _ => false

theorem checkCreationMatches_sound {creationBytes runtimeBytes : List UInt8}
    {spec : Solidity.ContractSpec}
    (hok : checkCreationMatches creationBytes runtimeBytes spec = true) :
    creationBytes.length ≤ 49152 ∧
    runtimeBytes.length ≤ 24576 ∧
    runtimeBytes.head? ≠ some 0xef ∧
    ∀ ctx ∈ sampleContexts,
      ∀ input ∈ creationProbeInputs,
        CreationMatchesOn creationBytes runtimeBytes spec ctx emptyStorage input := by
  unfold checkCreationMatches at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] at hok
  rcases hok with ⟨⟨⟨hcLen, hrLen⟩, hhead⟩, hallCtx⟩
  refine ⟨hcLen, hrLen, hhead, ?_⟩
  intro ctx hctx input hinp
  rw [List.all_eq_true] at hallCtx
  have h1 := hallCtx ctx hctx
  rw [List.all_eq_true] at h1
  have h3 := h1 input hinp
  cases heval : Solidity.evalDeployment spec runtimeBytes ctx input emptyStorage with
  | none => simp [heval] at h3
  | some pair =>
    rcases pair with ⟨expHalt, expSlots⟩
    simp only [heval] at h3
    cases hrun : Contract.Evm.run creationBytes input
        { ctx := ctx, original := emptyStorage, isStatic := false }
        (creationFuel creationBytes) { storage := emptyStorage } with
    | exhausted => simp [hrun] at h3
    | fault => simp [hrun] at h3
    | unsupported op => simp [hrun] at h3
    | finished used minGas res =>
      rcases res with ⟨actHalt, st'⟩
      simp only [hrun, Bool.and_eq_true, beq_iff_eq] at h3
      rcases h3 with ⟨hhalt, hsl⟩
      subst hhalt
      refine ⟨actHalt, expSlots, used, minGas, st', heval, hrun, ?_⟩
      intro retBytes hret
      subst hret
      exact slotsEqualOn_sound hsl

def invalidAbiProbeInputs (fn : Solidity.FuncDecl) : List Input :=
  let selBytes := fn.selectorBytes
  let defaults := fn.params.map (fun _ => 0#256)
  (List.range fn.params.length).filterMap fun idx =>
    match fn.params[idx]? with
    | none => none
    | some p =>
      (invalidProbeFor p.ty).map fun badWord =>
        { calldata := mkCalldata selBytes (defaults.set idx badWord), value := 0#256 }

def functionProbeInputs (fn : Solidity.FuncDecl) : List Input :=
  let selBytes := fn.selectorBytes
  let argVecs := buildArgVectors fn.params
  let shortInputs : List Input :=
    if fn.params.isEmpty then []
    else [{ calldata := selBytes ++ List.replicate (32 * fn.params.length - 1) 0, value := 0#256 }]
  let valueInputs : List Input :=
    match argVecs.head? with
    | none => []
    | some firstArgs => [{ calldata := mkCalldata selBytes firstArgs, value := 1#256 }]
  let validInputs : List Input :=
    argVecs.map fun args => { calldata := mkCalldata selBytes args, value := 0#256 }
  shortInputs ++ invalidAbiProbeInputs fn ++ valueInputs ++ validInputs

def dispatchFallbackInputs : List Input :=
  [ { calldata := [], value := 0#256 },
    { calldata := [], value := 1#256 },
    { calldata := [0x00], value := 0#256 },
    { calldata := [0xde, 0xad, 0xbe], value := 0#256 },
    { calldata := [0xff, 0xff, 0xff, 0xfe], value := 0#256 } ]

/-- Full suite of runtime probe inputs exercised by `validateContractArtifact`:
fallback/short/unknown-selector dispatch controls plus per-function ABI/value/argument probes. -/
def allRuntimeProbeInputs (spec : Solidity.ContractSpec) : List Input :=
  dispatchFallbackInputs ++ (spec.functions.map functionProbeInputs).flatten

/-- Top-level in-kernel contract validator checking:
1. Static well-formedness & mutability rules (`spec.wellFormed = true`).
2. Exact Keccak-256 method identifier map (`methodIds` matches `spec.functions`) and unique selectors.
3. Creation bytecode (`creationBytes`) matches `Solidity.evalDeployment` and installs `runtimeBytes`.
4. Runtime bytecode (`runtimeBytes`) matches `Solidity.evalRuntime` across `allRuntimeProbeInputs spec`
   (empty/short/unknown dispatch, ABI validation, value guards, checked/unchecked arithmetic, and
   packed multi-slot storage updates). -/
def validateContractArtifact (spec : Solidity.ContractSpec)
    (creationBytes runtimeBytes : List UInt8)
    (methodIds : List (String × List UInt8)) : Bool :=
  let selectorsMatch :=
    methodIds.length == spec.functions.length &&
    spec.functions.all fun fn =>
      match methodIds.find? (fun p => p.1 == fn.signature) with
      | some (_, bytes) => bytes == fn.selectorBytes
      | none => false
  let uniqueSelectors :=
    (spec.functions.map Solidity.FuncDecl.selectorBytes).Nodup
  let runtimeSuiteOk :=
    sampleContexts.all fun ctx =>
      (sampleStoragesFor spec).all fun slots =>
        (allRuntimeProbeInputs spec).all fun input =>
          checkSingleCall runtimeBytes spec ctx slots input
  spec.wellFormed &&
  selectorsMatch &&
  decide uniqueSelectors &&
  checkCreationMatches creationBytes runtimeBytes spec &&
  runtimeSuiteOk

/-- Soundness theorem for `validateContractArtifact`: whenever `validateContractArtifact`
returns `true`:
1. `spec.wellFormed = true` (static mutability/uniqueness/no-shadowing invariants hold).
2. Creation bytecode satisfies EIP-3860 (`≤ 49152`), and runtime bytecode satisfies
   EIP-170 (`≤ 24576`) and EIP-3541 (`head? ≠ some 0xef`).
3. Every declared method's 4-byte selector equals its proved Keccak-256 selector from
   `Contract.Export.Keccak`, and all selectors are pairwise distinct.
4. For every sampled `(ctx, input)` creation probe on fresh EIP-684 empty storage,
   `Contract.Evm.run creationBytes` halts in exact agreement with `Solidity.evalDeployment`
   (including packed storage slots).
5. For every sampled `(ctx, initSlots, input)` in `allRuntimeProbeInputs spec`,
   `Contract.Evm.run runtimeBytes` halts in exact agreement with `Solidity.evalRuntime`
   (including packed storage slots on return and rollback on revert). -/
theorem validateContractArtifact_sound (spec : Solidity.ContractSpec)
    (creationBytes runtimeBytes : List UInt8)
    (methodIds : List (String × List UInt8))
    (hok : validateContractArtifact spec creationBytes runtimeBytes methodIds = true) :
    spec.wellFormed = true ∧
    creationBytes.length ≤ 49152 ∧
    runtimeBytes.length ≤ 24576 ∧
    runtimeBytes.head? ≠ some 0xef ∧
    (spec.functions.map Solidity.FuncDecl.selectorBytes).Nodup ∧
    (∀ fn ∈ spec.functions,
      ∃ bytes, (fn.signature, bytes) ∈ methodIds ∧ bytes = fn.selectorBytes) ∧
    (∀ ctx ∈ sampleContexts,
      ∀ input ∈ creationProbeInputs,
        CreationMatchesOn creationBytes runtimeBytes spec ctx emptyStorage input) ∧
    (∀ ctx ∈ sampleContexts,
      ∀ initSlots ∈ sampleStoragesFor spec,
        ∀ input ∈ allRuntimeProbeInputs spec,
          RuntimeMatchesOn runtimeBytes spec ctx initSlots input) := by
  unfold validateContractArtifact at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  rcases hok with ⟨⟨⟨⟨hwf, ⟨_, hselAll⟩⟩, hnodup⟩, hcreation⟩, hruntime⟩
  rcases checkCreationMatches_sound hcreation with ⟨hcLen, hrLen, hhead, hcreationSound⟩
  refine ⟨hwf, hcLen, hrLen, hhead, hnodup, ?_, hcreationSound, ?_⟩
  · intro fn hfn
    rw [List.all_eq_true] at hselAll
    have hfnOk := hselAll fn hfn
    cases hfind : methodIds.find? (fun p => p.1 == fn.signature) with
    | none => simp [hfind] at hfnOk
    | some pair =>
      rcases pair with ⟨sig, bytes⟩
      simp only [hfind, beq_iff_eq] at hfnOk
      have hmem := List.mem_of_find?_eq_some hfind
      have hsig : sig = fn.signature := by
        have hp := List.find?_some hfind
        simpa [beq_iff_eq] using hp
      subst hsig
      exact ⟨bytes, hmem, hfnOk⟩
  · intro ctx hctx initSlots hsl input hinp
    rw [List.all_eq_true] at hruntime
    have h1 := hruntime ctx hctx
    rw [List.all_eq_true] at h1
    have h2 := h1 initSlots hsl
    rw [List.all_eq_true] at h2
    exact checkSingleCall_sound (h2 input hinp)

#audit_contract_proof previewSource_parsed_selector
#audit_contract_proof previewCreation_run_exact
#audit_contract_proof previewDeployment_certified
#audit_contract_proof previewRuntime_run_universal
#audit_contract_proof publicPreviewIdentity_certified
#audit_contract_proof corruptedPreviewIdentity_rejected
#audit_contract_proof validateContractArtifact_sound

end Compiler.Validation.Bytecode
