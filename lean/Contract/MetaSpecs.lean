/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Check.Axioms
import Contract.Hex
import Contract.Export.Keccak
import Contract.Primitives
import Contract.Yul.Expression
import Contract.Evm.Guarded
import Contract.Evm.Machine
import Contract.Evm.World

/-! Dedicated meta-specifications for the `Contract` base semantics (kept separate
from the base specification modules so reviewers can audit semantic definitions
independently from meta-theoretic sanity checks).

Covers:
1. Primitive roundtrips (`wordBytes` / `bytesWord`, `Memory.write` / `Memory.read`,
   canonical `Hex` odd-length and invalid-digit rejection).
2. FIPS 202 / Keccak-256 test-vector conformity (`hashBytes []` and ERC-20
   `transfer(address,uint256)` selector `0xa9059cbb`).
3. `Contract.Evm.Machine` totality/determinism, `decodeWordOpAt` → `decodeWordOp`
   subsumption, static-mode `SSTORE` rejection, 1024-word stack overflow rejection,
   PUSH-immediate `JUMPDEST` masking, EIP-2200 `2,301`-gas sentry enforcement, and
   quadratic memory-cost monotonicity.
4. `Contract.Evm.World` atomicity on non-returned frames, static value-transfer
   faults, EIP-684 non-empty code / non-zero nonce collision rejection, EIP-3541
   `0xef` prefix rejection, EIP-170 `24,576`-byte runtime size rejection, and
   EIP-3860 `49,152`-byte initcode size rejection. -/
namespace Contract.MetaSpecs

open Contract
open Contract.Yul
open Contract.Evm

/-! ## 1. Primitive & Hex Codec Meta-Properties -/

theorem bytesWord_wordBytes_roundtrip (w : Word) :
    bytesWord (wordBytes w) = w :=
  bytesWord_wordBytes w

theorem memory_read_write_word (m : Memory) (off : Nat) (w : Word) :
    bytesWord ((m.write off (wordBytes w)).read off 32) = w := by
  have hlen : (wordBytes w).length = 32 := wordBytes_length w
  have hrw : (m.write off (wordBytes w)).read off 32 = wordBytes w := by
    simpa [hlen] using Memory.read_write_same m off (wordBytes w)
  rw [hrw]
  exact bytesWord_wordBytes w

theorem hex_odd_length_rejected :
    Hex.decodeBytes? "0xabc" = none ∧ Hex.decodeBytes? "f" = none := by
  decide

theorem hex_invalid_char_rejected :
    Hex.decodeBytes? "0x60zz" = none := by
  decide

/-! ## 2. Keccak-256 Standard Test Vectors -/

/-- Empty-input Keccak-256 digest (`c5d24601...a470`). -/
theorem keccak256_empty_vector :
    Export.Keccak.hashBytes [] =
      [0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c,
       0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0,
       0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b,
       0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70] :=
  Export.Keccak.keccak256_empty

set_option maxRecDepth 200000 in
/-- Canonical ERC-20 `transfer(address,uint256)` 4-byte selector `0xa9059cbb`. -/
theorem keccak256_erc20_transfer_selector :
    (Export.Keccak.hashBytes (Export.Keccak.asciiBytes "transfer(address,uint256)")).take 4 =
      [0xa9, 0x05, 0x9c, 0xbb] := by
  decide

/-! ## 3. EVM Machine Meta-Properties -/

/-- `Contract.Evm.step` is total and deterministic over all inputs and states. -/
theorem step_deterministic (code : List UInt8) (input : Input) (env : Environment)
    (s : State) (r₁ r₂ : Guarded.Step State Result)
    (h₁ : step code input env s = r₁) (h₂ : step code input env s = r₂) :
    r₁ = r₂ :=
  h₁.symm.trans h₂

/-- Bounded-code `decodeWordOpAt` agrees with general `decodeWordOp` and `WordOp.byteWidth`. -/
theorem decodeWordOpAt_agrees_with_decodeWordOp (code : List UInt8) (pc : Nat)
    (op : WordOp) (width : Nat)
    (hd : decodeWordOpAt code pc = some (op, width)) :
    decodeWordOp code pc (code[pc]?.getD 0) = some op ∧ width = op.byteWidth := by
  unfold decodeWordOpAt at hd
  cases hbyte : code[pc]? with
  | none => simp [hbyte] at hd
  | some byte =>
    simp only [hbyte] at hd
    by_cases hpush : 0x60 ≤ byte.toNat ∧ byte.toNat ≤ 0x7f
    · simp only [hpush, and_self, ↓reduceIte] at hd
      split at hd
      · simp only [Option.some.injEq, Prod.mk.injEq] at hd
        rcases hd with ⟨rfl, rfl⟩
        simp [decodeWordOp, hpush, WordOp.byteWidth]
      · cases hd
    · simp only [hpush, ↓reduceIte, Option.map_eq_some_iff] at hd
      rcases hd with ⟨op', hfixed, heq⟩
      injection heq with hop hw
      subst hop hw
      refine ⟨by simp [decodeWordOp, hpush, hfixed], ?_⟩
      unfold decodeFixedWordOp at hfixed
      by_cases h5f : byte.toNat = 0x5f
      · simp [h5f] at hfixed; subst hfixed; rfl
      · simp only [h5f, ↓reduceIte] at hfixed
        by_cases hdup : 0x80 ≤ byte.toNat ∧ byte.toNat ≤ 0x8f
        · simp [hdup] at hfixed; subst hfixed; rfl
        · simp only [hdup, ↓reduceIte] at hfixed
          by_cases hswap : 0x90 ≤ byte.toNat ∧ byte.toNat ≤ 0x9f
          · simp [hswap] at hfixed; subst hfixed; rfl
          · simp only [hswap, ↓reduceIte] at hfixed
            split at hfixed <;> simp at hfixed <;> subst hfixed <;> rfl

/-- `SSTORE` (`0x55`) unconditionally faults in `STATICCALL` (`env.isStatic = true`). -/
theorem sstore_static_faults (input : Input) (ctx : Context) (orig : Slots)
    (key val : Word) (rest : List Word) (mem : Memory) (mw : Nat)
    (storage : Slots) (warm : Word → Bool) (refund : Int) :
    step [0x55] input ⟨ctx, orig, true⟩
      { machine := { pc := 0, stack := key :: val :: rest, memory := mem, memoryWords := mw },
        storage := storage, warm := warm, refund := refund } = .fault := by
  rfl

/-- EIP-2200 gas sentry meta-property: even when `SSTORE` is a dirty/no-op write
costing `100` gas, `runMetered` with `gas = 2300` faults because `guard = 2301 > 2300`,
whereas `gas = 2301` finishes with `2201` gas remaining. -/
theorem sstore_eip2200_sentry_enforced :
    let env : Environment := { isStatic := false }
    let init : State :=
      { machine := { pc := 0, stack := [0#256, 0#256] },
        warm := fun _ => true }
    runMetered [0x55, 0x00] {} env 4 2300 init = .exceptional ∧
    (∃ res, runMetered [0x55, 0x00] {} env 4 2301 init = .finished 2201 res ∧
      res.halt = .returned []) := by
  refine ⟨rfl, _, rfl, rfl⟩

/-- Pushing onto a full 1024-word EVM stack faults instead of exceeding 1024 items. -/
theorem push_at_stack_limit_faults (input : Input) (env : Environment) (s : State)
    (hpc : s.machine.pc = 0) (hlen : s.machine.stack.length = 1024) :
    step [0x5f] input env s = .fault := by
  unfold step
  simp [hpc, decodeWordOp, decodeFixedWordOp, execWordOp, WordOp.evalStack, hlen]

/-- Immediate `0x5b` bytes inside a `PUSH` instruction are never recognized as valid
`JUMPDEST` targets (`[0x60, 0x5b, 0x5b]` has sole `JUMPDEST` at `pc = 2`, not `1`, so
`JUMP` to `1` faults). -/
theorem push_immediate_masks_jumpdest :
    jumpDestinations [0x56, 0x60, 0x5b, 0x5b] = [3] ∧
    step [0x56, 0x60, 0x5b, 0x5b] {} {} { machine := { pc := 0, stack := [2#256] } } = .fault :=
  ⟨by decide, rfl⟩

/-- Quadratic memory gas `memoryCost` is monotonically non-decreasing in word count. -/
theorem memoryCost_mono {w₁ w₂ : Nat} (hle : w₁ ≤ w₂) :
    memoryCost w₁ ≤ memoryCost w₂ := by
  unfold memoryCost
  have hmul : w₁ * w₁ ≤ w₂ * w₂ := Nat.mul_le_mul hle hle
  have hdiv : w₁ * w₁ / 512 ≤ w₂ * w₂ / 512 := Nat.div_le_div_right hmul
  omega

/-! ## 4. EVM World-State Atomicity & Cancun EIP Meta-Properties -/

private theorem observeFrame_nonreturned_preserves (before staged : World) (tx : Transaction)
    (target : Address) (m : Guarded.Metered Result)
    (h : (observeFrame before staged tx target m).status ≠ .returned) :
    (observeFrame before staged tx target m).world = before ∧
    (observeFrame before staged tx target m).transaction = tx := by
  cases m with
  | finished gas res =>
    rcases res with ⟨halt, state⟩
    cases halt with
    | returned bytes => exact absurd rfl h
    | reverted bytes => exact ⟨rfl, rfl⟩
  | exceptional | unsupported _ | exhausted => exact ⟨rfl, rfl⟩

private theorem finishCreation_nonreturned_preserves (before staged : World) (tx : Transaction)
    (target : Address) (m : Guarded.Metered Result)
    (h : (finishCreation before staged tx target m).status ≠ .returned) :
    (finishCreation before staged tx target m).world = before ∧
    (finishCreation before staged tx target m).transaction = tx := by
  cases m with
  | finished gas res =>
    rcases res with ⟨halt, state⟩
    cases halt with
    | returned bytes =>
      unfold finishCreation at h ⊢
      by_cases h1 : bytes.length ≤ 24576
      · by_cases h2 : bytes.head? ≠ some 0xef
        · by_cases h3 : 200 * bytes.length ≤ gas
          · simp [h1, h2, h3] at h
          · simp [h1, h2, h3]
        · simp [h1, h2]
      · simp [h1]
    | reverted bytes => exact ⟨rfl, rfl⟩
  | exceptional | unsupported _ | exhausted => exact ⟨rfl, rfl⟩

/-- Any non-`.returned` `executeCall` outcome leaves both `world` and `transaction`
completely unchanged (full rollback of staged Ether transfer, storage, warm sets, and refunds). -/
theorem executeCall_nonreturned_preserves_world (world : World) (tx : Transaction)
    (ctx : Context) (input : Input) (isStatic : Bool) (fuel gas : Nat)
    (h : (executeCall world tx ctx input isStatic fuel gas).status ≠ .returned) :
    (executeCall world tx ctx input isStatic fuel gas).world = world ∧
    (executeCall world tx ctx input isStatic fuel gas).transaction = tx := by
  unfold executeCall at h ⊢
  by_cases hst : (isStatic && input.value != 0#256) = true
  · rw [if_pos hst]
    exact ⟨rfl, rfl⟩
  · rw [if_neg hst] at h ⊢
    cases htr : world.transfer ctx.caller ctx.self input.value with
    | none => exact ⟨rfl, rfl⟩
    | some staged =>
      rw [htr] at h
      exact observeFrame_nonreturned_preserves world staged tx ctx.self _ h

/-- Any non-`.returned` `executeCreation` outcome leaves both `world` and `transaction`
completely unchanged (rolling back `prepare` nonce `1` and staged Ether transfer). -/
theorem executeCreation_nonreturned_preserves_world (initcode : List UInt8)
    (world : World) (tx : Transaction) (ctx : Context) (input : Input) (fuel gas : Nat)
    (h : (executeCreation initcode world tx ctx input fuel gas).status ≠ .returned) :
    (executeCreation initcode world tx ctx input fuel gas).world = world ∧
    (executeCreation initcode world tx ctx input fuel gas).transaction = tx := by
  unfold executeCreation at h ⊢
  by_cases hpre : (decide (initcode.length ≤ 49152) && canCreateAt world ctx.self) = true
  · rw [if_pos hpre] at h ⊢
    cases htr : (world.prepare ctx.self).transfer ctx.caller ctx.self input.value with
    | none => exact ⟨rfl, rfl⟩
    | some staged =>
      rw [htr] at h
      exact finishCreation_nonreturned_preserves world staged tx ctx.self _ h
  · rw [if_neg hpre]
    exact ⟨rfl, rfl⟩

/-- Static calls carrying non-zero Ether value fault immediately before bytecode execution. -/
theorem executeCall_static_value_faults (world : World) (tx : Transaction)
    (ctx : Context) (calldata : List UInt8) (val : Word) (fuel gas : Nat)
    (hval : val ≠ 0#256) :
    executeCall world tx ctx ⟨calldata, val⟩ true fuel gas =
      ⟨.exceptional, [], world, tx, 0⟩ := by
  simp [executeCall, hval]

/-- EIP-684: contract creation at an address with existing code or non-zero nonce faults. -/
theorem executeCreation_occupied_code_or_nonce_rejects (initcode : List UInt8)
    (world : World) (tx : Transaction) (ctx : Context) (input : Input) (fuel gas : Nat)
    (hocc : world.code ctx.self ≠ [] ∨ world.nonces ctx.self ≠ 0) :
    executeCreation initcode world tx ctx input fuel gas =
      ⟨.exceptional, [], world, tx, 0⟩ := by
  apply executeCreation_collision_rejects
  rcases hocc with hc | hn
  · simp [canCreateAt, hc]
  · simp [canCreateAt, hn]

/-- EIP-3541: `finishCreation` rejects runtime code starting with `0xef` even with ample gas. -/
theorem finishCreation_eip3541_ef_rejected (before staged : World) (tx : Transaction)
    (target : Address) (tail : List UInt8) (gas : Nat) (state : State) :
    finishCreation before staged tx target
      (.finished gas ⟨.returned (0xef :: tail), state⟩) =
      ⟨.exceptional, [], before, tx, 0⟩ := by
  simp [finishCreation]

/-- EIP-170: `finishCreation` rejects runtime code exceeding `24,576` bytes. -/
theorem finishCreation_eip170_oversize_rejected (before staged : World) (tx : Transaction)
    (target : Address) (bytes : List UInt8) (gas : Nat) (state : State)
    (hover : 24576 < bytes.length) :
    finishCreation before staged tx target
      (.finished gas ⟨.returned bytes, state⟩) =
      ⟨.exceptional, [], before, tx, 0⟩ := by
  have hnot : ¬ bytes.length ≤ 24576 := by omega
  simp [finishCreation, hnot]

/-- EIP-3860: `executeCreation` rejects initcode exceeding `49,152` bytes. -/
theorem executeCreation_eip3860_oversize_rejected (initcode : List UInt8)
    (world : World) (tx : Transaction) (ctx : Context) (input : Input) (fuel gas : Nat)
    (hover : 49152 < initcode.length) :
    executeCreation initcode world tx ctx input fuel gas =
      ⟨.exceptional, [], world, tx, 0⟩ := by
  have hnot : ¬ initcode.length ≤ 49152 := by omega
  simp [executeCreation, hnot]

#audit_contract_proof bytesWord_wordBytes_roundtrip
#audit_contract_proof memory_read_write_word
#audit_contract_proof hex_odd_length_rejected
#audit_contract_proof hex_invalid_char_rejected
#audit_contract_proof keccak256_empty_vector
#audit_contract_proof keccak256_erc20_transfer_selector
#audit_contract_proof step_deterministic
#audit_contract_proof decodeWordOpAt_agrees_with_decodeWordOp
#audit_contract_proof sstore_static_faults
#audit_contract_proof sstore_eip2200_sentry_enforced
#audit_contract_proof push_at_stack_limit_faults
#audit_contract_proof push_immediate_masks_jumpdest
#audit_contract_proof memoryCost_mono
#audit_contract_proof executeCall_nonreturned_preserves_world
#audit_contract_proof executeCreation_nonreturned_preserves_world
#audit_contract_proof executeCall_static_value_faults
#audit_contract_proof executeCreation_occupied_code_or_nonce_rejects
#audit_contract_proof finishCreation_eip3541_ef_rejected
#audit_contract_proof finishCreation_eip170_oversize_rejected
#audit_contract_proof executeCreation_eip3860_oversize_rejected

end Contract.MetaSpecs
