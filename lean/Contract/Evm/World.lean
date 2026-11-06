/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Evm.Machine

/-! Persistent Cancun world state, transaction-wide access/refund state,
balance-checked value transfers with proved Ether conservation, and atomic
call / EIP-161/170/3541/3860 contract-creation frames. -/
namespace Contract.Evm

structure World where
  storage : Address → Slots := fun _ _ => 0#256
  balances : Address → Nat := fun _ => 0
  code : Address → List UInt8 := fun _ => []
  nonces : Address → Nat := fun _ => 0

structure Transaction where
  original : Address → Slots := fun _ _ => 0#256
  warm : Address → Word → Bool := fun _ _ => false
  refund : Int := 0

def transferBalances (balances : Address → Nat) (caller target : Address) (amount : Nat) :
    Address → Nat :=
  fun a =>
    if a = caller then balances a - amount
    else if a = target then balances a + amount
    else balances a

/-- Balance-checked Ether transfer. Unlike saturating `Nat` subtraction,
insufficient caller balance fails cleanly (`none`) and never mints Ether. -/
def World.transfer (world : World) (caller target : Address) (value : Word) : Option World :=
  if value.toNat ≤ world.balances caller then
    if value = 0#256 ∨ caller = target then some world
    else some { world with balances := transferBalances world.balances caller target value.toNat }
  else none

def World.install (world : World) (target : Address) (bytes : List UInt8) : World :=
  { world with code := fun a => if a = target then bytes else world.code a }

def World.store (world : World) (target : Address) (slots : Slots) : World :=
  { world with storage := fun a => if a = target then slots else world.storage a }

def World.prepare (world : World) (target : Address) : World :=
  { world with nonces := fun a => if a = target then 1 else world.nonces a }

def Fresh (world : World) (target : Address) : Prop :=
  world.code target = [] ∧ world.nonces target = 0 ∧ ∀ slot, world.storage target slot = 0#256

def Transaction.commit (tx : Transaction) (target : Address) (state : State) : Transaction :=
  { tx with
    warm := fun a => if a = target then state.warm else tx.warm a,
    refund := state.refund }

inductive Status where
  | returned | reverted | exceptional | unsupported | exhausted
  deriving DecidableEq, Repr

structure Frame where
  status : Status
  bytes : List UInt8
  world : World
  transaction : Transaction
  gasRemaining : Nat

def initialState (world : World) (tx : Transaction) (target : Address) : State :=
  { storage := world.storage target, warm := tx.warm target, refund := tx.refund }

/-- Observe a completed metered frame against `before` (rollback snapshot) and
`staged` (entry-transferred/prepared world). Revert and exceptional halts
restore `before` and `tx` atomically. -/
def observeFrame (before staged : World) (tx : Transaction) (target : Address) :
    Guarded.Metered Result → Frame
  | .finished gas ⟨.returned bytes, state⟩ =>
    ⟨.returned, bytes, staged.store target state.storage, tx.commit target state, gas⟩
  | .finished gas ⟨.reverted bytes, _⟩ =>
    ⟨.reverted, bytes, before, tx, gas⟩
  | .exceptional =>
    ⟨.exceptional, [], before, tx, 0⟩
  | .unsupported _ =>
    ⟨.unsupported, [], before, tx, 0⟩
  | .exhausted =>
    ⟨.exhausted, [], before, tx, 0⟩

/-- Execute a Cancun message-call frame:
1. Static calls with non-zero `input.value` fault immediately.
2. Insufficient caller balance (`balances caller < value`) faults immediately.
3. Transfer is staged before bytecode execution and rolled back on revert/fault. -/
def executeCall (world : World) (tx : Transaction) (ctx : Context)
    (input : Input) (isStatic : Bool) (fuel gas : Nat) : Frame :=
  if isStatic && input.value != 0#256 then
    ⟨.exceptional, [], world, tx, 0⟩
  else match world.transfer ctx.caller ctx.self input.value with
    | none => ⟨.exceptional, [], world, tx, 0⟩
    | some staged =>
      observeFrame world staged tx ctx.self
        (runMetered (staged.code ctx.self) input ⟨ctx, tx.original ctx.self, isStatic⟩
          fuel gas (initialState staged tx ctx.self))

/-- Finish Cancun contract creation with EIP-170 (`≤ 24576`), EIP-3541 (`head ≠ 0xef`),
and `200 * bytes.length` code-deposit gas. Any failure rolls back storage,
nonce preparation, staged value transfer, access warming, and refunds. -/
def finishCreation (before staged : World) (tx : Transaction) (target : Address) :
    Guarded.Metered Result → Frame
  | .finished gas ⟨.returned bytes, state⟩ =>
    if bytes.length ≤ 24576 ∧ bytes.head? ≠ some 0xef ∧ 200 * bytes.length ≤ gas then
      ⟨.returned, bytes, (staged.store target state.storage).install target bytes,
        tx.commit target state, gas - 200 * bytes.length⟩
    else
      ⟨.exceptional, [], before, tx, 0⟩
  | other => observeFrame before staged tx target other

/-- Execute a Cancun contract-creation frame with EIP-3860 (`≤ 49152` initcode),
EIP-161 initial nonce `1`, and staged balance-checked value transfer. -/
def executeCreation (initcode : List UInt8) (world : World) (tx : Transaction)
    (ctx : Context) (_fresh : Fresh world ctx.self) (input : Input) (fuel gas : Nat) : Frame :=
  if initcode.length ≤ 49152 then
    match (world.prepare ctx.self).transfer ctx.caller ctx.self input.value with
    | none => ⟨.exceptional, [], world, tx, 0⟩
    | some staged =>
      finishCreation world staged tx ctx.self
        (runMetered initcode input ⟨ctx, tx.original ctx.self, false⟩
          fuel gas (initialState staged tx ctx.self))
  else
    ⟨.exceptional, [], world, tx, 0⟩

def totalBalance (world : World) (addrs : List Address) : Nat :=
  addrs.foldr (fun a acc => world.balances a + acc) 0

theorem transfer_none_iff_insufficient (world : World) (caller target : Address) (value : Word) :
    world.transfer caller target value = none ↔ world.balances caller < value.toNat := by
  unfold World.transfer
  by_cases h : value.toNat ≤ world.balances caller
  · simp only [h, ↓reduceIte]
    split <;> simp <;> omega
  · simp only [h, ↓reduceIte]
    constructor
    · intro _; omega
    · intro _; trivial

theorem transfer_preserves_other (world world' : World) (caller target other : Address) (value : Word)
    (htr : world.transfer caller target value = some world')
    (hc : other ≠ caller) (ht : other ≠ target) :
    world'.balances other = world.balances other := by
  unfold World.transfer at htr
  by_cases hle : value.toNat ≤ world.balances caller
  · simp only [hle, ↓reduceIte] at htr
    by_cases hz : value = 0#256 ∨ caller = target
    · simp only [hz, ↓reduceIte, Option.some.injEq] at htr
      subst htr; rfl
    · simp only [hz, ↓reduceIte, Option.some.injEq] at htr
      subst htr
      simp [transferBalances, hc, ht]
  · simp [hle] at htr

theorem transfer_conserves_pair (world world' : World) (caller target : Address) (value : Word)
    (hne : caller ≠ target)
    (htr : world.transfer caller target value = some world') :
    world'.balances caller + world'.balances target =
      world.balances caller + world.balances target := by
  unfold World.transfer at htr
  by_cases hle : value.toNat ≤ world.balances caller
  · simp only [hle, ↓reduceIte] at htr
    by_cases hz : value = 0#256 ∨ caller = target
    · simp only [hz, ↓reduceIte, Option.some.injEq] at htr
      subst htr; rfl
    · simp only [hz, ↓reduceIte, Option.some.injEq] at htr
      subst htr
      have htc : target ≠ caller := Ne.symm hne
      simp only [transferBalances, ↓reduceIte, htc]
      omega
  · simp [hle] at htr

private theorem totalBalance_congr_off (w1 w2 : World) (caller target : Address) (addrs : List Address)
    (hnotC : caller ∉ addrs) (hnotT : target ∉ addrs)
    (hoff : ∀ a, a ≠ caller → a ≠ target → w1.balances a = w2.balances a) :
    totalBalance w1 addrs = totalBalance w2 addrs := by
  induction addrs with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.mem_cons, not_or] at hnotC hnotT
    simp only [totalBalance, List.foldr_cons] at ih ⊢
    rw [hoff a (Ne.symm hnotC.1) (Ne.symm hnotT.1), ih hnotC.2 hnotT.2]

private theorem totalBalance_extract (w : World) (x : Address) (addrs : List Address)
    (hnodup : addrs.Nodup) (hx : x ∈ addrs) :
    totalBalance w addrs = w.balances x + totalBalance w (addrs.erase x) := by
  induction addrs with
  | nil => cases hx
  | cons a rest ih =>
    rw [List.nodup_cons] at hnodup
    by_cases hax : a = x
    · subst hax
      simp [totalBalance, List.erase_cons_head]
    · have hmem : x ∈ rest := by
        cases hx with
        | head => exact absurd rfl hax
        | tail _ hm => exact hm
      have herase : (a :: rest).erase x = a :: rest.erase x := by
        simp [beq_iff_eq, hax]
      rw [herase]
      have hih := ih hnodup.2 hmem
      simp only [totalBalance, List.foldr_cons] at hih ⊢
      omega

theorem transfer_conserves_total (world world' : World) (caller target : Address) (value : Word)
    (addrs : List Address) (hnodup : addrs.Nodup)
    (hc : caller ∈ addrs) (ht : target ∈ addrs)
    (htr : world.transfer caller target value = some world') :
    totalBalance world' addrs = totalBalance world addrs := by
  by_cases hct : caller = target
  · subst hct
    unfold World.transfer at htr
    by_cases hle : value.toNat ≤ world.balances caller
    · simp [hle] at htr; subst htr; rfl
    · simp [hle] at htr
  · rw [totalBalance_extract world' caller addrs hnodup hc,
        totalBalance_extract world caller addrs hnodup hc]
    have hnodup1 : (addrs.erase caller).Nodup := hnodup.erase caller
    have ht1 : target ∈ addrs.erase caller :=
      (List.mem_erase_of_ne (Ne.symm hct)).mpr ht
    rw [totalBalance_extract world' target (addrs.erase caller) hnodup1 ht1,
        totalBalance_extract world target (addrs.erase caller) hnodup1 ht1]
    have hnotC : caller ∉ (addrs.erase caller).erase target := by
      intro hm
      have hm1 : caller ∈ addrs.erase caller := List.mem_of_mem_erase hm
      exact List.Nodup.not_mem_erase hnodup hm1
    have hnotT : target ∉ (addrs.erase caller).erase target :=
      List.Nodup.not_mem_erase hnodup1
    have hrem :
        totalBalance world' ((addrs.erase caller).erase target) =
          totalBalance world ((addrs.erase caller).erase target) :=
      totalBalance_congr_off world' world caller target ((addrs.erase caller).erase target) hnotC hnotT
        (fun a hac hat => transfer_preserves_other world world' caller target a value htr hac hat)
    have hpair := transfer_conserves_pair world world' caller target value hct htr
    rw [hrem]
    omega

/-- End-to-end Ether conservation across `executeCall`: regardless of whether the
frame returns, reverts, runs out of gas, or faults, total Ether across any
duplicate-free address set containing `ctx.caller` and `ctx.self` is invariant. -/
theorem executeCall_conserves_total (world : World) (tx : Transaction) (ctx : Context)
    (input : Input) (isStatic : Bool) (fuel gas : Nat)
    (addrs : List Address) (hnodup : addrs.Nodup)
    (hc : ctx.caller ∈ addrs) (hs : ctx.self ∈ addrs) :
    totalBalance (executeCall world tx ctx input isStatic fuel gas).world addrs =
      totalBalance world addrs := by
  unfold executeCall
  split
  · rfl
  · cases htr : world.transfer ctx.caller ctx.self input.value with
    | none => rfl
    | some staged =>
      dsimp only
      cases runMetered (staged.code ctx.self) input ⟨ctx, tx.original ctx.self, isStatic⟩
          fuel gas (initialState staged tx ctx.self) with
      | finished g res =>
        rcases res with ⟨halt, state⟩
        cases halt with
        | returned bytes =>
          dsimp only [observeFrame]
          have hstore : totalBalance (staged.store ctx.self state.storage) addrs =
              totalBalance staged addrs := rfl
          rw [hstore]
          exact transfer_conserves_total world staged ctx.caller ctx.self input.value addrs hnodup hc hs htr
        | reverted _ => rfl
      | exceptional | unsupported _ | exhausted => rfl

/-- End-to-end Ether conservation across `executeCreation`. -/
theorem executeCreation_conserves_total (initcode : List UInt8) (world : World) (tx : Transaction)
    (ctx : Context) (fresh : Fresh world ctx.self) (input : Input) (fuel gas : Nat)
    (addrs : List Address) (hnodup : addrs.Nodup)
    (hc : ctx.caller ∈ addrs) (hs : ctx.self ∈ addrs) :
    totalBalance (executeCreation initcode world tx ctx fresh input fuel gas).world addrs =
      totalBalance world addrs := by
  unfold executeCreation
  split
  · cases htr : (world.prepare ctx.self).transfer ctx.caller ctx.self input.value with
    | none => rfl
    | some staged =>
      dsimp only
      have hprep : totalBalance (world.prepare ctx.self) addrs = totalBalance world addrs := rfl
      cases runMetered initcode input ⟨ctx, tx.original ctx.self, false⟩
          fuel gas (initialState staged tx ctx.self) with
      | finished g res =>
        rcases res with ⟨halt, state⟩
        cases halt with
        | returned bytes =>
          dsimp only [finishCreation]
          split
          · dsimp only
            have hsi : totalBalance ((staged.store ctx.self state.storage).install ctx.self bytes) addrs =
                totalBalance staged addrs := rfl
            rw [hsi, ← hprep]
            exact transfer_conserves_total (world.prepare ctx.self) staged ctx.caller ctx.self input.value addrs hnodup hc hs htr
          · rfl
        | reverted _ => rfl
      | exceptional | unsupported _ | exhausted => rfl
  · rfl

theorem store_other_account (world : World) (target other : Address) (slots : Slots) (hne : other ≠ target) :
    (world.store target slots).storage other = world.storage other := by
  simp [World.store, hne]

theorem revert_rolls_back (before staged : World) (tx : Transaction) (target : Address)
    (gas : Nat) (bytes : List UInt8) (state : State) :
    observeFrame before staged tx target (.finished gas ⟨.reverted bytes, state⟩) =
      ⟨.reverted, bytes, before, tx, gas⟩ := rfl

#audit_contract_proof transfer_none_iff_insufficient
#audit_contract_proof transfer_conserves_total
#audit_contract_proof executeCall_conserves_total
#audit_contract_proof executeCreation_conserves_total

end Contract.Evm
