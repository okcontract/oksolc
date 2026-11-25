/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Check.Axioms
import Compiler.Algebraic.Proofs
import Compiler.Algebraic.RuleListProofs
import Compiler.Validation.Normalize
import Compiler.Validation.Graph
import Compiler.Validation.GraphInventory
import Compiler.Validation.GraphFailure
import Compiler.Validation.WordBlock
import Compiler.Validation.Solidity
import Compiler.Validation.Bytecode
import Compiler.Validation.Main

/-! Dedicated meta-specifications for the `Compiler` verification stack (kept
separate from the base validator and rule-proof modules so reviewers can inspect
meta-theoretic properties independently from core validators).

Covers:
1. Algebraic rule inventory non-vacuity (`productionRules.length = 50`) and
   negative refutation of non-preserving candidate rewrites (`x - 0 = 0`, `x + 1 = x`).
2. Multi-pass DAG composition: chaining `Validation.validate` across successive
   optimization passes (`g₀ → g₁ → g₂`) preserves exact semantics over all
   contexts and local assignments, plus concrete non-vacuity and forward/cycle
   reference rejection.
3. Word-block translation composition & negative controls: composing
   `Validation.validate` (DAG optimization) with `WordBlock.validate` (bytecode
   emission) yields end-to-end `Contract.Evm.run` preservation; truncated `PUSH`,
   stack-corrupting blocks, and wrong shift-operand bytecodes are rejected.
4. Solidity frontend meta-properties:
   - Exact Zig/Solidity precedence (`1 == 2 & 3` parses as `1 == (2 & 3)`, not
     `(1 == 2) & 3`);
   - Tight 32-byte storage slot packing (`bool` + `address` + `bool` pack into
     slot `0` at offsets `0`, `1`, `21`, while a following `uint256` starts at
     slot `1` offset `0`, with non-interfering `writePackedVar` / `readPackedVar`);
   - Static mutability rejection (`pure` reading state or `msg.sender`, `view`
     writing state, parameter shadowing state variable).
5. End-to-end `Bytecode.validateContractArtifact` acceptance of the canonical
   `Identity` preview artifact and rejection of the corrupted `RETURN → REVERT`
   negative control, plus RFC 8259 UTF-16 surrogate-pair JSON parser properties. -/
namespace Compiler.MetaSpecs

open Contract
open Contract.Yul
open Contract.Evm
open Compiler.Validation

/-! ## 1. Algebraic Rule Inventory Meta-Properties -/

/-- Exact count of exported production simplification rules in `Compiler.Algebraic.productionRules`. -/
theorem production_rules_count :
    Compiler.Algebraic.productionRules.length = 50 := by
  decide

/-- Negative control for algebraic rules: replacing `x - 0` with `0` (`⟨.sub, .right_zero, .zero⟩`)
is refuted (`¬ Rule.Sound ⟨.sub, .right_zero, .zero⟩`) on counterexample `x = 1#256, y = 0#256`. -/
theorem unsound_algebraic_rule_refuted :
    ¬ Compiler.Algebraic.Rule.Sound ⟨.sub, .right_zero, .zero⟩ := by
  intro hsound
  have h := hsound 1#256 0#256 rfl
  revert h
  decide

/-! ## 2. DAG Normalization & Multi-Pass Composition Meta-Properties -/

/-- Composing two validated DAG optimization passes (`g₀ → g₁` and `g₁ → g₂`)
preserves exact `evaluate` semantics end-to-end (`g₀ → g₂`) for all `ctx` and `locals`. -/
theorem graph_validate_trans (f₁ f₂ : Nat) (g₀ g₁ g₂ : List Node) (r₀ r₁ r₂ : Nat)
    (h₀₁ : validate f₁ g₀ g₁ r₀ r₁ = true)
    (h₁₂ : validate f₂ g₁ g₂ r₁ r₂ = true)
    (ctx : Context) (locals : String → Word) :
    ∃ v, evaluate g₀ r₀ ctx locals = some v ∧ evaluate g₂ r₂ ctx locals = some v := by
  obtain ⟨v₁, he₀, he₁⟩ := validate_sound f₁ g₀ g₁ r₀ r₁ h₀₁ ctx locals
  obtain ⟨v₂, he₁', he₂⟩ := validate_sound f₂ g₁ g₂ r₁ r₂ h₁₂ ctx locals
  rw [he₁] at he₁'
  injection he₁' with hv
  subst hv
  exact ⟨v₁, he₀, he₂⟩

/-- Concrete non-vacuity witness for `Validation.validate`: `x + 0` (nodes
`[input "x", literal 0, add 0 1]`, root `2`) validates against `[input "x"]` (root `0`). -/
theorem graph_validate_add_zero_nonvacuous :
    validate 16 [.input "x", .literal 0, .binary .add 0 1] [.input "x"] 2 0 = true := by
  decide

/-- Negative control: `Validation.validate` rejects `x + 1` vs `x`, and rejects
graphs containing forward/self references even in unreachable dead nodes. -/
theorem graph_validate_rejects_unsound_and_cycles :
    validate 16 [.input "x", .literal 1, .binary .add 0 1] [.input "x"] 2 0 = false ∧
    validate 16 [.input "x", .unary .bitnot 1] [.input "x"] 0 0 = false := by
  decide

/-! ## 3. Word-Block Pass Composition & Negative Refutations -/

/-- End-to-end pass composition: if DAG optimization `rawNodes → optNodes` is
validated by `Validation.validate` on top of `WordBlock.lowerSourceNodes`, and
bytecode emission from `optExpr` is validated by `WordBlock.validate`, then
`Contract.Evm.run` on `code ++ [0x00]` computes the exact Solidity `WordBlock.evalSource`
word on top of the preserved caller parameter stack. -/
theorem dag_and_wordblock_compose (dagFuel wbFuel : Nat)
    (parameters : List String) (rawNodes loweredNodes optNodes : List Node)
    (rawRoot optRoot : Nat) (optExpr : Expression) (code : List UInt8)
    (hlow : WordBlock.lowerSourceNodes parameters rawNodes = some loweredNodes)
    (hdag : validate dagFuel loweredNodes optNodes rawRoot optRoot = true)
    (hexp : expand optNodes optRoot = some optExpr)
    (hwb : WordBlock.validate wbFuel code parameters optExpr = true)
    (input : Input) (env : Environment) (locals : String → Word) (s : State)
    (hpc : s.machine.pc = 0) (hstack : s.machine.stack = parameters.map locals) :
    ∃ result cost,
      WordBlock.evalSource parameters rawNodes rawRoot locals = some result ∧
      Contract.Evm.run (code ++ [0x00]) input env (code.length + 1) s =
        .finished cost cost
          ⟨.returned [], { s with machine := { s.machine with pc := code.length, stack := result :: parameters.map locals } }⟩ := by
  cases hrawExp : expand loweredNodes rawRoot with
  | none => simp [validate, hrawExp] at hdag
  | some rawExpr =>
    have hsrc := WordBlock.lowerSourceNodes_sound parameters rawNodes loweredNodes
      rawRoot rawExpr env.ctx locals hlow hrawExp
    obtain ⟨v, heRaw, heOpt⟩ := validate_sound dagFuel loweredNodes optNodes rawRoot optRoot hdag env.ctx locals
    rw [evaluate_expand, hrawExp] at heRaw
    rw [evaluate_expand, hexp] at heOpt
    simp only [Option.map_some, Option.some.injEq] at heRaw heOpt
    have heqVal : WordBlock.evalExpr env.ctx locals optExpr = WordBlock.evalExpr env.ctx locals rawExpr := by
      simpa [WordBlock.evalExpr, ← heRaw] using heOpt
    obtain ⟨_, cost, hevm, _⟩ :=
      WordBlock.validate_sound wbFuel code parameters optExpr hwb input env locals s hpc hstack
    rw [heqVal] at hevm
    exact ⟨WordBlock.evalExpr env.ctx locals rawExpr, cost, hsrc, hevm⟩

/-- Concrete non-vacuity + shift-order verification for `WordBlock`:
Solidity `x << 1` (`rawNodes = [input "x", literal 1, shl 0 1]`, value first, shift second)
accepts EVM `[DUP1, PUSH1 1, SHL]` (`[0x80, 0x60, 0x01, 0x1b]`, shift on top of stack)
and rejects reversed `[PUSH1 1, DUP2, SHL]` (`[0x60, 0x01, 0x81, 0x1b]`, `1 << x`),
truncated `PUSH2` (`[0x61, 0x01]`), and frame-clobbering `[ADD]` (`[0x01]`). -/
theorem wordblock_shift_order_and_negative_controls :
    (match WordBlock.lowerSourceNodes ["x"] [.input "x", .literal 1, .binary .shl 0 1] >>=
        fun ns => expand ns 2 with
     | some expr =>
       WordBlock.validate 16 [0x80, 0x60, 0x01, 0x1b] ["x"] expr == true &&
       WordBlock.validate 16 [0x60, 0x01, 0x81, 0x1b] ["x"] expr == false
     | none => false) = true ∧
    WordBlock.validate 16 [0x61, 0x01] [] (.literal 1) = false ∧
    WordBlock.validate 16 [0x01] ["x", "y"] (.binary .add (.variable "x") (.variable "y")) = false := by
  decide

/-! ## 4. Solidity Precedence, Packed Storage, & Static Well-Formedness Meta-Properties -/

set_option maxRecDepth 200000 in
/-- Exact Zig/Solidity precedence check: `&` (prec 10) binds tighter than `==` (prec 6),
and `^` (prec 9) binds tighter than `|` (prec 8) and `<` (prec 7). -/
theorem solidity_bitwise_eq_precedence :
    (match Solidity.tokenize "1 == 2 & 3" >>= Solidity.parseExpr 16 with
     | some (expr, []) =>
       expr == .binary .eq (.lit 1#256) (.binary .bitAnd (.lit 2#256) (.lit 3#256))
     | _ => false) = true ∧
    (match Solidity.tokenize "1 < 2 | 3 ^ 4" >>= Solidity.parseExpr 16 with
     | some (expr, []) =>
       expr == .binary .lt (.lit 1#256)
         (.binary .bitOr (.lit 2#256) (.binary .bitXor (.lit 3#256) (.lit 4#256)))
     | _ => false) = true := by
  decide

/-- Tight 32-byte storage packing check: `bool flagA` (1B), `address owner` (20B),
and `bool flagB` (1B) pack into slot `0` at byte offsets `0`, `1`, `21` (22 bytes total),
while `uint256 total` (32B) advances to slot `1` offset `0` (`storageSlotCount = 2`);
writing each packed field preserves its neighbors in slot `0`. -/
theorem solidity_packed_storage_layout_and_isolation :
    let spec : Solidity.ContractSpec :=
      { name := "Packed"
        stateVars :=
          [ ⟨.bool, "flagA", none⟩
          , ⟨.address, "owner", none⟩
          , ⟨.bool, "flagB", none⟩
          , ⟨.uint256, "total", none⟩ ] }
    let eA : Solidity.StorageEntry := ⟨"flagA", .bool, 0, 0⟩
    let eOwner : Solidity.StorageEntry := ⟨"owner", .address, 0, 1⟩
    let eB : Solidity.StorageEntry := ⟨"flagB", .bool, 0, 21⟩
    let eTotal : Solidity.StorageEntry := ⟨"total", .uint256, 1, 0⟩
    let s0 : Slots := fun _ => 0#256
    let s1 := Solidity.writePackedVar s0 eA 1#256
    let s2 := Solidity.writePackedVar s1 eOwner 0xdeadbeef#256
    let s3 := Solidity.writePackedVar s2 eB 1#256
    let s4 := Solidity.writePackedVar s3 eA 0#256
    spec.storageLayout = [eA, eOwner, eB, eTotal] ∧
    spec.storageSlotCount = 2 ∧
    Solidity.readPackedVar s3 eA = 1#256 ∧
    Solidity.readPackedVar s4 eA = 0#256 ∧
    Solidity.readPackedVar s4 eOwner = 0xdeadbeef#256 ∧
    Solidity.readPackedVar s4 eB = 1#256 ∧
    s4 1#256 = 0#256 := by
  refine ⟨by decide, by decide, ?_, ?_, ?_, ?_, rfl⟩ <;> decide

set_option maxRecDepth 200000 in
/-- Static mutability and shadowing negative controls: `Solidity.parseSource`
rejects `pure` functions reading state or `msg.sender`, `view` functions writing
state, and parameters shadowing state variables. -/
theorem solidity_mutability_and_shadowing_rejected :
    (Solidity.parseSource
      "pragma solidity ^0.8.0; contract C { uint256 s; function f() external pure returns (uint256) { return s; } }").isNone = true ∧
    (Solidity.parseSource
      "pragma solidity ^0.8.0; contract C { function f() external pure returns (address) { return msg.sender; } }").isNone = true ∧
    (Solidity.parseSource
      "pragma solidity ^0.8.0; contract C { uint256 s; function f() external view { s = 1; } }").isNone = true ∧
    (Solidity.parseSource
      "pragma solidity ^0.8.0; contract C { uint256 x; function f(uint256 x) external pure returns (uint256) { return x; } }").isNone = true := by
  decide

/-! ## 5. Contract Artifact Validator & RFC 8259 Surrogate-Pair Meta-Properties -/

set_option maxRecDepth 400000 in
set_option maxHeartbeats 1600000 in
/-- Concrete end-to-end non-vacuity and negative refutation for
`Bytecode.validateContractArtifact`: a minimal `Ping` contract (`ping() -> 42`)
is accepted, whereas mutating its `RETURN` (`0xf3`) to `REVERT` (`0xfd`),
omitting its selector from `methodIdentifiers`, or prefixing `0xef` (EIP-3541)
is rejected. -/
theorem bytecode_validator_nonvacuous_and_negative_controls :
    let fn : Solidity.FuncDecl :=
      { name := "ping"
        params := []
        mutability := .pure
        returnTy := some .uint256
        body := [.returnVal (.lit 42#256)] }
    let spec : Solidity.ContractSpec :=
      { name := "Ping"
        functions := [fn] }
    let sel := Solidity.FuncDecl.selectorBytes fn
    -- Runtime (45 bytes, indices 0..44):
    -- 0..8:   34 15 60 08 57 5f 5f fd 5b  (revert if callvalue != 0; JUMPDEST at 8)
    -- 9..15:  60 04 36 10 60 2a 57        (if calldatasize < 4 jump to JUMPDEST at 42 = 0x2a)
    -- 16..25: 5f 35 60 e0 1c 63 <4B sel>  (selector extraction & push)
    -- 26..32: 14 60 21 57 5f 5f fd        (if eq jump to JUMPDEST at 33 = 0x21 else revert)
    -- 33..41: 5b 60 2a 5f 52 60 20 5f f3  (JUMPDEST(33): MSTORE(0, 42); RETURN(0, 32))
    -- 42..45: 5b 5f 5f fd                 (JUMPDEST(42): REVERT(0, 0))
    let runtimeOk : List UInt8 :=
      [ 0x34, 0x15, 0x60, 0x08, 0x57, 0x5f, 0x5f, 0xfd, 0x5b
      , 0x60, 0x04, 0x36, 0x10, 0x60, 0x2a, 0x57
      , 0x5f, 0x35, 0x60, 0xe0, 0x1c, 0x63 ] ++ sel ++
      [ 0x14, 0x60, 0x21, 0x57, 0x5f, 0x5f, 0xfd
      , 0x5b, 0x60, 0x2a, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3
      , 0x5b, 0x5f, 0x5f, 0xfd ]
    let runtimeRevert : List UInt8 :=
      [ 0x34, 0x15, 0x60, 0x08, 0x57, 0x5f, 0x5f, 0xfd, 0x5b
      , 0x60, 0x04, 0x36, 0x10, 0x60, 0x2a, 0x57
      , 0x5f, 0x35, 0x60, 0xe0, 0x1c, 0x63 ] ++ sel ++
      [ 0x14, 0x60, 0x21, 0x57, 0x5f, 0x5f, 0xfd
      , 0x5b, 0x60, 0x2a, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xfd
      , 0x5b, 0x5f, 0x5f, 0xfd ]
    -- Creation (20-byte loader prefix 0..19, runtime payload at offset 20 = 0x14):
    let rlen := UInt8.ofNat runtimeOk.length
    let creationOk : List UInt8 :=
      [ 0x34, 0x15, 0x60, 0x08, 0x57, 0x5f, 0x5f, 0xfd, 0x5b
      , 0x60, rlen, 0x60, 0x14, 0x5f, 0x39, 0x60, rlen, 0x5f, 0xf3, 0xfe ] ++ runtimeOk
    let creationForRevert : List UInt8 :=
      [ 0x34, 0x15, 0x60, 0x08, 0x57, 0x5f, 0x5f, 0xfd, 0x5b
      , 0x60, rlen, 0x60, 0x14, 0x5f, 0x39, 0x60, rlen, 0x5f, 0xf3, 0xfe ] ++ runtimeRevert
    Bytecode.validateContractArtifact spec creationOk runtimeOk [("ping()", sel)] = true ∧
    Bytecode.validateContractArtifact spec creationForRevert runtimeRevert [("ping()", sel)] = false ∧
    Bytecode.validateContractArtifact spec creationOk runtimeOk [] = false ∧
    Bytecode.validateContractArtifact spec creationOk (0xef :: runtimeOk) [("ping()", sel)] = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- RFC 8259 §7 UTF-16 surrogate-pair decoding and lone-surrogate rejection in
`Cli.JsonParser.parse`, plus control-character escaping in `escapeJsonString`. -/
theorem json_surrogate_pairs_and_control_escaping :
    (match Cli.JsonParser.parse "\"\\uD83D\\uDE00\"" with
     | some (.str s) => s.toList == [Char.ofNat 0x1F600]
     | _ => false) = true ∧
    (Cli.JsonParser.parse "\"\\uD83D\"").isNone = true ∧
    (Cli.JsonParser.parse "\"\\uDE00\"").isNone = true ∧
    Cli.JsonParser.escapeJsonString (String.ofList [Char.ofNat 0x01]) = "\\u0001" := by
  decide

#audit_contract_proof production_rules_count
#audit_contract_proof unsound_algebraic_rule_refuted
#audit_contract_proof graph_validate_trans
#audit_contract_proof graph_validate_add_zero_nonvacuous
#audit_contract_proof graph_validate_rejects_unsound_and_cycles
#audit_contract_proof dag_and_wordblock_compose
#audit_contract_proof wordblock_shift_order_and_negative_controls
#audit_contract_proof solidity_bitwise_eq_precedence
#audit_contract_proof solidity_packed_storage_layout_and_isolation
#audit_contract_proof solidity_mutability_and_shadowing_rejected
#audit_contract_proof bytecode_validator_nonvacuous_and_negative_controls
#audit_contract_proof json_surrogate_pairs_and_control_escaping

end Compiler.MetaSpecs
