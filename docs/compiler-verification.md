# `oksolc` Lean 4 Verification Architecture

`oksolc` pairs its production Zig compiler with an independent, small, zero-`sorry`
Lean 4 verification library and standalone translation-validation executable
(`oksolc-verify`).

## Architectural Principles

1. **Non-vacuous specifications (`∃ value, eval = some value`)**:
   Every validator soundness theorem proves unconditional semantic evaluation and
   equivalence (`Graph.validate_sound`, `Inventory.certify`, `Failure.certifySweep`,
   `WordBlock.validate_sound`, `publicPreviewIdentity_certified`). Postconditions
   are never guarded behind compiler status predicates such as `ordinary result = true`.
2. **Single unified Cancun EVM & balance conservation (`Contract.Evm`)**:
   All straight-line word blocks, contract deployments, and runtime contract calls
   execute on a single raw-byte Cancun EVM (`Contract.Evm.Machine` + `Contract.Evm.World`).
   `World.transfer` enforces `value.toNat ≤ world.balances caller`, with kernel-proved
   Ether conservation across calls and contract creations (`executeCall_conserves_total`,
   `executeCreation_conserves_total`).
3. **Full algebraic & procedural `RuleList` coverage**:
   - `Compiler.Algebraic` exports (`compiler-rules-export`) and proves every rule in
     `src/libevmasm/algebraic_rules.zig` (`production_rules_sound`,
     `production_expression_sound`).
   - `Compiler.Algebraic.RuleListProofs` proves 68 rewrite theorems covering the
     procedural rules in `src/libevmasm/rule_list.zig` across all 27 pure and
     environmental EVM opcodes (`ADD`, `SUB`, `MUL`, `DIV`, `SDIV`, `MOD`, `SMOD`,
     `EXP`, `SIGNEXTEND`, `AND`, `OR`, `XOR`, `BYTE`, `SHL`, `SHR`, `SAR`, `LT`,
     `GT`, `SLT`, `SGT`, `EQ`, `ISZERO`, `NOT`, `ADDMOD`, `MULMOD`, `ADDRESS`,
     `CALLER`, `ORIGIN`, `COINBASE`).
   - `Compiler.Validation.Normalize` implements a canonicalizing normalizer over the
     same 27-opcode Yul/EVM expression algebra and proves `normalize_sound` and
     `equivalent_sound`.
4. **Translation validation of `ExpressionClasses` (`#44`–`#47`)**:
   Rather than embedding brittle platform-specific Zig AIR ASTs, `compiler-graph-export`
   observes the real production `ExpressionClasses` pass (`src/libevmasm/expression_classes.zig`)
   both on normal runs and across deterministic `FailingAllocator` allocation cuts:
   - `Graph.lean` & `GraphInventory.lean` certify topological DAG well-formedness,
     every source representative ID (including 0-ary literals and `ADDRESS`/`CALLER`/
     `ORIGIN`/`COINBASE`), and every CSE hash-table cache entry (`Inventory.certify`).
   - `GraphFailure.lean` certifies every OOM allocation cut `0 .. N - 1` alongside
     the `.complete` baseline (`Failure.certifySweep`).
5. **End-to-end in-Lean Standard JSON & Solidity verification (`oksolc-verify`)**:
   `oksolc-verify` (`lean/Compiler/Validation/Main.lean`) includes an in-Lean
   SHA-256 implementation, RFC 8259 JSON parser, structurally recursive Solidity
   lexer/parser (`Solidity.lean`), proved Keccak-256 selector computation
   (`Contract.Export.Keccak`), and Cancun EVM validator (`Bytecode.lean`). No Python
   script parses Solidity or generates ad-hoc Lean files in the verification TCB.
6. **Strict kernel axiom hygiene**:
   Every exported theorem is checked at compile time by `#audit_contract_proof`
   (`Contract/Check/Axioms.lean`) to depend exclusively on Lean's three standard
   logical axioms (`propext`, `Classical.choice`, `Quot.sound`) — rejecting
   `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`, and custom axioms — and
   replayed from scratch with `leanchecker --fresh Compiler`.

## Module Layout

| Path | Role |
| --- | --- |
| `lean/Contract/Check/Axioms.lean` | `#audit_contract_proof` kernel axiom gate |
| `lean/Contract/Export/Keccak.lean` | In-kernel Keccak-256 permutation, padding, and 4-byte selector theorems |
| `lean/Contract/Primitives.lean` | 256-bit `Word`, 160-bit `Address`, EVM division/shift/signextend/byte/memory primitives |
| `lean/Contract/Yul/Expression.lean` | 27-opcode Yul/EVM expression AST and total evaluator |
| `lean/Contract/Evm/{Guarded,Machine,World}.lean` | Metered Cancun EVM bytecode machine, world state, and Ether conservation proofs |
| `lean/Compiler/Algebraic/{Model,Rules,Proofs,RuleListProofs,Audit}.lean` | Exported algebraic table + 68 procedural `RuleList` soundness theorems |
| `lean/Compiler/Validation/{Normalize,Graph,GraphInventory,GraphFailure}.lean` | 27-opcode normalizer, DAG validator, CSE cache inventory, and OOM-cut sweep certifier |
| `lean/Compiler/Validation/WordBlock.lean` | Cancun straight-line bytecode validator bridged to `Contract.Evm.runMetered` |
| `lean/Compiler/Validation/{Solidity,Bytecode,Audit,Main}.lean` | In-kernel Solidity parser, universal preview contract proofs, and `oksolc-verify` CLI |
| `src/compiler_rules_export.zig` | Exports `src/libevmasm/algebraic_rules.zig` to `lean/Compiler/Algebraic/Rules.lean` |
| `src/compiler_graph_export.zig` | Runs production `ExpressionClasses` and `FailingAllocator` sweeps on JSON DAGs |
| `src/compiler_word_export.zig` | Runs production `ExpressionClasses` + Cancun `Assembly` on admitted word expressions |

## Issues Fixed Relative to PR `#48`

1. **Eliminated vacuous `ordinary result = true` wrappers**: `#48` guarded its interner
   postconditions behind `ordinary result = true` and mapped empty byte slices
   (every 0-ary literal and environmental opcode) to `.outOfMemory ∨ .unsupported`.
   Here, 0-ary literals and `ADDRESS`/`CALLER`/`ORIGIN`/`COINBASE` are first-class
   nodes certified unconditionally by `Inventory.certify` and `Failure.certifySweep`.
2. **Eliminated 172k LOC of generated `zig_air` & 38 Python extractors**: Replaced
   1,440 `.lean` files and `aarch64-macos`-locked AIR dumps (`sourceValidityConditionsPreserved = false`)
   with 18 compact, human-auditable `.lean` files (~6.5k LOC total) that work identically
   on Linux and macOS.
3. **Fixed `World.transfer` Ether creation bug**: `#48` subtracted caller balance with
   saturating `Nat` subtraction while unconditionally adding `value.toNat` to target
   balance. `Contract.Evm.World.transfer` returns `none` when `balances caller < value.toNat`
   and proves `transfer_conserves_total`, `executeCall_conserves_total`, and
   `executeCreation_conserves_total`.
4. **Closed TCB gaps in Keccak-256 and Solidity parsing**: Added kernel proofs for
   `Contract.Export.Keccak` test vectors and selector bounds, and moved Solidity
   parsing, JSON decoding, and SHA-256 digest verification into `oksolc-verify`.
