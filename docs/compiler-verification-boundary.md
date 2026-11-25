# Compiler Verification Trust Boundary

This document specifies what the `oksolc` Lean 4 verification suite proves inside
the Lean kernel, what constitutes the Trusted Computing Base (TCB), and what lies
outside the current verification scope.

## What Is Kernel-Proved

1. **Algebraic & `RuleList` Rewrite Soundness (`Compiler.Algebraic`)**:
   - Every rule exported from `src/libevmasm/algebraic_rules.zig` preserves 256-bit
     EVM word semantics for all inputs (`production_rules_sound`,
     `production_expression_sound`), exported opcode byte numbers step identically to
     `Contract.Evm.Machine.step` (`production_binary_opcode_sound`,
     `production_ternary_opcode_sound`, `production_nullary_opcode_sound`), and
     `compiler-rules-export` is diff-checked in CI against `lean/Compiler/Algebraic/Rules.lean`.
   - All 68 procedural rewrite identities in `Compiler.Algebraic.RuleListProofs` hold
     for all 256-bit `BitVec` words and 160-bit execution context addresses.
2. **Translation Validation Soundness (`Compiler.Validation`)**:
   - `Normalize.equivalent_sound`: any two 27-opcode expressions accepted by
     `equivalent` evaluate to the exact same `Word` under all execution contexts and
     variable assignments.
   - `Graph.validate_sound` & `Inventory.certify`: whenever `oksolc-verify graph`
     accepts a `compiler-graph-export` certificate, both DAGs evaluate without
     dangling/forward/cyclic references, every source node's mapped representative ID
     preserves its exact `Word` value, and every CSE cache entry in `ExpressionClasses`
     evaluates to the exact `Word` of its target representative.
   - `Failure.certifySweep`: whenever `oksolc-verify graph-failure` accepts an
     allocation-cut sweep, every `FailingAllocator` cut `0 .. N - 1` leaves a
     semantically sound partial interner prefix and cache, and the baseline run
     completes all source nodes with exact value preservation.
   - `WordBlock.lowerSourceNodes_sound`, `WordBlock.validate_sound`, &
     `WordBlock.validateSource_sound`: whenever `oksolc-verify word` accepts assembled
     Cancun bytecode from `compiler-word-export`, all source DAG nodes (including
     unreachable nodes and Solidity value-first shift operands) lower cleanly and
     executing `code ++ [STOP]` on `Contract.Evm.Machine` from `pc = 0` halts cleanly
     with the exact `WordBlock.evalSource` result pushed atop the preserved caller
     parameter stack and exact gas accounting under `runMetered`.
3. **EVM Frame Conservation, Meta-Specifications, & Certified Artifacts (`Contract`, `Compiler`)**:
   - `executeCall_conserves_total`, `executeCreation_conserves_total`,
     `executeCall_nonreturned_preserves_world`, &
     `executeCreation_nonreturned_preserves_world`: value transfers never create or
     destroy Ether, and any non-returned frame rolls back staged transfers, nonces, and
     storage mutations (`Contract/MetaSpecs.lean`).
   - `previewDeployment_certified` & `publicPreviewIdentity_certified`: universal
     deployment and runtime execution theorems for `examples/verification/Function.sol`
     over all call values, all calldata buffers (`< 2^64` bytes), all storage states,
     and all gas budgets, paired with kernel refutation of the mutated runtime
     (`corruptedPreviewIdentity_rejected`).
   - `validateContractArtifact_sound`: any Standard JSON contract accepted by
     `oksolc-verify standard-json` satisfies static mutability/no-shadowing well-formedness
     (`spec.wellFormed = true`), EIP-3860 initcode limits, EIP-170 runtime code-size
     limits, EIP-3541 `0xef` prefix rejection, pairwise distinct selectors, exact
     Keccak-256 selector agreement (`Contract.Export.Keccak`), and concrete Cancun EVM
     behavioral agreement across constructor, dispatch, ABI decoding, value guards,
     checked/unchecked arithmetic panics, and tight 32-byte packed storage slots.
   - `Compiler/MetaSpecs.lean`: proves multi-pass DAG composition (`graph_validate_trans`),
     end-to-end DAG + word-block composition (`dag_and_wordblock_compose`), packed storage
     isolation, Solidity operator precedence, RFC 8259 surrogate-pair decoding, and
     concrete negative refutations for unsound rules/graphs/bytecodes/contracts.

## Trusted Computing Base (TCB)

- **Lean 4.29.0 Kernel & `leanchecker`**: Typechecking of `Contract` and `Compiler`,
  enforced with `#audit_contract_proof` (allowing only `propext`, `Classical.choice`,
  `Quot.sound`) and replayed via `leanchecker --fresh Contract` and
  `leanchecker --fresh Compiler`.
- **Lean Semantic Specifications**:
  - `Contract/Primitives.lean`, `Contract/Hex.lean`, `Contract/Yul/Expression.lean`, and
    `Contract/Evm/{Guarded,Machine,World}.lean` (the reference Cancun EVM semantics).
  - `Contract/Export/Keccak.lean` (checked in-kernel against standard NIST/EVM test vectors).
  - `Compiler/Validation/Solidity.lean` (reference lexer, parser, packed storage layout,
    static mutability checker, and ABI/statement evaluator for the admitted Solidity subset).
- **CLI I/O Layer (`Compiler/Validation/Main.lean`)**: File reading, UTF-8 decoding,
  RFC 8259 JSON parsing (with UTF-16 surrogate pairs), and SHA-256 request/response
  binding when running the compiled `oksolc-verify` binary on external JSON files.

## Explicit Non-Claims

- **Not a whole-compiler proof**: `oksolc` in Zig is *not* proved correct for arbitrary
  Solidity inputs. Untrusted compiler outputs are certified per-compilation by
  `oksolc-verify` (for `graph`, `graph-failure`, `word`, and admitted `standard-json`
  contracts), while `Identity.identity(uint256)` additionally carries a universal
  symbolic proof over all inputs.
- **Bounded EVM & Solidity subset**: `Contract.Evm` models single-frame deployment and
  runtime execution for pure/view/payable/storage contracts without nested `CALL`/
  `DELEGATECALL`/`CREATE2` reentrancy, precompiles, blobs, or transaction-level gas
  refunds/coinbase fee settlement. `validateContractArtifact` on general contracts
  outside `publicPreviewIdentity` checks selector/size invariants universally and
  executes a structured matrix of concrete ABI/storage/value/overflow test vectors
  on `Contract.Evm`.
