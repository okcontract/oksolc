# Certified Solidity Compilation (`Identity.identity(uint256)`)

This directory contains the reference end-to-end certified compilation artifact
for `Identity.identity(uint256)` together with its semantic negative control.

 Unlike per-test temporary Lean package generators or Python source extractors,
`oksolc-verify` parses the Standard JSON request and Solidity source directly
inside Lean (`Compiler.Validation.Solidity`), derives the 4-byte Keccak-256
selector in Lean (`Contract.Export.Keccak`), verifies SHA-256 request/response
digests, and checks both creation and deployed runtime bytecode on the unified
Cancun EVM machine (`Contract.Evm`).

In addition, `Compiler.Validation.Bytecode` proves universal Lean kernel theorems
over all call values, all calldata buffers (`< 2^64` bytes), all storage maps,
and all gas budgets (`previewDeployment_certified` and
`publicPreviewIdentity_certified`), audited by `#audit_contract_proof` and
replayed from scratch by `leanchecker --fresh`.

## Quick Start

Requires Zig `0.17.0` and Lean `4.29.0`:

```sh
# 1. Build oksolc and the Lean verification CLI + proof library
zig build build-cli -Doptimize=ReleaseFast
(cd lean && lake build Contract Compiler oksolc-verify)
LEAN_PATH=lean/.lake/build/lib/lean leanchecker --fresh Compiler

# 2. Verify fresh oksolc output matches the retained response and passes oksolc-verify
./zig-out/bin/oksolc --standard-json < examples/verification/request.json > /tmp/fresh-response.json
./lean/.lake/build/bin/oksolc-verify standard-json \
  examples/verification/request.json /tmp/fresh-response.json

# 3. Verify the retained positive pair and confirm the corrupted pair is rejected
./lean/.lake/build/bin/oksolc-verify standard-json \
  examples/verification/request.json examples/verification/response.json
! ./lean/.lake/build/bin/oksolc-verify standard-json \
  examples/verification/request.json examples/verification/corrupted-response.json
```

## Included Artifacts

| File | Description |
| --- | --- |
| `Function.sol` | Admitted Solidity source (`Identity.identity(uint256)`) |
| `request.json` | Standard JSON request (`viaIR: true`, optimizer enabled, `cancun`, no CBOR metadata) |
| `response.json` | Production `oksolc` Standard JSON output (`universalPreviewTheorem: true`) |
| `corrupted-response.json` | Consistent creation + runtime mutation replacing `RETURN` (`0xf3`) with `REVERT` (`0xfd`), rejected by `oksolc-verify` and refuted in kernel theorem `corruptedPreviewIdentity_rejected` |

See [`docs/compiler-verification.md`](../../docs/compiler-verification.md) and
[`docs/compiler-verification-boundary.md`](../../docs/compiler-verification-boundary.md)
for architecture details and the exact TCB boundary.
