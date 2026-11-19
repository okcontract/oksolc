# A certified Solidity compilation

This example compiles `Identity.identity(uint256)` and certifies its exact
creation and runtime bytes. It also requires rejection of a runtime whose
`RETURN` instruction was replaced by `REVERT`. The creation image is changed
consistently, so the negative control exercises semantics rather than a broken
creation/runtime pairing.

Use Zig 0.17.0, Lean 4.29.0 (including `lake` and `leanchecker`), and Python 3.
Run from the repository root. Ordinary Zig is sufficient; this example does not
use instrumented Zig AIR capture. Allow an 8 GiB process-tree memory budget.

```sh
zig build build-cli -Doptimize=ReleaseFast -j2
preview_evidence="$(mktemp -d "${TMPDIR:-/tmp}/oksolc-preview.XXXXXX")"
python3 test/lean/bounded_run.py --output "$preview_evidence/process" \
  --rss-mib 8192 --timeout 1800 -- \
  python3 test/lean/check_preview.py --corpus --jobs 2 \
  --output "$preview_evidence/certificate"
```

If the pinned Lean installation is not selected on `PATH`, append
`--lean-bin /path/to/lean-4.29.0/bin` to the final command. Each run needs a new
output directory. The first proof build may take several minutes; actual timing
depends on the machine. A failure, interruption, or resource limit is not
acceptance.

Inspect `$preview_evidence/certificate/report.json`. Successful acceptance has:

```json
{
  "status": "passed",
  "accepted": true,
  "example": "publicPreviewIdentity",
  "emittedEvmProof": true,
  "deploymentVerified": true,
  "freshPackage": true,
  "freshKernelReplay": true,
  "wholeCompilerVerified": false
}
```

This is an expected field subset, not a recorded acceptance report. The actual
report must also contain one accepted case, one rejected control named
`preview_return_changed_to_revert`, and no unvalidated cases. The output retains
the actual Standard JSON request/response, generated `Artifact.lean`, compiled
theorem audit, fresh proof package, replay logs, and negative-control diagnostics.

## What is proved

The certificate covers the admitted function's full dispatch, including short
calldata, unknown selectors, nonpayable rejection, and trailing calldata, for
all call values and calldata shorter than `2^64` bytes. It binds deployment to
the exact installed runtime and derives execution outcomes for every execution
gas budget under the model's frame assumptions. It does not establish general
Solidity correctness, a verified source parser, complete EVM semantics, or
transaction admission and fee settlement. See the
[trust boundary](../../docs/compiler-verification-boundary.md).

## Included artifacts

| File | Meaning |
| --- | --- |
| `Function.sol` | The complete source |
| `request.json` | Exact source and settings: optimized via IR, Cancun, no CBOR metadata |
| `response.json` | Retained native output with creation/runtime bytes and selector |
| `corrupted-response.json` | Same source and consistent deployment image, wrong runtime behavior |

The gate checks that a fresh compilation matches the retained creation/runtime
and selector fields and that the committed corruption is exactly the checked
mutation. It rejects drift instead of silently certifying a different example.

To replay the retained positive pair without running the compiler:

```sh
python3 test/lean/check_compiler_functions.py \
  --request examples/verification/request.json \
  --response examples/verification/response.json --jobs 2 \
  --output "$preview_evidence/retained"
```

That command certifies only the supplied pair; the `--corpus` preview command
above additionally runs the mandatory semantic corruption control. To inspect
the deliberately failing proof separately, use `corrupted-response.json` and a
new output directory with the same function gate. Its report must not accept.

When compiler bytes legitimately change, regenerate both retained responses,
review their differences, and rerun the complete preview gate. Do not edit the
expected acceptance status to bypass a failure.
