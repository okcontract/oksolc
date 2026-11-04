# Partial compiler verification — early preview

The optional Lean project verifies selected compiler operations and provides
sound validators for selected compiler artifacts. It does not establish
correctness of the whole Solidity compiler.

Start with the [complete Solidity example](../examples/verification/README.md).
It includes source, settings, retained creation/runtime bytes, a deliberately
corrupted output, and one command that requires both acceptance and semantic
rejection. The [release procedure](compiler-verification-release.md) explains
how to obtain durable evidence for the exact public commit.
For changes to the development, follow the
[verification contributor guide](../lean/CONTRIBUTING.md).

## What a verification result means

| Assurance level | Evidence required | Scope and limits |
| --- | --- | --- |
| Model theorem | Lean proof checking of the declared statement | Establishes a property of the model under its hypotheses; not native correspondence |
| Source-bound implementation proof | Matching source/capture identities, refinement proofs, audits, controls and replay | Selected production operations; unresolved caller and graph premises stay explicit |
| Compilation certificate | Exact source/settings/output binding, sound validation or generated proof, audit and fresh replay | Only the accepted artifact pair and declared input/semantic domain |
| Whole-compiler correctness | Complete pipeline composition or a sufficiently broad artifact route | Open; neither proof counts nor a green build imply it |

The available Zig-to-Lean translation is **restricted and partly trusted**.
`extract_*.py` admits specific source constructs, and `zig_air/` captures and
decodes selected AIR operations. Neither is a general or verified Zig frontend.
New AIR captures need the pinned instrumented Zig toolchain; ordinary Zig is
sufficient for the artifact example. Unsupported source validity, layouts, or
operations reject rather than acquiring a correctness claim.

The [review paper](lean-verification-review.pdf)
([LaTeX](lean-verification-review.tex)) introduces the notation, representative
proof endpoints, and remaining obligations. It records a source-only review at
its stated baseline, not an independent audit or a fresh acceptance run.

## Scope and trust

There are two complementary routes:

- Implementation proofs cover selected algebraic rewrites, constant folding,
  expression interning, argument normalization, ownership and allocation-failure
  paths. Restricted Zig AIR models support native-memory and hash proofs.
- Artifact validators check actual input/output pairs: pure expression graphs,
  failure observations, assembled word expressions, and bounded Solidity
  function, contract and storage fragments. Their soundness theorems bind the
  exact source, settings and emitted bytes admitted by each profile.

Unsupported constructs, failed bindings, exhausted resources and rejected
artifacts never count as verified. A validator may reject correct output.
Passing compiler tests or building the Lean library alone is not a certificate
for a compilation.

The [version 2 trust boundary](compiler-verification-boundary.md) states the
Lean-kernel, Zig/host, native-memory, language-model and admission assumptions.
The [verification map](compiler-verification-map.json) records scoped theorems,
gates and open obligations. Its consistency check does not run those gates or
certify a current artifact. General frontend/backend preservation and complete
native recursive-optimizer correspondence remain open; see the
[preview roadmap](lean-verification-next-steps.md). The
[issue backlog](verification-issues/README.md) identifies concrete consumer
premises and completion criteria.

## Project structure

| Path | Responsibility |
| --- | --- |
| `lean/Compiler/Algebraic` | Production rule table, word model and rewrite proofs |
| `lean/Compiler/Extraction` | Source-bound compiler and ownership models and proofs |
| `lean/Compiler/ZigAir` | Restricted AIR, typed memory and native primitive proofs |
| `lean/Compiler/Validation` | Sound checkers for admitted compiler artifacts |
| `lean/Contract` | Shared semantic models and theorem-dependency auditing |
| `lean/extract_*.py`, `lean/zig_air` | Fail-closed source extraction and AIR capture |
| `lean/common.py`, `lean/environment.py`, `lean/prove.py` | Bounded execution, input/tool identities and development proof checks |
| `src/compiler_verification`, `src/compiler_*_export.zig` | Observations of actual native compiler operations |
| `test/lean` | Proof gates, corruption controls, native fixtures and regression tests |

The shared `Contract` modules are the transitive semantic dependencies of the
compiler proofs.

## Requirements and quick checks

Use Zig 0.17.0 and Lean 4.29.0, pinned in `.zigversion` and
`lean/lean-toolchain`. The Lean package has no external dependencies. Put the
pinned Lean binaries on `PATH`, or pass `--lean-bin /path/to/lean-4.29.0/bin` to
the proof tools. Python 3 is required; corpus extraction also uses `zstd`.

```sh
python3 test/lean/check_verification_map.py
python3 -m unittest discover -s test/lean -p 'test_*.py'
zig build test-compiler-rewrites test-compiler-dispatch-trace \
  test-compiler-graph-export test-compiler-word-export -Doptimize=Debug -j4
cd lean
LEAN_NUM_THREADS=2 lake --quiet --rehash build Compiler
```

`lake build Compiler` explicitly includes every compiler proof and attachment
test module. Use two workers for the complete library to stay within an 8 GiB
process-tree memory budget, and at most four across other verification gates.
Use `test/lean/bounded_run.py` for an aggregate process-tree memory/time limit.
Keep Zig's global cache outside the checkout for cache-enabled compiler tests.

## Development and artifact acceptance

For a focused development check with theorem-dependency auditing:

```sh
proof_evidence="$(mktemp -d "${TMPDIR:-/tmp}/oksolc-proof.XXXXXX")"
python3 lean/prove.py --module Compiler.Algebraic.Proofs \
  --declaration Compiler.Algebraic.production_rules_sound \
  --jobs 4 --output "$proof_evidence/development"
```

Development checks explicitly report `developmentOnly`. Add `--fresh` for
independent kernel replay of that module and its imports; this still does not
certify an emitted artifact.

For an actual word-artifact acceptance gate:

```sh
zig build build-compiler-word-export -Doptimize=ReleaseFast -j4
word_evidence="$(mktemp -d "${TMPDIR:-/tmp}/oksolc-word.XXXXXX")"
python3 test/lean/bounded_run.py --output "$word_evidence/process" \
  --rss-mib 8192 --timeout 1800 -- \
  python3 test/lean/check_compiler_words.py --corpus --jobs 4 \
  --output "$word_evidence/acceptance"
```

The corresponding `check_compiler_graphs.py`,
`check_compiler_graph_failures.py`, `check_compiler_functions.py`,
`check_compiler_contracts.py` and `check_compiler_storage.py` gates cover their
separate admitted profiles. Build `build-compiler-graph-export` for graph gates
and `build-cli` for Solidity gates. Gates bind exact inputs and tools, audit
theorems and their transitive axioms, run semantic corruption controls, and
freshly build and kernel-replay the accepted proof packages including imports.
Every case and batch must pass; incomplete reports are not acceptance.

`verify_compiler.py` provides bounded named native-proof workflows. AIR-backed
acceptance additionally requires the matching captured Zig toolchain report;
an ordinary Zig installation is not a substitute. Generated models and tests
remain usable without making that stronger native-execution claim.

Keep raw run evidence outside the repository. Use
`python3 test/lean/triage_evidence.py <explicit-log-or-report-files> --compact`
to inspect bounded diagnostics, preserving the original files and exit status.
The verification CI runs inventory, regression and library checks alongside
separate word-artifact and public-preview jobs. Its manual `full_artifacts`
option enables all six artifact corpora; published releases require all profiles
before attaching durable evidence. See the [release procedure](compiler-verification-release.md).

## Public starting point

The verification work began in a separate private repository. This preview is
the public starting point; its proof sources, trust boundary, and open obligations
describe the current state. Acceptance evidence must be reproduced for the exact
public commit using the checks above.
