# Contributing to compiler verification

Read the [assurance levels](../docs/compiler-verification.md#what-a-verification-result-means)
and run the [public example](../examples/verification/README.md) first. A theorem
about a model, source-bound implementation preservation, and a certificate for
one compilation are different results. Choose the result your change advances.

Commands below run from the repository root. Use Lean 4.29.0, Zig 0.17.0 and
Python 3. Supply `--lean-bin /path/to/lean-4.29.0/bin` to proof tools if needed.
Keep output outside the checkout and use a new directory for each run.

## Find the consumer before adding a lemma

| Work | Start here | Follow toward |
| --- | --- | --- |
| Word identities and production rule table | `Compiler/Algebraic/Model.lean`, `Rules.lean`, `Proofs.lean` | Extracted matching, construction and dispatch |
| Source extraction | `extract_compiler.py`, `compiler_ir.py`, `Compiler/Extraction/Correspondence.lean` | The source-bound operation's consumer |
| Normalization and ownership | `Compiler/Extraction/NormalizationMemoryCaller.lean` | `InternerCallerProduction.lean`, then native find/force endpoints |
| Native recursive optimizer | `Compiler/Extraction/InternerNativeFindProduction.lean`, `InternerNativeForceProduction.lean` | Initial facts, caller admission and complete production composition |
| AIR/memory | `Compiler/ZigAir/Control.lean`, `Machine.lean`, `Memory.lean` | Concrete invocation and its compiler caller |
| Graph certificates | `Compiler/Validation/GraphInventory.lean`, `Normalize.lean` | `test/lean/check_compiler_graphs.py` |
| Solidity certificates | `Compiler/Validation/SolidityCall.lean`, `SolidityContract.lean`, `SolidityStorage.lean` | Corresponding `test/lean/check_compiler_*.py` profiles |

Paths in the table are relative to `lean/` unless prefixed with `test/`.
Use the [coverage map](../docs/compiler-verification-map.json) to find the named
obligation, its evidence roots, assumptions and gate. The
[issue backlog](../docs/verification-issues/README.md) identifies current native
consumers. Historical proof counts and successful fixtures do not establish
universal production coverage.

## Generated files and regeneration

Read a file's header and find its producer before editing it. Generated Lean
programs describe admitted source or AIR; keep manual lemmas in their proof
clients. Do not manually alter generated semantics to make a proof pass.

For the matching/construction example, check freshness without writing files:

```sh
python3 lean/extract_compiler.py --check
python3 lean/extract_cache.py --check
```

After deliberately changing the admitted Zig source or its extractor, regenerate
and inspect the full diff:

```sh
python3 lean/extract_compiler.py
python3 lean/extract_cache.py
git diff -- lean/Compiler/Extraction
```

These two commands regenerate only their own outputs. Other `extract_*.py`
scripts have their own CLI and dependencies; inspect `--help` and the relevant
gate rather than assuming one command regenerates the project.
`extract_compiler.py` also emits the typed IR through `compiler_ir.py`.
`Compiler/Algebraic/Rules.lean` comes from the native rule exporter and has a
separate exact-byte binding check in `test/lean/check_compiler.py`.

AIR-generated files require the pinned instrumented Zig checkout, capture
report, explicit source closure and matching generator. Follow
[zig_air/README.md](zig_air/README.md) and the relevant `generate*.py --help`.
Generate into a new external directory, compare the admitted program and
manifest with the committed output, then update the source and proof clients
together. Ordinary Zig cannot manufacture fresh AIR acceptance evidence.
Do not substitute an old capture or silently omit an unsupported instruction.

## Iterate with focused checks

```sh
proof_work="$(mktemp -d "${TMPDIR:-/tmp}/oksolc-proof-work.XXXXXX")"
python3 lean/prove.py --module Compiler.Algebraic.Proofs \
  --declaration Compiler.Algebraic.production_rules_sound \
  --jobs 2 --output "$proof_work/algebraic"
```

The report is explicitly `developmentOnly`. `--fresh` additionally replays the
module and imports, but still does not certify a compilation. For named native
proof clients and their focused controls:

```sh
python3 test/lean/verify_compiler.py hash --output "$proof_work/hash"
python3 test/lean/verify_compiler.py map-publication --output "$proof_work/map"
```

Run these sequentially. Their default phase is development, not native
acceptance. Hash preflight/acceptance requires `--air-toolchain` with a matching
instrumented build report. The wrapper's `--help` describes phases and limits.

Run the relevant Python regressions when changing admission or proof generation,
for example:

```sh
PYTHONPATH=test/lean python3 -m unittest test_compiler_functions test_preview
python3 test/lean/check_verification_map.py
```

## When complete acceptance is required

| Change | Required evidence before making an acceptance claim |
| --- | --- |
| Local lemma, same endpoint statement | Build the affected clients and audit the affected theorem roots |
| Endpoint statement, interpreter, or ownership semantics | Affected complete proof gate, consumer statement/axiom audit, rejection controls and fresh replay |
| Extractor or bound Zig body | Fresh source binding/regeneration and mutation controls, plus dependent complete gates |
| Artifact admission or proof generation | Complete affected artifact corpus, semantic corruptions, exact bindings, fresh package/audit/replay |
| Release | Clean-commit full procedure in the release guide, including all six artifact profiles and the preview |

The [verification guide](../docs/compiler-verification.md) lists gate commands;
the [release procedure](../docs/compiler-verification-release.md) packages their
evidence. Keep the aggregate 8 GiB watchdog and at most four Lean workers across
verification work; the full library and release runner use two. Do not run
unrelated verification gates concurrently in the same checkout. Stop editing
inputs before acceptance: stale source/tool identities must reject.

## Useful bounded first contributions

- Add a missing malformed-input or semantic-corruption control to an existing
  artifact profile. Identify the theorem boundary it protects and demonstrate
  semantic rejection rather than timeout, parser accident, or resource failure.
- Audit one admitted source construct against its Lean evaluator. Document the
  exact grammar, checked/unchecked behavior and rejection boundary before
  proposing an admission extension.
- Improve one endpoint's premise inventory or reproduction instructions, using
  its actual theorem type and current command interface.
- Help with one bounded task in the issue backlog after identifying the consumer
  premise your change will remove.

## Review expectations

State the problem and resulting guarantee, then list the named consumer and
which premise is removed or changed. Explain all remaining input-domain, host,
source-admission and model-adequacy assumptions. Include commands, terminal
status and retained evidence identities; label historical or development-only
results accurately.

Retain ordinary OOM and exact reached failure states. Unsupported observations,
incomplete fuel, and violated contracts must not become successful results.
An ordinary-result implication needs separate admission/progress reasoning;
finite examples do not establish native termination. Preserve non-vacuous ABI
witnesses and full dispatch/deployment binding for artifact certificates.

Do not add `sorry`, extra axioms, native-evaluation shortcuts, unchecked semantic
oracles, or disabled controls. Changes to the fixed trust boundary require an
explicitly reviewed boundary-version change. Prefer a small consumer-facing
improvement over broad reorganization of proof files.
