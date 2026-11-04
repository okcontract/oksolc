# Preparing verification release evidence

Release evidence belongs to the exact clean commit being published. Historical
acceptance or a green library build cannot replace certificates for current
artifacts. The release receipt summarizes existing gates; it does not introduce
a new proof or establish whole-compiler correctness.

## Before tagging a preview

Commit all preparation changes, use the pinned Zig 0.17.0 and Lean 4.29.0 tools,
and run from the repository root:

```sh
release_evidence_root="$(mktemp -d "${TMPDIR:-/tmp}/oksolc-release-evidence.XXXXXX")"
python3 test/lean/release_verification.py run \
  --output "$release_evidence_root/checks" \
  --lean-bin /path/to/lean-4.29.0/bin
python3 test/lean/release_verification.py bundle \
  --input "$release_evidence_root/checks" \
  --output "$release_evidence_root/compiler-verification.tar.gz"
```

Replace the Lean path with the actual installation, or omit `--lean-bin` if the
pinned binaries are on `PATH`. The runner builds native producers, checks Python
regressions and native proof observations, builds the complete Lean library,
then runs all six artifact corpora and the public preview sequentially. Each
phase has an aggregate 8 GiB process-tree limit; builds/proofs use two workers.
Allow substantial time and disk space for fresh packages. The runner refuses
a dirty checkout or an output directory inside it. Do not edit source inputs
or rebuild tools during acceptance.

`release-run.json` must say `passed`. Bundling independently requires successful
receipts for `models`, `words`, `graphs`, `graph_failures`, `functions`, `contracts`,
`storage`, and `preview`, all at the same commit/tree. Each artifact report must
cover every requested case and batch, rejected semantic controls, fresh package
construction, and fresh kernel replay. Changed evidence, mixed revisions,
missing profiles, and resource failures reject. The archive contains the
manifest-bound proof sources, packages, audits, diagnostics, and receipts; its
adjacent `.sha256` file identifies the archive.

Attach the archive and checksum to the preview release. Keep the release notes
explicit about the supported domains and remaining assumptions. Do not describe
the model-build receipt as an artifact certificate. If a full corpus fails, keep
the diagnostics and resolve the failure before claiming complete release-gate
acceptance. Never reuse receipts from a different commit.

## GitHub Actions

[Compiler verification](../.github/workflows/verification.yml) runs library and
regression checks separately from artifact jobs. Every ordinary run includes
the word corpus and the public Solidity preview, including its negative control.
Choose **Run workflow → full_artifacts** on the intended release commit to run
the other five corpora too. Each profile gets its own runner, timeout, and
diagnostics; a failed profile does not cancel its siblings.

CI retains evidence for 90 days. For durable retention, publication of a GitHub
release triggers all profiles again at that tag and attaches the complete
archive/checksum only after every job succeeds. This workflow does not create
or publish a release. Its write permission is confined to the final release
attachment job. Evidence uploads do not overwrite existing release assets;
review and remove an obsolete asset explicitly before retrying publication.

Before publishing, inspect the successful manual run for the intended commit.
The later automatic attachment is an additional check, not a substitute for
that pre-release review. Do not advertise a release certificate until its
complete evidence is available. GitHub repository settings may further limit
artifact retention; release assets provide retention independent of CI expiry.

## What to review

- Exact commit/tree, requested source/settings, and creation/runtime identities.
- The theorem statements and admitted language/fork/input domains.
- Logical axioms and the fixed source-admission, host, and model assumptions.
- Complete cases, controls, batches, replay completion, and resource receipts.
- Differences from the previous release; no whole-compiler claim is inferred
  from corpus counts.
