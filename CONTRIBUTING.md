# Contributing

For compiler changes, start with the build, supported pipeline, compatibility
exceptions, and test instructions in [README.md](README.md). Include a minimal
reproducer and the exact source, settings, version, expected behavior, and actual
behavior when reporting a discrepancy. Follow [SECURITY.md](SECURITY.md) for
suspected vulnerabilities.

For the optional Lean development, use the
[verification contributor guide](lean/CONTRIBUTING.md). It identifies the proof
entry points, generated files, focused checks, and acceptance requirements.
The [verification backlog](docs/verification-issues/README.md) contains bounded
tasks with named consumers and completion criteria.

Keep changes focused. Explain the resulting behavior, why it is correct, what
was checked, and any remaining assumptions or unsupported cases. Separate
refactoring from semantic changes when that makes review easier. Preserve the
existing license and source provenance. Do not commit build caches or raw local
evidence; retain reproducible evidence through the documented release process.
