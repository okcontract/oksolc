# Changelog

## 0.1.5-dev - 2026-09-30

Solidity compatibility target: `0.8.36`.

### Added

- Add official benchmarks for `oksolc`, initially supporting 12 projects.

### Fixed

- libsolidity: A library helper without parameters has no receiver to bind, 
  even when it overloads an applicable member.

## 0.1.4 - 2026-09-30

Solidity compatibility target: `0.8.36`.

### Added

- Independent oksolc versions for the Zig package, public Zig API, and
  `oksolc version`. Solidity-facing CLI and C ABI versions include the product
  version in build metadata.
- `oksolc version --json` for product, Solidity compatibility, and compiler
  build identities, plus version-command help.
- This retrospective changelog and the release procedure in the README.

### Fixed

- Pass compiler build options to the standalone parser fuzz target so it can
  report the new oksolc version and compile in CI.
- Avoid duplicate CI and fuzz runs for pull requests by limiting push triggers
  to `main`.

### Changed

- Disable the optional web browser by default. Enable it with `-Dbrowser=true`;
  ordinary builds no longer require Bun or TypeScript.
- Run Debug unit and ownership tests alongside ReleaseFast compiler interface
  and compatibility checks in parallel CI jobs, avoiding repeated optimized
  test builds. Keep ReleaseSafe fuzzing in its own job. Pushes and pull requests
  share the same steps.

### Performance

- Generate the lexer keyword lookup at compile time and streamline parser
  token classification and Yul dialect setup.
- Index optimizer recursion graph handles and bulk-sort SSA name sets.
- Reuse completed function effect summaries instead of repeating transitive
  call-graph walks.

## 0.1.3 - 2026-09-26

Solidity compatibility target: `0.8.36`.
Merged [#4](https://github.com/okcontract/oksolc/pull/4) at
[`dc89a65`](https://github.com/okcontract/oksolc/commit/dc89a6539f0a551e5e31eec16d32c4026c753a3d).

### Fixed

- Open the cache authentication key directory with the access needed to update
  its permissions.
- Initialize CI cache paths in workflow steps and restore them after Zig setup,
  keeping trusted and pull-request cache locations separate.
- Resolve CLI smoke-test cache paths absolutely.
- Compare unoptimized IR as Yul tokens so direct tree generation can change
  whitespace and comments; retain exact comparisons for other compiler output.

## 0.1.2 - 2026-09-25

Solidity compatibility target: `0.8.36`.
Merged [#3](https://github.com/okcontract/oksolc/pull/3) at
[`80f84dd`](https://github.com/okcontract/oksolc/commit/80f84dd7757df045889a2a51894af0b6d8c812a4).

### Fixed

- Initialize authenticated cache databases atomically and synchronize
  concurrent initialization.
- Flush cache usage records before closing the store.
- Report compiler startup errors to Forge without masking them with broken
  pipe errors.

## 0.1.1 - 2026-09-25

Solidity compatibility target: `0.8.36`.
Merged [#1](https://github.com/okcontract/oksolc/pull/1) at
[`2ef4c47`](https://github.com/okcontract/oksolc/commit/2ef4c47df6d36d1f8dcd35a56b87ce28892f9177).

### Performance

- Lower Solidity code and ABI helpers directly into typed Yul trees, with
  streaming rendering for requested artifacts.
- Cache optimized Yul as owned AST snapshots and reanalyze cached trees without
  reparsing text.
- Reuse optimizer analysis and SSA storage; transfer owned statements,
  expressions, and names through rewrites and stack allocation passes.
- Reclaim EVM backend and common-subexpression scratch storage earlier and
  transfer assembly payloads through optimization passes.
- Stream source snippets, escaped strings, JSON, and assembly into output
  buffers with fewer intermediate allocations.

### Fixed

- Keep published profiler reports and stack diagnostics independently owned,
  and propagate allocation failures instead of publishing incomplete reports.

## 0.1.0 - 2026-09-20

Solidity compatibility target: `0.8.36`.
Initial project import at
[`58e5ed1`](https://github.com/okcontract/oksolc/commit/58e5ed1b8ec37bafd3624968c5f0207f48891635).

### Added

- Initial Zig implementation of the Solidity compiler, targeting optimized
  via-IR compilation through Standard JSON.
- The `oksolc` CLI, a `libsolc`-compatible shared C library, and the public
  `solidity` Zig module.
- Foundry integration through `--version` and `--standard-json`.
- Incremental compiler sessions, optional authenticated persistent caching,
  and bounded parallel compilation.
- Watch and serve commands, a local compiler browser, compiler profiling, and
  project library installation.
- A frozen Solidity compatibility corpus, fuzz targets, and benchmarks.

### Limitations

- Intended for development; not considered production ready for deploying
  contracts onchain. The supported compilation path is optimized via-IR.
