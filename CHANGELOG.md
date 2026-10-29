# Changelog

## 0.2.4 - Unreleased

Solidity compatibility target: `0.8.36`.

### Fixed

- Point CLI help to the current repository and use the `oksolc` name in project
  documentation, build errors, and benchmark help and diagnostics
  ([#42](https://github.com/okcontract/oksolc/issues/42)).

## 0.2.3 - 2026-10-27

Solidity compatibility target: `0.8.36`.

### Changed

- Upgrade the optional web browser's Bun requirement to `1.4.4`.

### Performance

- Memoize unsuccessful dependency-path searches to avoid repeatedly traversing
  shared import subgraphs, preserving deterministic path selection and behavior
  within strongly connected components.

### Fixed

- Reject same-session recursive compilation from backend worker progress
  callbacks, preventing deadlocks while preserving unrelated concurrent callers
  and compilation through other sessions.
- Prevent `watch` from overwriting its input through relative, absolute, or
  directory aliases of the output path.
- Release cloned rational storage when constant conversion produces no value.
- Prevent reduced Yul constant-search budgets from underflowing after recursive
  calls exhaust the remaining steps.
- Validate every alternating benchmark sample, rejecting zero-exit compiler
  errors, malformed or empty output, and missing artifacts. Record output
  digests and check artifact manifests with isolated configuration and cache
  directories.
- Include the full memory expansion cost of both accessed ranges in `MCOPY`
  gas estimates.

### Compatibility

- `MCOPY` gas estimates correct an underestimate in solc 0.8.36. This affects
  reported estimates, not emitted bytecode. See the
  [documented compatibility exceptions](README.md#status-and-compatibility).

## 0.2.2 - 2026-10-20

Solidity compatibility target: `0.8.36`.

### Changed

- Lower-level Zig ABI size and offset queries and
  `ReturnInfo.estimated_return_size` now use `u256` instead of `u32`.
- Direct calls to `compileSolidityStandardJsonAlloc` and
  `compileYulStandardJsonAlloc` now take a `source_errors` slice after
  `loaded_sources`; pass `&.{}` when source resolution produced no diagnostics.

### Fixed

- Preserve ordinary Solidity typing when `settings.experimental` is enabled
  ([#30](https://github.com/okcontract/oksolc/issues/30)).
- Traverse deep inheritance and override graphs without fixed recursion limits,
  and keep the stdio service running after internal compiler failures
  ([#31](https://github.com/okcontract/oksolc/issues/31)).
- Validate each source URL candidate against `keccak256` before accepting it,
  continuing to later URLs after a hash mismatch. Retain hash diagnostics
  alongside callback failures and `StackTooDeep` exceptions in sequential and
  parallel compilation ([#32](https://github.com/okcontract/oksolc/issues/32)).
- Use cycle-aware mapping detection so recursive structs are not misclassified
  as containing mappings ([#33](https://github.com/okcontract/oksolc/issues/33)).
- Materialize string and hexadecimal literals when wrapping fixed bytes in
  user-defined value types ([#34](https://github.com/okcontract/oksolc/issues/34)).
- Allow state variable writes qualified by contract name, including immutables
  and internal function pointers ([#35](https://github.com/okcontract/oksolc/issues/35)).
- Support deleting immutable variables during construction
  ([#36](https://github.com/okcontract/oksolc/issues/36)).
- Match solc 0.8.36 version-range comparisons for large numeric pragma
  components ([#37](https://github.com/okcontract/oksolc/issues/37)).
- Keep ABI calldata sizes, strides, and offsets exact across the 4 GiB boundary
  ([#38](https://github.com/okcontract/oksolc/issues/38)).
- Keep static external-call return size totals exact across the 4 GiB boundary
  ([#39](https://github.com/okcontract/oksolc/issues/39)).

### Compatibility

- ABI calldata layouts and static return size totals above `2^32 - 1` bytes use
  exact `u256` arithmetic instead of reproducing solc 0.8.36's 32-bit wrapping.
  See the [documented compatibility exceptions](README.md#status-and-compatibility).

## 0.2.1 - 2026-10-19

Solidity compatibility target: `0.8.36`.

### Security

- Resolve relative imports in the virtual source namespace, preserving URL-like
  names and existing path components instead of selecting a normalized alias
  (`GHSA-wvq5-vxvm-x7xp`).
- Read project remappings through verified directory and regular-file handles,
  rejecting symlinks and non-regular files to prevent disclosure through
  `remappings.txt`, and retaining the pinned project root during watch updates
  (`GHSA-qhgr-hfq3-p3rr`).
- Reject ambiguous Yul object and data paths with structured diagnostics in every
  declaration order and build mode, preventing dotted names from replacing nested
  runtime code (`GHSA-9q3c-q3gp-jg4h`). This includes ambiguous declaration orders
  accepted by solc 0.8.36; see the [compatibility exceptions](README.md#status-and-compatibility).
  Namespace checks share path components and reuse tree validation throughout
  analysis and optimization, keeping scratch storage proportional to the input.

### Fixed

- Preserve request and source insertion order in original and minimized
  differential-fuzz reproducers so replay uses the same request bytes.
- Apply one compiler-service deadline to request transmission and response
  receipt, and terminate timed-out workers before closing buffered stdin.
- Resolve native array `push` and `pop` overloads together with attached
  functions, matching solc's selection, ambiguity, and argument diagnostics.
- Preserve diagnostic 4731 for zero-parameter attachments declared after array
  calls instead of returning an internal compiler failure.

## 0.2.0 - 2026-10-17

Solidity compatibility target: `0.8.36`.

### Added

- Add stateful incremental fuzzing that compares retained compiler sessions
  byte-for-byte with clean compilation across multi-source edit histories.
- Add an external differential campaign against pinned solc 0.8.36, covering
  in-memory, SQLite, and restarted sessions, corpus mutations, failure
  reduction, and optional semantic execution with evmone.

### Changed

- Require Zig 0.17.0 and migrate the compiler and build system to its current
  standard library and build APIs.
- Use the pinned official `translate-c` package for C bindings and reuse Zig's
  configuration cache across unchanged builds.
- The lower-level Zig `SemanticRevision.initializeDependencyMasks` API now
  returns an owned `incremental.DependencyMaskMarker`. Replace
  `revision.markDependencyUsed(graph, importer, referenced)` with
  `marker.mark(importer, referenced)` and call `marker.deinit()` after collection.
  See the [Zig API migration example](README.md#zig-api-migration-for-020).

### Performance

- Index function-flow lookups and memoize semantic dependency-mask updates.
- Cache stack-slot multiplicities while constructing EVM stack layouts.
  Defer setup for cheap shuffles and hash slot identities in large tables.
- Reuse exact assembly common-subexpression chunks across optimization rounds
  with bounded retained storage.
- Compile the yyjson adapter, yyjson, and SQLite as separate build jobs shared
  by the CLI, library, and tests, allowing C compilation to overlap binding
  generation while respecting Zig's build concurrency limit.

### Fixed

- Format multiline diagnostic highlights independently of closing-line
  indentation.
- Refresh compiler identities at build time, reject concurrent edits during
  header translation or compilation, and recover on unchanged retries.
- Preserve offline package settings, dependency overrides, and linter
  passthrough arguments in nested lint builds.
- Keep allocation-failure tests deterministic across platforms with Zig 0.17's
  allocator.
- Preserve dependency-mask initialization retry state and continue compilation
  when optional optimizer-cache storage runs out of memory.
- Rebind reused source export snapshots after incremental edits, preserving
  imported declarations and `using` aliases across retained sessions.
- Match solc diagnostics for recursive structures, invalid literal and
  fixed-point conversions, invalid UTF-8 conversions, incompatible array-push
  overloads, and abstract `super` lookup.
- Preserve specific call diagnostics for single native or attached candidates,
  while treating combined overload sets and data-location availability like
  solc.
- Wrap oversized storage-layout byte counts instead of overflowing, and return
  diagnostics for Yul AST assertion failures instead of terminating compilation.
- Stabilize Yul optimizer allocation-failure recovery and tolerate absent
  references for unused variables.

## 0.1.6 - 2026-10-12

Solidity compatibility target: `0.8.36`.

### Added

- Hackerbane [HB-AR-2026.17 audit report](audits/hb-ar-2026.17-oksolc.html)
  and [response](audits/hb-ar-2026.17-response.md), with regression coverage
  for the audit fixes.

### Performance

- Reuse unchanged stack preparation between Yul compression and stack-limit
  evasion.
- Keep parallel backend workers supplied with prepared jobs while overlapping
  input preparation and backend compilation.

### Fixed

- Preserve AST ownership during stack-preparation handoff and reject
  incompatible allocators before transferring the AST.
- Apply assembly data in lexical key order, reject prefixed PUSH values, and
  parse assembly tag integers using their declared base.
- Reject CLI source paths containing file or directory symlinks.
- Resolve `super` calls by signature and module overloads by argument types.
- Enforce Solidity member availability and selector purity, and remove
  unavailable dynamic return types on pre-Byzantium EVM targets.
- Count inserted discard calls during Yul pruning, preventing
  `MissingReference` and `ReferenceUnderflow` on later iterations.
- Encode named custom-error arguments in `require` in declaration order while
  preserving argument evaluation order. This intentionally corrects the
  solc 0.8.36 behavior.
- Match solc array-push parameter names, custom-error selector spelling, and
  byte-array pop helper ordering.
- Match solc diagnostics for named type conversions, nonpayable constructors,
  and out-of-range Yul literals.
- Honor Standard JSON output selection for IR and emit `null` layout types
  when no storage types exist.

### Compatibility

- Retain hexadecimal array bounds in IR and omit unused dispatch helpers from
  unoptimized IR. See the [documented compatibility exceptions](README.md#status-and-compatibility)
  for all intentional differences from solc 0.8.36.

## 0.1.5 - 2026-09-30

Solidity compatibility target: `0.8.36`.

### Added

- Add official benchmarks for `oksolc`, initially supporting 12 projects.
- Add OpenZeppelin Contracts 5.6.1 to the external benchmarks and CI.

### Fixed

- libevmasm: Prevent the constant optimizer's recursive search counter from
  underflowing, avoiding runaway compilation and excessive memory use on
  inputs such as OpenZeppelin's `Bytes.toNibbles` masks.
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
