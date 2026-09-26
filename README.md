# oksolc

`oksolc` is a Zig implementation of the Solidity compiler that we built for our
internal use in developing [Chainwall](https://chainwall.org).

Its goal is to provide an alternative implementation of Solidity for development
purposes, allowing faster iteration on the developer experience.

**We don’t consider `oksolc` to be production ready for deploying smart
contracts onchain, and recommend using the original solc compiler for
deployment. That said, we strive to be byte-compatible at this stage with
Solidity 0.8.36. Any deviation in compiler output should be considered a bug and
reported in Issues.**

The supported compilation path is the optimized, via-IR compilation through the
Standard JSON interface.

The project provides:

- `oksolc`, a small command-line interface
- a shared `libsolc`-compatible C ABI and installed `libsolc.h`
- a public Zig module named `solidity`

Note this project was built with AI assistance (using GPT 5.5 then 5.6 Sol) but
under strict human guidance and control, our team having previous experience in
building compilers and in formal verification. We intend to publish the methods
and controls that we used.

## Status and compatibility

The compatibility target is the original Solidity `0.8.36` compiler for Standard
JSON, creation bytecode, diagnostics, and deterministic output.

The `compile` command enables the optimizer with 200 runs. Use `standard-json`
when exact control of compiler settings or output selection is required.

## Requirements

- Zig `0.16.0`
- TypeScript `7.0.2` (`tsc`) and Bun `1.4.2` for CLI builds
- libc and a working C toolchain
- Clang with ASan/UBSan runtimes for `fuzz-json-adapter` and `fuzz` (limited to
  the yyjson adapter for now)
- Python 3 for tests and benchmark orchestration
- `solc` version `0.8.36` for optional reference audits and benchmark
  comparisons

The first Zig build downloads the dependencies declared in `build.zig.zon`.

## Build and install

Build the CLI, shared library, and C header:

```sh
zig build -Doptimize=ReleaseFast
```

The executable is at `zig-out/bin/oksolc`; the library and header are in
`zig-out/lib` and `zig-out/include`. Add `zig-out/bin` to your `PATH` or install
to a different prefix:

```sh
zig build -Doptimize=ReleaseFast --prefix "$HOME/.local"
```

For development, omit `-Doptimize` for Debug mode, or use
`-Doptimize=ReleaseSafe` for an optimized build with runtime safety checks. To
build only the CLI, use `zig build build-cli`.

Distribution builds can strip debug information and select a target:

```sh
zig build -Dtarget=aarch64-macos -Doptimize=ReleaseFast -Dstrip=true \
  --prefix build/macos-arm64
zig build -Dtarget=x86_64-linux-gnu -Doptimize=ReleaseFast -Dstrip=true \
  --prefix build/linux-amd64
```

## Compile contracts

Compile one or more Solidity files and write the Standard JSON result to stdout:

```sh
oksolc compile Contract.sol Library.sol
```

For control over compiler settings and requested artifacts, supply a Standard
JSON request from a file or stdin. Use `-o` to save the result:

```sh
oksolc standard-json request.json
oksolc standard-json - < request.json
oksolc standard-json -o build/output.json request.json
```

For filesystem imports, `--base-path` sets the source lookup root and repeatable
`--include-path` options add library directories (include paths require an
explicit base path).

AS of now, source paths must stay within the configured roots and cannot contain
symlinks.

Independent contract backends can compile in parallel. `--jobs` sets total
concurrency, including the main thread:

```sh
oksolc compile --parallel --jobs 4 Contract.sol Library.sol
```

Add `--progress` for terminal progress, or `--profile-optimizer FILE` to save
compiler timings as JSON. Run `oksolc --help` or `oksolc <command> --help` for
all options.

## Use with Foundry

Point your project’s `foundry.toml` at the built executable and enable the
supported optimized via-IR pipeline:

```toml
[profile.default]
solc = "/absolute/path/to/oksolc/zig-out/bin/oksolc"
via_ir = true
optimizer = true
optimizer_runs = 200
```

Then run `forge build` as usual. Run `forge clean` first if you need to rebuild
artifacts produced by a previous compiler.

To enable parallel compilation for the project, add an `oksolc.toml` alongside
`foundry.toml`:

```toml
parallel = true
jobs = 4
```

## Install project libraries

For projects that manage libraries as Git submodules:

```sh
oksolc install
```

This uses Git to install the submodules needed by `remappings.txt`, including
nested dependencies, at the commits recorded by the repository. Without
`remappings.txt`, it installs all declared submodules; an empty file selects
none.

Git must be on `PATH`. Use `--base-path PATH` to select another project and
`--jobs N` to change the number of concurrent clones (default: 4). Git handles
credentials and checkout conflicts; resolve any conflict and rerun to continue.

## Watch and browse

We implemented a minimalistic web browser that updates as you edit:

```sh
oksolc serve --browse
```

Open `http://127.0.0.1:8080`. The browser provides source navigation, search,
definition links, references, diagnostics, ABI, bytecode, and other compiler
artifacts. Use `--port` to choose another port.

By default, `serve` watches Solidity files in `src/` and their imported
dependencies. It reads `remappings.txt` and recompiles when sources, used
imports, or remappings change. To watch another source directory, set it in
`oksolc.toml`:

```toml
source-path = "contracts"
```

You can also use `--source-path contracts`. Restart the server after changing
`oksolc.toml`.

For a single compilation or an existing Standard JSON request/output pair:

```sh
oksolc browse src/Vault.sol
oksolc browse --request input.json
oksolc browse --request input.json --import-output output.json
```

Compilations are saved in `.oksolc/browser.sqlite`.

Note you should add `.oksolc/` to your project `.gitignore`.

Run `oksolc browse` to reopen saved results. Select an older compilation to
inspect it, or **Follow latest** to return to live updates. Use
`--database FILE` for another location or `--database :memory:` for a temporary
session.

Without `--browse`, `oksolc serve` writes one Standard JSON result per line. You
can also watch a request file and update an output file after each change:

```sh
oksolc watch request.json -o output.json
```

For tool integrations, `oksolc serve --stdio` keeps a compiler session alive and
exchanges Standard JSON messages.

## Configuration and caching

Project settings live in `oksolc.toml`. The project root is the nearest parent
containing that file or a `.git` marker, or the current directory if neither
exists. Commands accepting `--base-path` use that path as the project root.

User defaults live in `$XDG_CONFIG_HOME/oksolc/config.toml`, normally
`~/.config/oksolc/config.toml`. Project settings override user defaults, with
one exception: persistent compiler caching must be enabled in the user
configuration, outside the repository:

```toml
cache = true
```

Every compilation uses the incremental compiler. Long-running `serve` and
`watch` sessions reuse work in memory; persistent caching allows reuse between
processes. Each project’s cache is stored under
`$XDG_CACHE_HOME/oksolc/projects-v2`, normally `~/.cache/oksolc/projects-v2`,
and authenticated with a local key created in the user configuration directory.

Use `--no-cache` or set `cache = false` in `oksolc.toml` to disable persistence.
Browser snapshots are saved separately, so they remain available with caching
off.

Inspect, prune, or remove the current project’s compiler cache:

```sh
oksolc cache stats
oksolc cache prune --max-bytes 8GiB --max-entries 51200
oksolc clean
```

Cache limits can also be set in `oksolc.toml`. The defaults are:

```toml
cache-max-entries = 102400
cache-max-bytes = "16GiB"
cache-busy-timeout-ms = 250
```

## Development

Run tests in Debug and ReleaseSafe, then check formatting and lint:

```sh
zig build test
zig build test -Doptimize=ReleaseSafe
zig build fmt-check
zig build lint
```

[GitHub CI](.github/workflows/ci.yml) runs these checks in Debug and ReleaseSafe
on pushes and pull requests, including the frozen compatibility corpus, CLI
cache lifecycle regressions, and browser type checks. The
[fuzz workflow](.github/workflows/fuzz.yml) runs bounded fuzzing on relevant
changes and a longer campaign every week. Both workflows can also be started
manually from GitHub Actions.

CI validates workflow definitions with actionlint. Run the same check locally
before changing the workflows:

```sh
go run github.com/rhysd/actionlint/cmd/actionlint@v1.7.12 -color
```

`zig build check` compiles the compiler, CLI, and tests without running the
unit-test executables. For browser changes, use:

```sh
zig build typecheck-browser test-browser-types
zig build browser-smoke test-cli test-browser-store -Doptimize=ReleaseSafe
```

The test suite compares against checked-in `solc 0.8.36` outputs. Unoptimized
contract IR is compared as Yul tokens, allowing whitespace and comment changes
from direct tree generation. All other output bytes must match exactly. Run that
check alone, or audit the fixtures against your installed `solc`:

```sh
zig build compatibility-check
zig build reference-check -Dbenchmark-reference-solc=solc
```

See the [compatibility corpus](test/zig/standard-json/README.md) for fixture
details. To run the parser, JSON, and Standard JSON fuzzers, plus the yyjson
adapter under ASan/UBSan:

```sh
zig build fuzz --fuzz=10K -Dadapter-fuzz-runs=10000 -j2
```

## Benchmarks

Run benchmarks on an otherwise idle machine with a native ReleaseFast build.
Reports are written under `build/benchmarks`.

The local suite checks exact Standard JSON output against system `solc`, then
times three contracts:

```sh
zig build benchmark-local -Doptimize=ReleaseFast \
  -Dbenchmark-reference-solc=solc -Dbenchmark-runs=3
```

For focused compiler and optimizer workloads:

```sh
zig build benchmark-zbench -Doptimize=ReleaseFast
```

For incremental compilation, the synthetic edit traces check output
compatibility and record cache metrics:

```sh
zig build benchmark-incremental -Doptimize=ReleaseFast
```

## Repository layout

| Path                | Contents                                             |
| ------------------- | ---------------------------------------------------- |
| `src/cli/`          | CLI and local compiler browser                       |
| `src/libsolidity/`  | Solidity frontend and via-IR code generation         |
| `src/libyul/`       | Yul parser, analysis, code generation, and optimizer |
| `src/libevmasm/`    | EVM assembly and optimization                        |
| `src/libsolc/`      | Standard JSON dispatcher and C ABI                   |
| `src/incremental/`  | Incremental compilation and persistent caching       |
| `src/root.zig`      | Public `solidity` Zig API                            |
| `include/libsolc.h` | Public C header                                      |
| `test/zig/`         | Unit, integration, CLI, and compatibility tests      |
| `test/benchmarks/`  | Benchmark fixtures and launchers                     |
| `build.zig`         | Build, test, and benchmark steps                     |

## License

`oksolc` is licensed under the [GNU General Public License v3.0](LICENSE.txt).
See [THIRD_PARTY_LICENSES.txt](THIRD_PARTY_LICENSES.txt) for dependency notices.
