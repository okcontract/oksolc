# Compiler verification — early preview

This optional Lean 4.29.0 project contains partial proofs of compiler operations
and sound validators for selected compiler artifacts. Its Lake targets build
separately from the compiler's Zig targets.

Start with the [certified Solidity example](../examples/verification/README.md):
one complete source, exact creation/runtime bytes, a fresh proof package, and a
corrupted artifact that must reject. See the
[verification guide](../docs/compiler-verification.md) for the assurance levels,
the [source-review paper](../docs/lean-verification-review.pdf) for the proof
architecture, and the [release procedure](../docs/compiler-verification-release.md)
for evidence tied to a public commit.

| Result | What it establishes | What it does not establish |
| --- | --- | --- |
| Lean model theorem | Its statement under its explicit hypotheses | Correspondence to current native compiler execution |
| Source-bound implementation proof | A selected operation under its admitted source and host contracts | Unproved caller premises or the rest of the compiler |
| Accepted compilation certificate | Preservation for the exact source/settings/artifacts in its declared domain | Other compilations or general Solidity/EVM semantics |
| Whole-compiler correctness | Open | No such claim is made by this preview |

The Zig-to-Lean tooling is **restricted and partly trusted**. Source extractors
and AIR generators reject unsupported constructs; they are not a general or
verified Zig frontend. New native AIR captures require the pinned, instrumented
Zig toolchain. An ordinary Zig installation can build the compiler and run the
public artifact example. Building committed Lean models needs no AIR recapture.

`Compiler/Extraction` contains source-bound optimizer and ownership models,
`Compiler/ZigAir` contains restricted Zig AIR and native-memory models, and
`Compiler/Validation` contains artifact validators. The shared `Contract/`
modules provide only the word, Solidity/Yul/EVM semantics and proof-audit
dependencies used by these proofs.

Install the toolchain pinned in `lean-toolchain`, then run from the repository
root with two workers:

```sh
cd lean
LEAN_NUM_THREADS=2 lake --quiet --rehash build Compiler
```

A successful build checks the supplied proof terms. It does not by itself
establish source freshness, native behavior, complete compiler verification,
or acceptance of a current compilation. Acceptance also requires the matching
source bindings, theorem audits, negative controls and independent kernel replay.
