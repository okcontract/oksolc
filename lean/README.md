# Compiler verification

This optional Lean 4.29.0 project contains partial proofs of compiler operations
and sound validators for selected compiler artifacts. Its Lake targets build
separately from the compiler's Zig targets.

`Compiler/Extraction` contains source-bound optimizer and ownership models,
`Compiler/ZigAir` contains restricted Zig AIR and native-memory models, and
`Compiler/Validation` contains artifact validators. The shared `Contract/`
modules provide only the word, Solidity/Yul/EVM semantics and proof-audit
dependencies used by these proofs.

Install the toolchain pinned in `lean-toolchain`, then build with two workers:

```sh
LEAN_NUM_THREADS=2 lake --quiet --rehash build Compiler
```

A successful build checks the supplied proof terms. It does not by itself
establish source freshness, native behavior, complete compiler verification,
or acceptance of a current compilation. Acceptance also requires the matching
source bindings, theorem audits, negative controls and independent kernel replay.
