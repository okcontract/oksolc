# Restricted Zig AIR tooling

These tools connect selected native compiler operations to the Lean models in
`Compiler/ZigAir` and `Compiler/Extraction`. They translate restricted Zig
semantics into Lean models.

`build_toolchain.py` and `patch_toolchain.py` prepare an explicitly supplied Zig
checkout with the reviewed `SemanticExport.zig` and `SemanticValidity.zig`
instrumentation. `capture.py` captures admitted function instances and source
identities. The `generate*.py` tools reject unsupported semantics and produce
the corresponding Lean programs; `link_specializations.py` connects captured
specializations. Use each command's `--help` for its required inputs.

Native AIR acceptance requires the matching captured toolchain report, exact
source and standard-library hashes, supported function instances, proof clients,
corruption controls and fresh kernel replay. An installed, uninstrumented Zig
compiler alone cannot provide that capture. The committed generated models can
be built and their theorems checked without claiming a fresh native capture.

Keep capture archives and run evidence outside the repository. The
[verification guide](../../docs/compiler-verification.md) and
[fixed trust boundary](../../docs/compiler-verification-boundary.md) define the
scope of the resulting claims and the remaining host/native-memory obligations.
