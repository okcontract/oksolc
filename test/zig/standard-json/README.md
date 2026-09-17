# Frozen `solc` compatibility corpus

`corpus.json` identifies the compatibility inputs and the byte-exact reference
outputs captured from `solc 0.8.36 --standard-json`. Each reference output is
checked into `expected/` and pinned by its SHA-256 digest in the manifest. The
manifest commits those digests to a deterministic Keccak-256 Merkle root, also
recorded in `merkle-root.txt` as a hexadecimal digest.

`zig build compatibility-check` compiles the inputs with the clean Zig
dispatcher and compares the resulting bytes with this frozen corpus. It is
part of `zig build test` and does not execute or download `solc`.

Maintainers can audit the provenance of the five frozen outputs locally with:

```sh
zig build reference-check -Dbenchmark-reference-solc=/path/to/solc-0.8.36
```

## Intentional trust policy

Required CI intentionally does not download or execute an upstream `solc`
binary. It checks byte compatibility with the frozen outputs and verifies their
individual SHA-256 digests and aggregate Merkle root. This is an integrity gate,
not independent authentication: changing an input, output, digest, or root is a
compatibility-baseline change that requires maintainer review and a local audit
against the original compiler.

The `zsolc-reference-output-v1` tree is defined as follows. Integers are
unsigned 32-bit big-endian values, strings are UTF-8 bytes, and each
`reference_sha256` is decoded to 32 raw bytes before hashing:

```text
leaf(i) = keccak256(
  0x00 || len(version) || version || i || len(case_id) || case_id || output_sha256
)
node(left, right) = keccak256(0x01 || left || right)
```

Leaves follow manifest order. Parent ordering is preserved, and an unpaired
node is duplicated at every level. The version included in every leaf is the
manifest's `reference.required_version`.
