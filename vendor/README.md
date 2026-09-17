# Vendored dependencies

Most packages in this directory support the optional `zig build lint` step.
SQLite's official amalgamation is linked into `oksolc` and `libsolc` for the
persistent compiler cache and browser snapshots.

## Provenance

The source archives were downloaded from GitHub over HTTPS on 2026-08-25 and
pinned by immutable commit. SHA-256 values below cover the downloaded archive
bytes, before the local manifest-only patches described below.

| Package | Upstream revision | Archive SHA-256 |
|---|---|---|
| zlinter | `KurtWagner/zlinter@8b10b45d33c684be4f869baf95a37c282e9db750` | `82c1a2322b1b941b4f50880240af2167a178083bf89c41dc6966a9ecf1cd5c5b` |
| ZLS | `zigtools/zls@494486203c3a48927f2383aa3d5ce5fca112186d` | `dcf2d2a0d10001e313592752e9ad44a18cb76c0bf828f6b28af648f519247d76` |
| known-folders | `ziglibs/known-folders@d6d03830968cca6b7b9f24fd97ee348346a6905d` | `969a38a43bfde75ad4a72b0ed639953788d4383f20a235fd7a7ec3a11f664896` |
| diffz | `ziglibs/diffz@b39fe07e7fdbcf56e43ba2890b9f484f16969f90` | `df7454517b746d3782ec662da5c32d44578b02479b23ce59f066259591f2f343` |
| lsp-kit | `zigtools/lsp-kit@b886a2b0d5cee85ecbcc3089b863f7517cc9ff7f` | `11e34ecf050fc888dff416d6bbe4664183b85770bd86eb6ed0d3c632c1bb193b` |

## Local changes

Only dependency manifests are changed:

- `zlinter/build.zig.zon` resolves ZLS from `../zls`;
- `zls/build.zig.zon` resolves its three non-lazy dependencies from sibling
  directories.

ZLS retains its upstream lazy Tracy declaration. Tracy is disabled by the
zlinter build and is neither fetched nor compiled.

Each package retains its upstream `LICENSE`; consolidated notices are in
[THIRD_PARTY_LICENSES.txt](../THIRD_PARTY_LICENSES.txt).

## SQLite provenance

SQLite 3.53.4 was downloaded from the official project over HTTPS on
2026-08-25:

- archive: `https://www.sqlite.org/2026/sqlite-amalgamation-3530400.zip`;
- archive SHA3-256: `628a44cfe82c66aed1ccbbe85a562d2e33ebe64b3288981ed76285612227934e`;
- `sqlite3.c` SHA3-256: `67f423e9ebbbdc473cbc4772c872ee6b89f31fde4ed0279a5c25d5f65c043a16`.

The archive hash and source-file hash match SQLite's download and 3.53.4
release pages. Only `sqlite3.c`, `sqlite3.h`, and `sqlite3ext.h` are retained;
the command-line shell is not vendored. SQLite is dedicated to the public
domain; see `https://www.sqlite.org/copyright.html`.
