# Security policy

`solidity-zig` is under active development and is not considered production
ready for deploying smart contracts. A compiler discrepancy can change
contract behavior, so treat every generated artifact as untrusted until it has
been independently verified.

## Supported versions

Security fixes are made on the latest revision of this repository. No released
version is currently designated production-safe. The compatibility target is
the compiler version documented in README.md.

## Reporting a vulnerability

Please report suspected vulnerabilities privately through the repository's
GitHub **Security** tab using **Report a vulnerability**. Do not open a public
issue before maintainers have had an opportunity to investigate.

Include the smallest reproducible input, the `oksolc` version and build mode,
the target EVM version, compiler settings, actual output, expected output, and
any comparison made with the reference Solidity compiler. Never include live
private keys, secrets, or proprietary contracts.

Issues without a security impact can be filed through the normal issue tracker.
