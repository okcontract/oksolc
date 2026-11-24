# Security policy

## Supported versions

Security fixes are made on the latest revision of this repository. On the
documented workloads, `oksolc` matched the complete Standard JSON output of solc
`0.8.37`, `0.8.38`, and `0.8.39` with the optimizer and via-IR enabled. See the
[supported targets and compatibility results](README.md#status-and-compatibility).

## Reporting a vulnerability

Please report suspected vulnerabilities privately through the repository's
GitHub **Security** tab using **Report a vulnerability**. Do not open a public
issue before maintainers have had an opportunity to investigate.

Include the smallest reproducible input, the `oksolc` version and build mode,
the target EVM version, compiler settings, actual output, expected output, and
any comparison made with the reference Solidity compiler. Never include live
private keys, secrets, or proprietary contracts.

Issues without a security impact can be filed through the normal issue tracker.

## Notes

Thanks to Hackerbane, that conducted a pro bono audit
[Hackerbane audit report](audits/hb-ar-2026.17-oksolc.html) and 
[sahuang](https://github.com/sahuang) for reporting multiple findings.

Work on formal verification has begun using
[okcontract/zean](https://github.com/okcontract/zean).
