# Verification issue backlog

These are proof/model gaps for the early preview. They are not reports of
demonstrated Solidity miscompilation. Each issue identifies its consuming theorem
and an observable completion criterion. The bodies are retained here so they
remain available in source archives and can be reviewed alongside the proofs.

| GitHub issue | Tracked body | Completion signal |
| --- | --- | --- |
| [#44](https://github.com/okcontract/oksolc/issues/44) | [Anonymous empty slices](01-empty-slice.md) | The actual empty argument view reaches native update without unsupported rejection |
| [#45](https://github.com/okcontract/oksolc/issues/45) | [Complete native hash producer](02-native-hash.md) | Map consumers use the digest from the composed native execution |
| [#46](https://github.com/okcontract/oksolc/issues/46) | [Rehash/install/retire](03-map-growth.md) | The real owner transition preserves the complete map/graph invariant |
| [#47](https://github.com/okcontract/oksolc/issues/47) | [Production entry](04-production-entry.md) | Actual initialization and callers discharge native find/force premises |

The [preview roadmap](../lean-verification-next-steps.md) places these tasks
alongside artifact coverage work. The [coverage map](../compiler-verification-map.json)
retains formal scope statuses; opening or closing an issue alone does not change
verification status. No new trust assumption is authorized by this backlog.
