# verification: preserve the native map invariant through rehash and owner replacement

Existing proofs cover table preparation, probing and selected publication under
explicit invariants. This issue closes the actual owner transition, not only a
temporary-table fixture.

## Evidence and consumer

Start with `lean/Compiler/Extraction/ExpressionMapSearchMemory.lean` and
`lean/Compiler/Extraction/InternerNativeGraph.lean`. The consumer requires the
table/probe invariant and `NativeGraph.Facts` after any reachable growth operation.

## Completion criteria

- Allocate and initialize replacement storage, then migrate every live binding.
- Prove lookup routing and representative values survive collisions, tombstones,
  capacity boundaries, and the exact migration order.
- Install the replacement into the actual owner and retire the old storage.
- Preserve key ownership, caller borrows, layout/lifetime relations, and graph
  facts on success and each ordinary allocation-failure path.
- Use actual reached failure states; do not invent rollback or cleanup.
- Compose the transition into production lookup/publication and recursive
  callers, with source binding, controls, audits and fresh replay.

Endpoint native hash correspondence depends on the native hash producer issue;
the table-transition reasoning can progress independently. Initial invariant
establishment belongs to the production-entry issue. This does not change any
existing fixed host allocation, copy, or free contract.
