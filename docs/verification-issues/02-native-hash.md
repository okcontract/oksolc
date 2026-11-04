# verification: connect the complete native hash producer to map consumers

This tracks an unclosed implementation correspondence, not missing hash
collision resistance or a demonstrated compiler defect.

## Evidence and consumer

`lean/Compiler/ZigAir/WyhashUpdateAirComplete.lean` proves complete admitted
update invocation with reached failure writes and cleanup. Local hash and typed
memory results do not yet establish the entire native producer call sequence.
The receiver-based consumers are `Facts.lookup_from_receiver` and
`Facts.probe_receiver_then_publish` in
`lean/Compiler/Extraction/ExpressionMapSearchMemory.lean`, alongside the existing
`Facts.lookup_from_local_wyhash` and `Facts.probe_local_wyhash_then_publish`
consumers in `lean/Compiler/Extraction/ExpressionMapWyhash.lean`.

## Completion criteria

- Compose caller context/key preparation, initialization, ordered field updates,
  argument-byte admission, finalization, and cleanup on the same reached state.
- Feed the value produced by that native execution into lookup/publication;
  remove the corresponding supplied-digest/local-runner connection premise.
- Derive byte order, arithmetic budgets, permissions, bounds, separation, and
  source framing at the call site, including empty arguments.
- Preserve OOM prefixes and reject unsupported source-validity conditions.
- Retain exact source/AIR bindings, semantic controls, statement/axiom audits,
  and fresh imported kernel replay for the final consumer.
- Record the removed consumer premise. Hiding it in a wrapper is not discharge.

Hash collisions must remain handled by probing and full key equality; no
cryptographic collision-resistance premise is needed.

Dependency: anonymous empty-slice admission. Scope excludes universal native
graph initialization and whole-compiler correctness.
