# verification: admit anonymous empty slices in native hash update

This is a model/admission limitation, not a demonstrated Zig compiler defect.

## Evidence and consumer

`lean/Compiler/Extraction/ExpressionMapHashNativeEmpty.lean` proves
`HashSlice.empty_native_update`: the captured empty argument view produces
`emptyBytes`, and the native update adapter returns OOM or unsupported. The
successful cell-model update on `[]` does not establish this native call.

The consuming boundary is the complete hash runner feeding native map lookup
and publication. Its empty-argument path must consume the actual captured update
invocation proved in `lean/Compiler/ZigAir/WyhashUpdateAirComplete.lean`.

## Completion criteria

- Give anonymous empty slices a consistent representation through parameter
  saving, typed slots, reads, and invocation.
- Derive successful empty-update behavior under the declared resource contracts;
  retain actual allocation failures and caller storage/stack framing.
- Preserve nonempty bounds, initialization, alias, and lifetime checks.
- Cover empty sentinel, nonempty, invalid descriptor, alias, and allocation-failure
  controls with current source bindings, declaration audit and fresh replay.
- Consume the result in the production-facing hash runner; do not replace the
  missing connection with a successful local-model premise.

Do not add a nonempty-input restriction to hide this supported production case,
reinterpret unsupported as success, or expand the fixed trust boundary.

Dependencies: none. This unblocks complete native hash producer composition.
