# verification: derive native optimizer entry invariants at production call sites

The native find/force theorems prove useful conditional behavior. This issue
derives their compiler premises from real initialization and reachable callers.

## Evidence and consumers

- `lean/Compiler/Extraction/InternerNativeFindProduction.lean`:
  `NativeRecursion.production_find_verified`.
- `lean/Compiler/Extraction/InternerNativeForceProduction.lean`:
  `NativeRecursion.production_force_verified`.
- `lean/Compiler/Extraction/InternerNativeGraph.lean`: `NativeGraph.Facts`.
- `lean/Compiler/Extraction/InternerPhysicalMeaning.lean`: the ordinary-result
  guard in `Ensures`.

## Completion criteria

- Establish native graph/table facts from actual compiler creation and preserve
  them across every admitted reachable mutation.
- Derive query agreements, represented/private input, item representation,
  scratch allocation, and enclosing caller frames at the actual entry points.
- Compose the exact result, graph, memory, allocator effects, and cleanup through
  recursive children. Keep reachable sites separate from unused inventory entries.
- Preserve force's caller-provided semantic equality; recording an alias does
  not prove that equality.
- Publish separate statements for ordinary-completion correctness, source/native
  safety admission, exclusion of unsupported semantic faults in the declared
  domain, and any established completion/sufficient-fuel property.
- Show non-vacuous admitted executions and retain ordinary error cases, source
  binding, controls, theorem audits and fresh imported replay.
- Remove the initial/compiler premises from the final consumer instead of
  relabeling them as host assumptions.

Dependencies: complete native hash composition and map growth preservation for
the full admitted endpoint. Native termination beyond finite observations and
the rest of the compiler pipeline must remain explicitly open unless proved.
