# Lean verification: next steps after the source review

Review date: 2026-11-04. Baseline: the proof sources accompanying this public preview.
Companion: [review paper](lean-verification-review.pdf), [LaTeX source](lean-verification-review.tex).

This is a proposed execution roadmap based on source inspection. No Lean build,
kernel replay, extraction, compiler execution, or historical acceptance run was
performed for the review. The milestones below are future acceptance criteria.
They do not revise the statuses in the existing
[coverage map](compiler-verification-map.json) or replace the
[boundary contract](compiler-verification-boundary.md).

This roadmap starts from the proof state included in the public preview.
The [public example](../examples/verification/README.md) and
[release evidence procedure](compiler-verification-release.md) provide the
current reproduction commands.

## Direction

Keep the hybrid architecture. Prioritize exact source/deployment/runtime artifact
certificates for broader semantic coverage. Continue native implementation proofs
as a bounded effort to establish compiler memory safety and close a concrete
optimizer endpoint. These are different guarantees; one cannot substitute for
the other.

The Zig-to-Lean machinery is already included: restricted source extractors in
`lean/extract_*.py` and instrumented AIR capture/generation in `lean/zig_air/`.
It is not a general or verified Zig frontend. Do not restart this work as a
general transpiler project unless that becomes an explicit product objective.

Judge progress by admitted source features, complete artifact boundaries, and
compiler premises removed from final theorem statements. File counts, proof
counts, and passing examples are supporting measurements only.

## Current position

| Area | Source-supported position | Next missing connection |
| --- | --- | --- |
| Algebraic rules and dispatch | Production table soundness, generated IR correspondence, broader rewrite proofs | Production semantics and the encompassing compiler path |
| Normalization | Composed contents, ownership, transfer, framing and specified failure proofs | Valid caller admission and composition through graph effects |
| Recursive optimizer | Finite logical recursion and increasingly concrete native caller proofs | Initial native facts, query agreement, complete production composition and completion claims |
| Native map/hash | Typed storage, hash-update invocation, receiver probing/publication | Empty-slice adapter; complete native hash producer; rehash/install/retire |
| Artifact certificates | Restricted graph, byte-block, Solidity deployment/runtime and storage routes | Broader source/ABI/control/effect coverage and current per-artifact acceptance |
| Whole compiler | General endpoint explicitly open | Full stage composition or broader accepted-artifact route |

## Milestone 0 — Make the assurance contract easy to inspect

Deliver a compact endpoint manifest derived from the existing coverage map and
compiled declarations when checks are next authorized. For each endpoint, record:

- Exact theorem name, source module, statement, and transitive logical axioms.
- Source/settings/artifact domain, target architecture and fork.
- Fixed host/model assumptions separately from unproved compiler premises.
- Which conclusions require an ordinary outcome, sufficient fuel, successful
  allocation, or represented initial state.
- Whether the result concerns a logical model, typed-memory execution, captured
  AIR, current bound production source, or an actual accepted artifact.
- Reproduction command, source/tool identities, and durable evidence location.

Reuse [Declarations.lean](../lean/Contract/Check/Declarations.lean),
[prove.py](../lean/prove.py), and
[compiler_artifacts.py](../test/lean/compiler_artifacts.py). Avoid introducing a
second status database. Add concise generated endpoint views to the existing map.

Acceptance: a reviewer can distinguish the conditional
`Recursive.production_verified` result from native find/force results and from
an artifact certificate from the current endpoint statements. Each
unclosed premise has an owner and a consumer. No premise is reclassified as a
host assumption merely to close a milestone.

## Milestone 1 — Close the demonstrated empty-slice adapter gap

Start with
[ExpressionMapHashNativeEmpty.lean](../lean/Compiler/Extraction/ExpressionMapHashNativeEmpty.lean).
Its `empty_native_update` theorem proves that the captured empty view can produce
`emptyBytes`, followed by OOM or unsupported in the native update adapter. A
successful cell-model update of `[]` does not prove this native call.

Define a consistent representation for anonymous empty byte slices across
argument capture, saved parameter slots, reads, and update invocation. Preserve
the distinction between a zero-length sentinel and readable nonempty backing.
Do not fix the issue by imposing a nonempty-input premise on the production
endpoint or by treating unsupported as success.

Acceptance:

- A represented empty argument list reaches the actual update invocation with
  the specified empty-update behavior, under explicit resource contracts.
- The proof derives its call admission and preserves caller storage and stack
  cleanup; it does not assume a successful intermediate update.
- Nonempty views retain bounds, initialization, lifetime, and separation checks.
- Empty/nonempty, invalid descriptor, alias, and allocation-failure controls are
  retained; regenerated source binding and kernel replay cover the consumer.
- The hash/map consumer uses the result, removing the adapter rejection from its
  supported domain. No claim of a native Zig bug is inferred from the old model.

Dependency: this is the first native implementation task; it need not delay
independent artifact work.

## Milestone 2 — Compose the complete native hash producer

Consume the existing
[complete update invocation](../lean/Compiler/ZigAir/WyhashUpdateAirComplete.lean)
from real caller byte admission. Connect initialization, ordered field updates,
argument-byte views, finalization, and cleanup on the same reached state. Retain
the source validity conditions that ReleaseFast AIR may erase.

Use the receiver-level consumers in
[ExpressionMapSearchMemory.lean](../lean/Compiler/Extraction/ExpressionMapSearchMemory.lean)
to define success. Local hash equality is not the endpoint: the exact value
computed by the captured producer must supply the lookup/publication input.

Acceptance:

- The final native consumer no longer needs a caller-supplied digest or an
  unconnected local-runner correspondence premise for this admitted path.
- Arithmetic, layout, byte order, permissions, empty input, source framing,
  partial allocation failures, and cleanup are derived at the call site.
- Finalization and context/key preparation have explicit source/AIR bindings.
- Collision behavior is justified by probing and full key equality. No
  collision-resistance assumption is added.
- The endpoint premise ledger shows the removed obligation; moving it into a
  callback or wrapper does not count as discharge.

## Milestone 3 — Establish and preserve the actual map/graph invariant

Complete growth as a transition on the real owner: allocate and initialize the
new table, migrate every live binding, install the table, and retire old storage.
Preserve lookup routing, representative values, key ownership, caller borrows,
and the actual failure prefix. Keep replacement, tombstones, collisions, and
capacity boundaries explicit.

Then derive
[NativeGraph.Facts](../lean/Compiler/Extraction/InternerNativeGraph.lean) and the
table/probe invariant from actual compiler initialization. Trace every reachable
mutator that can invalidate them. Separate reachable call sites from an inventory
that also contains unused helpers.

Acceptance: induction from initialization through arbitrary admitted sequences
of graph operations preserves the complete invariant, including ordinary OOM
paths. The production caller does not receive a prevalidated hypothetical graph
in place of the actual initialized and mutated one. Local temporary-map fixtures
alone do not meet this milestone.

## Milestone 4 — Publish one closed native optimizer endpoint

Use
[production_find_verified](../lean/Compiler/Extraction/InternerNativeFindProduction.lean)
and
[production_force_verified](../lean/Compiler/Extraction/InternerNativeForceProduction.lean)
as the starting endpoints. Derive their initial facts, query agreements, source
privacy/representation, item representation, and enclosing frames at production
entry. Preserve force's required semantic equality: inserting a cache alias is
not a proof of that equality.

Connect the exact result, graph, memory, allocator effects, and deferred cleanup
through recursive children. Audit the `ordinary` guard in
[Ensures](../lean/Compiler/Extraction/InternerPhysicalMeaning.lean): a proof that
rejects all interesting executions does not establish a useful native guarantee.

Publish separate statements for:

1. Partial correctness of every admitted ordinary completion.
2. Establishment and preservation of source/native safety preconditions.
3. Exclusion of unsupported semantic faults for the declared domain.
4. Completion or sufficient observation fuel, where established. If unrestricted
   native recursion termination is not proved, state that limitation explicitly.

Acceptance: the declared production slice has a final theorem whose remaining
assumptions are the fixed boundary contracts and real input-domain conditions,
not the slice's own graph/callback correctness or unexplained initial invariant.
The same theorem covers the relevant ordinary error paths. Fresh bindings,
dependency audits, negative controls, and imported kernel replay accompany it.

## Artifact track — Deliver semantic breadth alongside bounded native work

Select complete source units from the intended deployment workload and classify
their first unsupported constructs using the current admission code. Choose the
next extension from those results; the source review alone does not establish
which feature would deliver the most application coverage.

For each extension:

1. Specify the source semantics and complete admitted grammar before changing
   admission. Preserve non-vacuous ABI domains and reject unsupported siblings.
2. Extend the independent target model only for required instructions and effects.
3. Generate certificates binding exact source/settings, creation/runtime bytes,
   dispatch from entry, and deployed-code installation.
4. Include success, revert, exceptional/static, and gas-boundary behavior relevant
   to the feature; preserve rollback and transaction-local effects.
5. Add corruption controls for the new semantic boundary, alongside existing
   controls. Resource exhaustion is not semantic rejection or acceptance.
6. Produce a complete fresh certificate package and imported replay. Report
   acceptance coverage and rejection reasons without implying that rejected
   artifacts are necessarily incorrect.

Retain the current
[SolidityCall](../lean/Compiler/Validation/SolidityCall.lean),
[SolidityContract](../lean/Compiler/Validation/SolidityContract.lean), and
[SolidityStorage](../lean/Compiler/Validation/SolidityStorage.lean) guarantees.
Do not silently drop the calldata size bound, nonpayable checks, short/unknown
dispatch paths, storage original/current state, warmth, refund deltas, or static
write faults when generalizing them.

Before admitting loops, require a checked invariant/termination or explicitly
partial-correctness policy. Before admitting external calls or gas introspection,
define an observation relation that handles their gas-sensitive behavior. The
current costed no-call subset cannot simply be reused unchanged. Keep transaction
admission, creation-address derivation, and fee/refund settlement exclusions
explicit until separately covered.

Scheduling recommendation: after at most two coherent native premise-removal
changes, review the consumer and deliver an artifact coverage increment. If no
endpoint premise is removed, reconsider the native subtask before expanding it.

## Trust reduction and maintenance

Work on these when they support the selected endpoints:

- **Source/model adequacy:** review admitted Solidity constructs and EVM opcode,
  memory, gas, static, and rollback rules against a pinned independent semantics.
  The review itself used repository sources only; this comparison is future work.
  Differential fixtures provide evidence, not an adequacy proof.
- **Extraction:** publish a supported-construct and source-validity matrix. Test
  rejection of dead-result operations with side effects, changed guards, casts,
  aliases, comptime resolution, and standard-library changes. The two source IR
  backends share a parser and cannot independently validate it.
- **Artifact capture:** keep exact byte binding and establish complete native
  snapshot capture at the boundary. A checker over a supplied cache cannot find
  an entry omitted before capture.
- **Interfaces:** package coherent invariant families and expose a few named
  endpoint modules. Preserve visible field meanings and failure states. Avoid
  broad file consolidation without a demonstrated maintenance benefit.
- **Evidence:** retain immutable replay packages or durable content-addressed
  receipts. Temporary paths and historical corpus totals are not current
  acceptance. Include the exact public repository revision.
- **Checks:** use focused development checks while iterating, then the complete
  affected gates once a consumer changes. Retain existing worker/memory limits.
  Repeated unchanged full-suite runs do not improve the theorem statement.

## Completion criteria and deferred work

A restricted certified compiler product is ready when every *accepted* output
has a replayable certificate for its exact source/settings/deployment/runtime
pair and a clear domain and observation policy. Unsupported, failed, and
resource-limited cases remain explicit. This can be delivered before universal
implementation verification.

A universal implementation claim additionally requires the open parsing,
analysis, lowering, Yul optimization, backend, assembly/linking, and request
orchestration obligations to compose, or a clearly delimited artifact validation
replacement at each boundary. It also requires the promised failure/progress
properties. The optimizer milestone alone cannot close these stages.

Defer a general verified Zig frontend, full allocator/LLVM verification, a
wholesale Lean rewrite of the compiler, and proof-count-driven infrastructure
expansion. Revisit them only if measured endpoint needs or an explicit trust
reduction objective justify the cost.
