# Compiler verification boundary, version 2

The fixed host toolchain is Zig 0.17. This contract specifies the trust
assumptions, caller memory obligations, and division of verification
responsibility for the public preview.

The first production milestone is the complete `NormalizedArguments.init` /
`takeOwned` / `deinit` operation. Its composed theorem is
`Normalization.production_verified`, checked by `check_word_swap.py --normalization`.
The next milestone composes that execution into recursive optimizer
preservation. Primitive work must discharge a named obligation in that
composition. The authoritative inventory is
[`compiler-verification-map.json`](compiler-verification-map.json). Proof
counts alone do not establish coverage or current acceptance.

## What a completion claim means

An implementation proof establishes preservation for all admitted executions
of the bound production operation under its stated contracts. An artifact
validator establishes preservation for the **actual input/output pair that it
accepts**. Either route can close a semantic boundary. The validator must have
a proved soundness theorem and strict artifact binding; rejection, resource
exhaustion and unsupported inputs do not establish preservation. A sound
validator may reject correct compiler output. Test parity alone closes neither
route. This is the distinction used by
[verified register-allocation validation](https://xavierleroy.org/publi/validation-regalloc.pdf).

The optimizer graph route captures every input-node result ID, all native
representatives and the entire interner cache after the admitted production
operations. `Inventory.certify` composes successful evaluation of both graphs,
word preservation at every returned ID and agreement of every captured cache
key with its stored representative, for every word environment. The selected
root theorem follows from the same certificate. Unused result IDs and cache
bindings are checked even when they cannot affect that root.

The proved checker also regroups constants for the production recursive
`RuleList.reassociate` operation: ADD, MUL, AND, OR and XOR, with either nested
operand position and paired nested expressions. This discharges actual artifact
equalities such as `(x + 3) + 5 = x + 8` using word-level associativity and
commutativity. It checks both the returned results and recursive cache aliases.
Other operators cannot enter that rewrite. Finite normalization fuel can reject
valid output; it never supplies an assumed equality.

Capture completeness remains part of `artifact.binding`: source review checks
iteration over the actual native map; a certificate for a supplied snapshot
cannot detect an omitted native entry. The profile supports pure acyclic word
graphs with sequence zero, at most 256 nodes, expansion 4,096 and 1,024 cache
entries. Unsupported fields/operators, malformed references, allocation failure,
resource limits and failed equivalence checks reject explicitly. This is a
successful-artifact guarantee, not a proof of native memory safety, arbitrary
future mutations or the complete recursive implementation. Those obligations
remain open under the existing memory contracts. No host assumption is added.

The intended final claim concerns Solidity behavior and exact emitted EVM
creation/runtime bytes, with fork, input domain, rollback and gas observations
explicit. A certificate for one pure function does not establish this claim for
all Solidity. The function route covers one pure `uint256` function with checked
or unchecked arithmetic under fixed Cancun settings. Its certificate quantifies
over every call value and calldata shorter than `2^64` bytes, including unknown selectors, short arguments,
nonpayable rejection and permitted trailing bytes. That size bound is the
certificate's explicit domain, not an EVM consensus limit. Return/revert bytes,
incoming-value rollback, persistent world and every execution gas budget are
observed. The closed source parser remains trusted. Accepted ordinary compiler
artifacts receive this guarantee without proving each transformation algorithm.

The ABI decision follows Solidity's documented acceptance of
[trailing data](https://docs.solidity.org/en/latest/frequently-reported-non-bugs.html#non-canonical-abi-encoded-calldata-is-accepted)
and [nonpayable rejection](https://docs.solidity.org/en/latest/abi-spec.html#json).
Each checked dispatch path starts at runtime entry and binds the complete code;
the partition theorem composes every path, including failures. Canonical-call
preservation for unchecked arithmetic follows from the stronger certificate.
Unsupported or resource-limited proof generation still rejects the artifact.

Checked addition, subtraction and multiplication propagate the exact
[`Panic(0x11)` payload](https://www.soliditylang.org/blog/2020/12/16/solidity-v0.8.0-release-announcement/)
through nested expressions. Bitwise operations and
[shifts retain word truncation](https://docs.soliditylang.org/en/latest/types.html#shifts).
The source model reuses `Contract.CheckedOp`; the proof binds the arithmetic
mode to the admitted source and checks the actual guards and panic-memory
writes. Pure operands have no effects, and every arithmetic failure here has
the same panic payload, so operand evaluation order does not change the source
outcome. Exact execution costs are derived from each artifact; different
optimized artifacts need not use equal gas. The ABI
witness proves a nonempty input domain, not successful body execution: a valid
function may always panic. Division, signed or narrow types, mixed arithmetic
blocks, statements and stateful behavior remain outside this fragment.

The function gate packages at most 16 certificates per proof object, retaining
the 64 MiB object limit. Every batch has explicit case indices, source/object
hashes, a fresh package audit and kernel replay. Acceptance requires every batch
and the unchanged input/tool bindings; a partial batch run is not corpus success.

The same certificate now binds exact creation and runtime bytes from one
Standard JSON response. `SolidityDeployment.certify` proves execution of the
implicit nonpayable, effect-free constructor and installation of precisely the
certified runtime. It then derives call preservation at the deployed account;
installed-code correctness is no longer a premise of this composed endpoint.
Constructor value rejection, execution/deposit out-of-gas, rollback of target
nonce preparation and incoming value, and a successful deployment witness are
included. The gas budget starts after admission/intrinsic/initcode charges.
Address derivation, creator nonce handling, collision/message admission and
transaction fees remain outside this frame. Appended constructor arguments,
explicit constructors, state initializers and general Solidity are unsupported.
The generator currently proves runtime-at-tail layout; correct other layouts
may be rejected. Limits of 2,048 creation bytes and 1,024 runtime bytes bound
certificate generation and are not protocol limits.

The existing Cancun frame model applies the
[runtime size limit](https://eips.ethereum.org/EIPS/eip-170),
[0xEF prefix rejection](https://eips.ethereum.org/EIPS/eip-3541), and
[initcode limit and code-deposit charge](https://eips.ethereum.org/EIPS/eip-3860).
Artifact proofs discharge size/prefix checks and derive every execution gas
boundary; the EVM model adequacy assumption remains unchanged.

## Fixed trust boundary

The map records the exact contracts and gives each one a stable identifier.
These are assumptions of the implementation-to-native claim, not milestones
to verify Zig, LLVM or the allocator before verifying this compiler:

| Boundary | Assumed contract | Work that remains inside our verification |
| --- | --- | --- |
| Lean | Lean 4.29.0 kernel and the audited logical axioms `propext`, `Classical.choice`, `Quot.sound` | Exact proof roots/imports, fresh replay, no extra axioms or admitted goals |
| Zig admission | Reviewed restricted exporters, pinned Zig 0.17 resolution/comptime semantics and captured AIR describe the admitted production bodies | Fail-closed source binding, generated freshness, correspondence of emitted semantics and their proofs |
| Host execution | Zig/LLVM, linker, ABI and hardware implement admitted Zig semantics under the proved preconditions | Compiler control flow, ownership, bounds, casts and supported failure behavior |
| Native memory | Native allocations/aliases admit the typed layout and lifetime injection stated in `host.layout` | Establish each operation's `Represents`, `Related`, writable/owned and separation preconditions and preserve them |
| External allocation | Aligned, bounded, disjoint fresh storage or OOM; old storage framed; private effects in call order | Zero/nonzero branching, descriptor/registry checks, initialization, and both ordinary allocation failures |
| Native copy | Exact copy on initialized source and writable disjoint destination; dupe allocates first | Argument lengths, source/destination identity, order, ownership and actual reached effects |
| Native free | Matching allocator and complete live persistent extent; aliases invalidated; frame preserved; empty no-op | Correct release and transfer decisions; exactly which caller owns cleanup |
| Native stack | Captured layout, fresh call frames and valid lifetimes | Stack/scratch use and explicit finite-observation or memory-fault outcomes |
| Language models | Independent models describe the explicitly admitted Solidity/Yul/EVM constructs and fork | Preservation by compiler code or accepted artifacts; unsupported constructs stay explicit |
| Artifact admission | Reviewed strict parser/orchestration bind exact source, settings and output bytes to the theorem | Rejection of mismatched, malformed and unsupported artifacts; per-artifact proof checking |

The **host** Zig backend assumption does not assume correctness of this
compiler's **Solidity-to-EVM** backend. That backend remains in scope. Likewise,
model adequacy does not assert that lowering preserves the model.

Native allocation and memcpy can remain external contracts for the normalization
milestone. Proving their implementations is optional trust reduction. Capturing
caller AIR is also optional when a reviewed complete source extractor supplies
the declared binding. Neither option permits omitting statements or assuming
normalization's own postcondition. This scope separation follows the explicit
verified/unverified boundaries in
[CompCert's correctness statement](https://compcert.org/man/manual001.html).

`Except` semantic contract faults and proof-observation exhaustion are distinct
from Zig's recoverable OOM. A violated external contract is not an accepted
execution and supplies no native rollback guarantee. The checked model retains
its actual partial state; no cleanup is invented. Successful native execution
must satisfy the contracts, and the composed theorem must account for ordinary
OOM at both initializer allocation and borrowed duplication.

Changes to these contracts require a boundary-version change, source review and
rechecking dependent claims. Reducing an assumption is useful only when it
advances a named production obligation or deliberately reduces this boundary.

## Normalization acceptance contract

`normalization.production` must have one composed theorem, bound by the complete
production-body admission in `lean/extract_cache.py` and the extracted insertion
program. Its execution must connect the existing memory operations and ownership
decisions, rather than combine independent final-state claims.

The theorem must cover the following paths for arbitrary represented argument
lists, valid caller scratch storage and admissible external allocation effects:

| Path | Required behavior |
| --- | --- |
| Noncommutative or fewer than two arguments | Borrow the input unchanged; skip preparation and temporary allocation |
| Commutative, fits scratch (including exact fit) | Copy into the scratch prefix and sort ascending; own no caller scratch storage |
| Commutative, exceeds scratch | Allocate, copy and sort; retain the whole temporary allocation until release or transfer |
| `takeOwned` with a temporary | Transfer the same allocation and clear lookup ownership; no duplicate or premature free |
| `takeOwned` with borrowed input/scratch | Allocate and copy the exact prepared contents into an independent owned slice, or propagate ordinary OOM with reached effects |
| `deinit` and caller cleanup | Release a remaining owned temporary, skip borrowed/transferred storage, invalidate the handle; caller cleanup consumes the transferred slice once |

The postcondition must establish exact contents (ascending normalization where
required), original source and unrelated-storage frame, live ownership on
transfer, absence of double-free, and cleanup on lookup/failed-take/caller-cleanup
exits. Empty sentinels require no backing allocation. All callbacks receive the
actual effects reached by earlier allocation/copy/sort steps. Scratch preconditions
must be derived at the production caller boundary, not assumed for arbitrary
aliasing buffers.

The component dependencies already available are
`normalization.allocationContract`, `normalization.preparationContract`,
`normalization.borrowedDuplicateContract` and `normalization.releaseContract`.
Any additional primitive proof must name the missing composed-theorem premise
it discharges. Acceptance also requires source mutation controls, failure-path
fixtures, theorem dependency audit, fresh replay and review against this table.

`normalization.recursiveBridge` then refines `Scoped.Resources` for the same
execution and composes with `InsertionSort.detailed_verified`. The existing
theorem covers finite recursive observations and abstract graph contracts;
concrete graph-memory and native completed-execution connections stay visible
in `optimizer.graphMemory` and `optimizer.recursiveProduction`.
The physical `PreparedPrimitives` adapter now has exact correspondence with
normalization memory execution for arbitrary states and budgets, including
faults. Its production theorem inherits these fixed contracts. The remaining
bridge requires the same execution across intervening graph effects and recursive
invocation nesting. `--scope-trace` now checks the local cursor projection to
`Scoped.initScope`, `take` and `close`, bound to a transcript produced by the
physical adapter. It preserves surrounding trace positions and rejects semantic
faults before total resource projection. Successful transfer supplies exactly the
physical slice's contents to the scope, not only the same ownership and cursor.
It does not certify surrounding events,
complete native caller traces, or global transcript consumption.

`--owned-continuation` connects physical normalization to the source-bound
`find` owned continuation (`controlOwned`/`controlMiss`). Callbacks receive the
exact owned slice, a key with the same arguments, and the state reached by prior
operations. Deferred cleanup runs on their returned state; publication hands
off only after success, while insertion receives ownership before either
outcome. Detached lookup destruction never reads an already consumed alias.
`OwnedCall.production_verified` establishes source preservation and caller
ownership closure for ordinary outcomes, under named callback contracts.
`run_verified` also preserves the body result and retains semantic-fault state.

The callback contracts are open **compiler implementation obligations** in
`optimizer.graphMemory`, not additions to the frozen host trust boundary.
The nested-normalization fixture discharges its borrow contract from the
existing complete operation theorem; it does not implement recursive graph
simplification. The owned-continuation theorem alone excludes cache-hit/capacity
routing and `forceEqual`; the complete caller extension below covers their
control. Complete recursive execution projection and production graph storage
remain open. Word preservation must ultimately describe that same execution.

`--interner-callers` extends this to both complete extracted control bodies.
`OwnedCall.Caller.production_verified` derives caller scratch and composes
initialization, capacity/validation guards, cache hits, owned continuations and
deferred cleanup. A lookup hit may still own a temporary; its release is proved
from `deinit_refines`. Ordinary outcomes close caller ownership and preserve the
source; final results and callback graph changes are retained. Semantic faults
keep the exact body state. The shared `ForceCode.controlOwned` continuation is
also used by the existing scoped ownership, frame and word proofs.

This is complete **control/memory coverage under contracts**, not closure of
`optimizer.recursiveProduction`. Read-only query observations are explicit and
the memory theorem covers all of their results; their correspondence to native
capacity, determinism and representative queries is still a compiler obligation.
Graph implementation contracts and projection of the same physical recursive
execution into word preservation remain open. Native stack allocation/lifetime
continues to use the existing `host.stack` boundary.

`--physical-words` proves memory and word preservation for the **same complete
physical caller execution**. `OwnedCall.Semantic.production_verified` derives
normalization's word meaning from its actual checked result, composes exact
key/slice callback contracts, and uses the memory theorem to retain the body
result and graph through cleanup. Ordinary outcomes preserve the graph invariant
and old node values; successful `find` returns the requested word. `forceEqual`
retains its caller-supplied semantic equality premise. Semantic faults remain
rejected observations with the exact body state, not ordinary-error proofs.

Semantic insertion, publication and simplification contracts are additional
**compiler obligations**, not host assumptions. A concrete fixture discharges
both memory and semantic contracts: it performs nested normalization, checks an
existing ID against the key's value, publishes/consumes the slice, and exercises
successful and failing complete callers. Its abstract value graph is explicitly
a fixture. Physical recursive simplifier induction, native graph/query refinement
and completed native execution binding remain open; this gate does not close
`normalization.recursiveBridge` or `optimizer.recursiveProduction`.

`--physical-dispatch` closes the execution-interface blocker between that caller
and the recursive dispatcher. The seven extracted dispatcher/helper modules now
use Lean's standard `Monad` and `MonadLift` interfaces. Their logical-heap
specialization retains the existing recursive word proofs; their physical-world
specialization threads actual memory and allocator effects through constructor
calls. Both use the same generated control and constructor request encoding.
Exact language errors are lifted without recovery; bind propagates every fault
with its reached state. This follows Lean's documented
[monad lifting interface](https://lean-lang.org/doc/reference/latest/Functors___-Monads-and--do--Notation/Lifting-Monads/);
the local proof and failure tests establish the particular state behavior.

Concrete fixtures cover ordered calls, early/late failure, semantic rejection,
materialization, unary and revision-specific paths. A nested constant-fold
fixture enters two complete physical callers through the actual dispatcher and
checks cleanup on success and ordinary failure. These are interface and fixture
claims. The logical word proofs do not automatically become proofs about the
physical specialization: universal recursive word/borrow induction and native
constructor argument preparation remain open, alongside graph/query refinement.

`--dispatcher-preservation` proves the complete dispatcher effect relation for
all opcodes, argument lists, options and related constructors, including every
helper and the ordered fallback stages. This is a proof about the shared
extracted programs. It adds no monad law or parametricity axiom. A proof-producing
tactic retains shared continuations and applies proved rules; the kernel checks
its output, including during fresh replay. The design keeps the distinction
between [monad interfaces and their laws](https://lean-lang.org/doc/reference/latest/Functors___-Monads-and--do--Notation/Laws/)
explicit instead of treating polymorphism as a preservation theorem.

Two physical interpretations discharge named simplifier obligations.
`simplify_borrows` derives the complete caller ownership field from recursive
constructor borrowing. `simplify_verified` transports the existing word proof
and a physical invariant through exact constructor simulation: admitted results
and reached graphs must match, and the physical predicate must survive ordinary
failures as well as success. Matching final words alone does not satisfy this
contract. Semantic faults remain rejected observations with actual effects.

Fixtures instantiate both laws with a live nonempty outer allocation, counted
constructor effects and every finite unfolding of the existing logical recursive
model. That counted adapter is explicitly a simulation fixture. Proving this
simulation for recursive physical `Caller.find`, implementing and validating
native constructor argument preparation, and closing complete physical recursion
remain open. The graph/query and frontend/backend boundaries are unchanged.

The map names this production obligation `optimizer.recursiveConstructors` and
makes it a dependency of `normalization.recursiveBridge`. Native `makeOperation`
passes the supplied slice to `findDefault`; the current extracted constructor
request retains argument values without their borrowed/temporary provenance.
Closing the obligation requires preserving that actual storage and its lifetime
through recursive calls, then deriving `Recursive.Projects` for the same execution.
Allocating a fresh buffer for every logical list would model different compiler
behavior. The concrete constructor and dispatcher call sites are therefore the
next exporter targets; general Zig translation and native allocator proofs are
not prerequisites. The gate must include nonempty nested arguments, preservation
of the live outer borrow, and OOM after earlier graph growth.

`ConstructorFrame.operation_verified` now proves the argument-view call boundary
under the existing physical graph callback contracts. It forwards the original
allocation, offset and length into the complete caller, checks capacity before
allocating its two-word scratch array, runs the existing normalization and defer
interpreter, and unwinds the reached stack frame on ordinary outcomes. The source
view, persistent argument contents, word result and reached graph survive that
unwind. Allocator effects and lifetime/address counters are retained. Stack
exhaustion remains a rejected resource observation; semantic faults retain their
reached memory and local ownership without invented cleanup.

`Normalization.Valid.injected` now requires persistent backing for every
allocator-owned registry entry. Borrowed source and scratch views stay outside
that registry. Argument allocation/duplication, item creation, byte cloning,
publication and destruction preserve the strengthened invariant in their existing
model proofs. `Valid.cleanup` derives it after stack unwind, so the frame theorem
restores the complete `Valid`/`Good` invariant on ordinary success and OOM.
This strengthens a compiler invariant; the fixed host contracts are unchanged,
and no final-state correctness premise is introduced.

The earlier existence-only predicate is retained as `Backed` for the checked
`backing_does_not_imply_safe_return` counterexample. `escaping_not_valid` proves
the departing stack-backed registry entry violates the strengthened invariant.
These are model invariant checks, not a native compiler bug report. Native graph
storage refinement and recursive constructor simulation remain `optimizer.graphMemory`
and `optimizer.recursiveConstructors` obligations; preserving the model invariant
does not derive universal native caller admission. Dispatcher call-site
temporary/borrowed provenance remains a separate extraction obligation.

`--dispatcher-production` connects those laws to the complete physical caller
composition. `OwnedCall.Recursive.production_verified` derives the actual
simplifier's ownership and word contracts, then composes fresh scratch,
normalization, dispatch, publication/insertion, transfer and cleanup. The seed
simplifier has no correctness premise. Insertion/publication ownership and word
contracts, recursive constructor simulation and query refinement remain explicit
compiler obligations. `forceEqual` retains its semantic equality premise.

Complete caller fixtures use nonempty source operands and the counted recursive
adapter. They check source preservation and cleanup after success and ordinary
failure, including publication failure after recursive graph growth; rejected
cutoff retains its live slice and reached effects. These fixtures establish the
composed proof attachment, not native argument preparation or complete physical
recursive induction. The fixed host assumptions and coverage statuses remain
unchanged.

`check_owned_keys_physical.py` connects the source-admitted `publishOwned`
profile to normalization's typed release. Logical and physical interpretations
share `Code.execute`/`Code.complete`; checked equations preserve the previous
logical model, including its diagnostic free effects. The physical operation
uses the existing owned-key table and one normalization session. It proves
replacement, new/empty entries, incoming ownership, borrowed-cell framing,
allocation-history preservation and cache semantics. Probe effects survive OOM;
successful free observes the state after probing. A release contract fault stops
before the free callback or key store and retains the reached state.

The `--caller` gate derives publication's memory and semantic contracts inside
both complete physical callers and the actual shared dispatcher. There is no
publication postcondition premise. An executable admission check verifies the
reached key/slice agreement, old entry ownership, and separation from the
incoming allocation and borrowed source. The check is proved sound and complete
for its stated local input contract, including empty sentinels. Accepted calls
execute the unchanged publication body. Rejection is a non-ordinary semantic
observation retaining the reached state; it is not a native error or accepted
compilation. This check
is in the model, not inserted into the compiler, and may reject executions that
would not violate native memory safety. Universal native admission must still
be proved from graph ownership and caller invariants or checked against bound
execution evidence.

The existing owned-key table supplies allocation identities missing from the
value-only graph model. It is carried alongside private allocator effects;
allocation/free wrappers preserve it. The existing semantic cache remains its
proved value projection, not a second native cache operation. The publication
proof preserves that connection when it holds at entry. Other graph operations
must establish and preserve the same connection. The constructor fixture only
validates an existing word; it is not a native recursive constructor proof.

Native bucket allocation/probing, entry pointers and metadata binding remain
compiler implementation obligations. Insertion, queries, complete physical
recursive construction and global graph ownership also remain open. These are
recorded in `optimizer.publicationMemory` and `optimizer.graphMemory`; neither
is closed. No assumption was added to the fixed host boundary. Allocator
implementations remain under their existing contracts.

## Insertion execution boundary

`optimizer.insertionExecution` closes the control/semantic model of the complete
source-bound `insertOwned` body. `Storage.Program.execute` uses the existing
extracted program and ownership transitions; allocation and cleanup callbacks
see the reached state and retain their private effects. The older allocation-only
interpreter cannot express cleanup affecting a subsequent callback, which is
the reason for this interpretation of the same program representation.

`InsertionExecution.verified` composes ownership and capacity preservation with
the existing graph projection, representative coherence and word preservation
for that same execution. The proof covers arbitrary callback effects, both
determinism branches, capacity rejection, and every ordinary allocation failure.
Semantic faults retain the reached state and effects, stop further cleanup, and
are rejected observations. They are not OOM or successful cleanup.

Run `python3 test/lean/check_insertion_execution.py --output <new-directory>`.
The gate binds the extracted program to production source, checks allocation and
release order and graph rollback, rejects semantic executor/source mutations,
audits dependencies and replays the kernel with imports. This closes a model
obligation, not production insertion. Native clone, vector, hash-map and typed
memory refinement must still implement its primitive transitions and attach to
the physical callers. In particular, a callback's arbitrary private effects are
not evidence that those effects preserve physical memory. Those obligations
remain in `optimizer.graphMemory`; no host assumption was added.

The `--destructor` subgate connects the extracted `Expression.deinit` body to
insertion's `lastValue` rollback callback. Its order is item payload cleanup,
item allocation release, argument release, and descriptor invalidation. It
uses normalization's checked whole-allocation free for the arguments. The
composed insertion theorem includes that callback's argument lifetime/frame
postcondition and its reached-state precondition. Fixtures derive the latter
after actual typed argument duplication and exercise both rollback frees.
Semantic item/release faults retain effects and stop before later cleanup.

`optimizer.expressionDestruction` remains partial. Item callbacks use framed
interfaces: they can inspect the reached memory and change private effects;
their native argument-memory separation, item allocation death and payload
destruction remain compiler implementation obligations. The theorem makes no
item-ownership claim. Descriptor invalidation records that the representative
may no longer be read; it does not invent initialized bytes for Zig `undefined`.
Proving every native insertion path supplies the admitted descriptor and
connecting the other graph operations remain open. The host boundary is
unchanged; callback types are not evidence of native refinement.

The `--payload` subgate additionally checks the complete `AssemblyItem.deinit`
body. `AssemblyItemDeinit.run_verified` releases its optional owned byte extent
in normalization's existing logical/typed registry, skips absent/empty payloads,
and invalidates the value. It derives preservation of every argument allocation
from distinct registry block kinds. Typed persistent-release checks are shared
with argument cleanup; free does not require initialized byte contents.

This discharges the payload-cleanup operation within
`optimizer.expressionDestruction`. Native optional-field projection, ownership
establishment and the memory-changing callback connection remain compiler
obligations. The current expression item interface still frames the registry;
this subgate does not claim that it invokes the new byte cleanup. The item's
own allocation is also still live: `allocator.destroy(self.item)` is a separate
operation. These limitations remain explicit in the coverage map and report;
no new host assumption is added.

The `--payload-insertion` subgate closes that callback connection. A shared
expression executor now accepts operations that change the full session; the
older framed model is an explicit adapter. `Payload.run_verified` composes the
actual extracted item destructor with the subsequent allocation callback and
argument free. Byte cleanup derives argument ownership; argument free cannot
revive the released payload, including an empty argument sentinel with its ID.
A later allocation callback fault preserves the payload release and reached
effects while stopping before argument cleanup or descriptor invalidation.

`Payload.insertion_verified` concerns the same complete insertion execution and
its word-preserving projection. The rollback fixture performs actual typed
duplication and all three buffer releases with matching semantic descriptors,
and derives its reached ownership preconditions. Native item allocation
destruction is still framed, and the native optional-field projection and
universal caller ownership preconditions remain open compiler obligations.
Value invalidation is still a descriptor validity boundary; this does not
assert initialized native item fields or a proved struct layout. The frozen
host boundary and the partial production classification remain unchanged.

The `--item-lifetime` subgate replaces the framed allocation callback with
`AssemblyItem.destroy_verified`. The same expression/insertion execution now
consumes the payload, item and argument allocations in the shared logical and
typed registry. Payload cleanup derives retained item ownership from disjoint
registry block kinds; item destruction derives retained argument ownership;
argument cleanup cannot revive either earlier allocation. The rollback fixture
also consumes the original argument buffer after releasing its duplicate.
Wrong owners, types, extents, permissions, stack objects and dead allocations
reject explicitly; later faults retain earlier cleanup effects.

This uses the frozen `host.layout` and `host.release` contracts. A native probe
imports the production `AssemblyItem` through `src/modules.zig` and captures
`@sizeOf`/`@alignOf` using Zig 0.17.0, the pinned Zig 0.17 checkout’s `lib`, and LLVM in Debug,
ReleaseSafe and ReleaseFast. Each accepted profile must reproduce the generated
nominal allocation type. Compiler/library, target, CPU, OS range, mode, probe,
model and production sources are hash-bound in the retained capture report.
Other targets/profiles fail admission. The probe binds the native layout
observation; Lean does not prove Zig's layout calculation or allocator code.

Nominal record metadata deliberately has no field access semantics. Default
Zig struct layout is unspecified (local Zig guide sections 8.3 and 8.12), and
size/alignment alone do not prove field projection. The pinned allocator's
`destroy` frees the complete child extent; its implementation remains behind
the existing release contract. Native optional-field projection, initialization,
object/payload ownership construction and universal caller admission remain
open compiler obligations. Thus `optimizer.expressionDestruction` is still
partial even though the composed theorem closes all three lifetime deaths.
No host assumption was added, and no whole-compiler claim follows from this gate.

The `--clone-insertion` subgate connects the existing source-extracted
`AssemblyItem.clone` body to this cleanup path. Its executor now accepts the
shared memory session and preserves reached effects on both success and error.
Checked byte duplication supplies fresh payload ownership, actual typed reads,
allocator pairing and frames. `rollback_verified` derives the destructor's
payload premise from that clone execution, while preserving the caller's item
object and argument ownership. Insertion callbacks retain the returned clone
value for append-failure and publication-failure cleanup in the same source
control program and word-preserving graph projection.

The byte adapter is an executable specification of the existing `host.allocation`
and `host.copy` contracts. It requests storage before reading the source, checks
the returned region, copies exact typed bytes, and checks the initialized result.
Absent/empty payloads make no request. Ordinary OOM preserves both heaps and
retains allocator effects. Invalid regions, source descriptors or copy results
reject explicitly, retaining the reached allocation/copy state; they do not
become native OOM or trigger invented unwinding. Its soundness theorem covers
accepted observations; it is not a memcpy AIR proof or a claim about native
behavior after a violated host contract.

`optimizer.itemClone` remains partial. The object is already allocated at the
`--clone-insertion` attachment boundary. Native field projection/assignment,
object initialization, vector/hash-map refinement and universal caller admission
remain compiler obligations. Neither arbitrary metadata preservation nor a
local returned-value record proves native field layout. The frozen host boundary
is unchanged; this connection removes the initial cloned-payload ownership
premise from the composed path without replacing it with a clone-correctness
assumption.

The `--item-creation` subgate removes that already-owned-object premise from
the composed creation, clone and rollback path. `Creation.create` requests the
captured item size/alignment under `host.allocation`, checks the persistent
region and registers its lifetime in the same session used by normalization.
The native Zig 0.17 `Allocator.create` returns undefined storage; accordingly,
the nominal cell has no initialized fields. Its logical item is a provisional
projection, and the source control model separately tracks allocation and value
ownership. This is an executable host-contract attachment, not allocator AIR.

`create_clone_rollback` derives object and payload ownership from the two
accepted operations and feeds the existing complete destructor. Clone OOM
leaves the created allocation owned at the reached effects; the actual
allocation errdefer consumes it. Creation OOM retains effects without publishing
an allocation. Invalid regions and registry collisions stay semantic faults,
retaining the admitted reached state without invented native unwinding. Both
duplicated and transferred argument fixtures execute the full source insertion
body, including failure cleanup. Deterministic publication rollback also composes
into the same word-preserving projection.

`optimizer.itemCreation` remains partial: native field initialization/projection,
vector/table mutation and universal native caller admission are still open.
The theorem checks successful observations under the frozen memory contracts;
it does not establish that every native call is admitted, or native behavior
after a violated contract. The trust boundary is unchanged.

The `--caller` subgate closes the admitted physical caller attachment.
`Insertion.production_verified` composes both complete callers with concrete
insertion and publication, without assuming either whole callback postcondition.
Argument duplication/transfer, object creation, source clone, publication and
all applicable cleanup execute through one shared typed/logical session. The
source control theorem and local memory proofs establish word preservation and
memory validity for that same execution, including ordinary failure outcomes.

`Insertion.execution_fields` now derives item and operand correspondence through
the complete insertion program, including duplication, clone, publication and
every applicable cleanup. Its invariant uses the existing memory validity and
copy contracts. `cell_binding` derives the candidate's key/value binding from
those reached locals; the semantic proof does not check or assume final-cell
equality. The same result is a dependency of both complete caller endpoints.

Admission checks the **input** descriptor/key and word, successful local
descriptors, and the borrowed source allocation frame. Failed checks retain the
actual reached state as a semantic rejection. These are finite model-admission
checks; they are not added native compiler branches, an actual-artifact validator,
or proof that every native call passes. The append/probe interfaces still require
native container refinement, and the item descriptor provider still requires
native field binding. Neither is a new trusted host operation. The derived local
field invariant is not a proof of native object stores or container layout.
Fixtures establish it before admission for success and every configured
allocation failure on both argument ownership paths. Mutations corrupt copied
operands, item data and sequence fields; an explicit counterexample confirms
that input/frame admission alone cannot replace the field invariant.

`optimizer.insertionCaller` records this partial connection. Native fields,
containers, global resident-graph ownership, native query refinement, universal admission
and recursive constructor simulation remain compiler obligations. The general
theorem uses the shared dispatcher under its existing constructor contracts;
the complete caller fixtures use a no-rewrite simplifier and separately observe
actual sorting, insertion, publication and cleanup. No compiler-wide assurance
is inferred from those fixtures.

The `--queries` subgate specializes both complete callers with source-bound
capacity, determinism and representative validation, and the existing proved
representative constant/operation readers. `Query.production_verified` composes
these with the same normalization, concrete insertion/publication and shared
dispatcher execution. It removes the arbitrary query and read-soundness
parameters; recursive constructor simulation remains an explicit premise.

`Terminal.force_verified` removes that recursive premise from the complete
`forceEqual` path, which never invokes the simplifier. `Terminal.constant_verified`
does the same for source-bound `makeConstant` through `findDefault` and `find`;
more generally, `Terminal.production_verified` covers every non-operation find.
Exact equality of complete caller executions justifies replacing the unreachable
simplifier while reusing the existing normalization, graph and cleanup proofs.
The graph contracts come from the same concrete insertion/publication execution.
The equality of the forceEqual target and expression remains a required premise.

These endpoints cover ordinary errors and retain rejected semantic-fault states.
Fixtures poison the simplifier's result, graph and private effects, prove success
and OOM cleanup for the terminal paths, and check that an ordinary operation
reaches the poison. Empty constant arguments require no sorting budget; an
actually reached sort with exhausted budget rejects. Dependency audits reject
reintroduced recursive simulation dependencies, and mutations check the operation
guard, publication, constant value and forceEqual equality premise. This closes
the admitted terminal-call connection, not native graph/field refinement or
recursive operation construction. The frozen host boundary is unchanged.

The determinism extractor binds `SemanticInformation.isDeterministic`, the
`AssemblyItem.hasInstruction` assertion, item tags and opcode values. The early
`AssemblyException` is an ordinary error and runs registered cleanup. Malformed
item/optional combinations are rejected as violated defined-execution
preconditions in every build mode, including ReleaseFast where the assertion's
dynamic check is erased. An absent representative projection is rejected before
any caller action; it cannot masquerade as an empty graph. This guard is model
admission, not a branch added to the compiler.

The native probe compares all 525 admitted tag/opcode/optional shapes in Debug,
ReleaseSafe and ReleaseFast. Those observations support source adequacy; they
are not a proof of native descriptor field loads, memory layout refinement or
recursive constructor behavior. The composed fixtures exercise the actual
dispatcher and source-bound representative readers with a checked constructor
fixture; they do not establish native recursive construction. Native field and
container refinement, global graph ownership and universal admission remain
open under the unchanged fixed host boundary.

## Complete pure-contract artifact route

`artifact.solidityContract` extends the exact-artifact route from one function to
complete selected contracts of up to eight external or public functions, each
explicitly `pure` or `payable` with a body in the closed expression grammar.
Expression parameters remain uint256; results are uint256 expressions, bounded
address literals or boolean literals. Empty functions with no return values also
admit unused bytes4 parameters and explicit `view`, as described below. Empty
selected contracts use a separate complete certificate. The independent closed parser rejects other declarations
and duplicate signatures. It resets expression/parameter
scope and payability for each function. Overloading
by arity is admitted; selector collisions reject. The existing source parser and
artifact binding remain trusted under `artifact.binding`.

Per-function payability follows the [Solidity ABI mutability rules](https://docs.soliditylang.org/en/v0.8.36/abi-spec.html#json).
A selected `pure` method rejects nonzero value; a selected `payable` method
admits any value. Both still require the selector and complete arguments.
Successful calls commit the incoming balance transfer; rejection, checked
arithmetic panic and out-of-gas restore the entire world snapshot. Self-calls
preserve balances. The existing `World.transfer` and EVM call frame are reused;
message admission, including sender funds, and transaction fees precede this
model and are not certified here. Bodies still cannot read `msg.value`, access
state or make calls. Receive/fallback and explicit constructors remain rejected;
the implicit constructor remains nonpayable. The single-function parser remains
pure-only; the separate storage route admits per-method payability and receive.

The default output selection still requires one contract declaration. Explicit
`Function.sol:<contract>` selection admits up to eight independently parsed
contract declarations, including empty unselected siblings. Every declaration
must belong to the closed grammar; none is skipped because it was not selected.
Imports, inheritance, state and calls remain rejected, so a selected body's
semantics cannot depend on another declaration. Duplicate names, an absent
target, multiple output targets, and extra or renamed response contracts
reject. The complete source bytes and selected contract are bound to the request;
sibling artifacts remain explicitly uncertified. Other compiler settings are
unchanged except for the two explicit metadata policies below.

Contract certificates admit either the existing metadata-free policy
(`appendCBOR: false`, `bytecodeHash: "none"`) or literal-content IPFS metadata
(`useLiteralContent: true`, `bytecodeHash: "ipfs"`, `appendCBOR: true`). The latter
matches the retained OpenZeppelin request's metadata settings. Cancun, viaIR,
optimizer settings and the source grammar remain fixed. The generator retains
every emitted byte, including the CBOR trailer, in both runtime and creation
proofs. The existing theorem checks their actual execution and full installed
code, with code-deposit gas charged for the complete runtime. It assumes neither
that a trailer is unreachable nor that it can be removed. This does not attest
to the authenticity or availability of an IPFS document: the certificate's source
and artifact bindings remain the authoritative claim.

An address result admits `address(integer-literal)` with a value below `2^160`,
or a bare literal matching exactly `0x[0-9]{40}`. These forty hexadecimal digits
contain no letters, so their
[EIP-55 checksum](https://eips.ethereum.org/EIPS/eip-55) has no case choices.
This bounded admission follows Solidity's
[address-literal rules](https://docs.soliditylang.org/en/v0.8.36/types.html#address-literals);
other bare spellings, address parameters, arithmetic and payable casts reject.
Explicit conversions retain their existing conservative rejection of leading-zero
decimal and checksum-like 39–41-digit hex forms, following the pinned
[address conversion rules](https://docs.soliditylang.org/en/v0.8.36/types.html#address)
and [ABI encoding](https://docs.soliditylang.org/en/v0.8.36/abi-spec.html#types).
The generated body uses `SolidityAddressLiteral.literal`, whose range premise is
kernel checked. `SolidityAddressLiteral.result` proves that either arithmetic mode
returns the 160-bit address zero-extended to one 32-byte word; the actual runtime
trace consumes this result. Return types do not enter the selector. The existing
word expression, dispatch, deployment and installed-runtime proofs are reused.

An ordinary Solidity boolean return admits exactly `true` or `false`. `SolidityBoolLiteral.result`
proves a canonical 32-byte return containing respectively one or zero in either
arithmetic mode, as required by the same ABI rules; the runtime trace consumes
this theorem. Boolean parameters, casts, expressions and word truthiness remain
rejected. The shared word ABI and complete deployment/call certificate are reused.
This extends trusted source admission, not verification of the parser itself.
The single-function route remains word-only and pure; the separate storage route
has its own Boolean arguments, packed fields and payability rules.

A `bytes32` result admits only `bytes32("...")` with one double-quoted,
printable ASCII literal of zero through 32 bytes, without escapes. Solidity's
[string-literal conversion](https://docs.soliditylang.org/en/v0.8.30/types.html#string-literals-and-types)
and [fixed-byte ABI encoding](https://docs.soliditylang.org/en/v0.8.30/abi-spec.html#formal-specification-of-the-encoding)
put the original bytes first and pad on the right with zeros; no dynamic offset
or length word is present. The generator retains the source byte list and
proposes a 256-bit word. The kernel checks both the length bound and the exact
equation `wordBytes value = bytes ++ replicate (32 - bytes.length) 0`.
`SolidityBytes32Literal.result` consumes that checked equation in the actual
runtime trace, reusing the expression, dispatch and deployment certificates in
both arithmetic modes. The generator's numeric conversion is therefore not an
extra assumption. The source parser and model adequacy remain trusted.

Escapes, non-ASCII content, single quotes, Unicode/hex string literals,
concatenation, implicit conversions, dynamic strings and other fixed-byte result
widths reject, including in unselected siblings. The shared tokenizer recognizes
the admitted string as one token, so comment markers inside it remain data.
The raw-return assembly grammar does not acquire a bytes32 declaration through
this extension. The retained Sablier `ERC20Bytes32` source is a complete source
unit; its original 281-source request, original settings and source-contract
security are outside the certificate.

A separate closed inline-assembly body admits only
`assembly { mstore(0, literal) return(0, 32) }`, as the entire function body.
The [Yul EVM dialect](https://docs.soliditylang.org/en/latest/yul.html#evm-dialect)
defines this as a scratch-memory write followed by termination with the exact
32 bytes; there is no Solidity boolean/address result cleanup after `return`.
`SolidityRawReturn.bytes_eq` derives the bytes for arbitrary initial memory,
reusing `Memory.read_write`. Its native trace feeds the same `SolidityDispatch`
metering, rollback, deployment and installed-runtime certificate. Declared
uint256/address/bool result types stay in the source report, alongside the
explicit `rawWordReturn` body scope and full 256-bit returned word. A
noncanonical boolean result remains noncanonical in the certificate.

These raw-return methods may be pure/view/payable and have unused uint256/bytes4
parameters. Named and unnamed parameters retain their original ABI positions;
unnamed parameters are also admitted in empty bodies, but stay rejected in
expression bodies. Both terminal-body kinds share `SolidityNoReturn` admission
and its parameterized `selected_returning` proof. Source admission rejects all
other assembly operations, variables, offsets, return lengths, flags and extra
statements, including in unselected siblings. Literal operands reuse the existing
bounded conversion lexer, including its conservative rejection of leading-zero
decimals and address-like hex forms. The [scratch-memory rule](https://docs.soliditylang.org/en/latest/assembly.html#memory-management)
permits the first 32-byte write; arbitrary memory-safe assembly is not admitted.
The source adapter and language-model adequacy remain trusted. This extension
certifies preservation of these exact source observations, not ERC165 conformance
or the security of the source contract itself.

The shared word parser admits `type(uint256).max` as the existing typed word
literal `2^256 - 1`, using Solidity's
[integer type information](https://docs.soliditylang.org/en/v0.8.36/units-and-global-variables.html#type-information).
Signed/narrow type bounds, other type properties and untyped rational expressions
remain rejected. Public functions expose the same modeled message-call entry;
their additional [internal-call visibility](https://docs.soliditylang.org/en/v0.8.36/contracts.html#visibility-and-getters)
does not add behavior here because the complete grammar still rejects calls and
inheritance. Visibility remains explicit in the source inventory and reports.
The parser accepts exactly `pragma solidity ^0.8.0;` or `pragma solidity *;`.
A [version pragma checks compatibility](https://docs.soliditylang.org/en/v0.8.36/layout-of-source-files.html#version-pragma);
it does not switch the pinned language/compiler semantics. Other version syntax,
additional pragmas and ABI-coder changes still reject. These shared admission
rules also apply to the single-function and word-storage routes.

The single-function and complete-expression-contract routes additionally admit
one standalone decimal or hexadecimal integer literal as a `uint256` return,
provided it is below `2^256`. Solidity's
[literal conversion rules](https://docs.soliditylang.org/en/v0.8.30/types.html#integer-types)
permit this implicit conversion without truncation. Both routes share the
existing bounded-literal validator and word `.literal` semantics; the generated
certificate checks the exact creation/runtime image through the existing
deployment and call theorems. The source parser remains trusted. This does not
admit [literal arithmetic](https://docs.soliditylang.org/en/v0.8.30/types.html#rational-and-integer-literals),
which retains arbitrary precision until conversion. Bare operands within typed
expressions, negative/overflowing values, fractions, exponents, separators,
parenthesized bare expressions, leading-zero decimals and address-like hex forms
remain rejected. The separate storage statement parser retains its existing
explicitly typed expression grammar.

The retained EigenLayer 0.3.0 `src/test/mocks/EmptyContract.sol` unit exercises
this conversion with its complete, unchanged `foo()` body returning `0`.
Certification selects this 159-byte source under the supported Cancun settings,
with metadata-free and IPFS images. Its original London settings and the other
228 sources in the retained request remain outside the certificate; missing
upstream provenance is not reconstructed.

The source model computes each selector from its canonical signature, following
the [Solidity ABI specification](https://docs.soliditylang.org/en/latest/abi-spec.html).
The kernel checks the compiler's method identifier against that computation and
checks distinct word selectors for the complete declared function list. This
binds overloaded names without trusting the compiler's dispatch table. Every
function has a canonical ABI-call witness; a witness need not return successfully
because checked arithmetic may panic.

`SolidityContract.certify` combines complete-runtime traces from PC zero for
short calldata, unknown selectors and every selected function's value/argument/
result paths. It quantifies over all calldata below 2^64 bytes, all message values
and all execution gas budgets. Creation returns the exact certified runtime,
installs it at a fresh target, and composes with later calls in the resulting
world. The source-independent creation frame, installation and successful
deployment lemmas are shared with the single-function route. No runtime-is-
installed premise remains at the composed endpoint.

`SolidityEmptyContract.certify` covers a selected declaration with no functions,
state, receive/fallback handler or explicit constructor. It requires an actual
runtime trace from PC zero for every input, with the explicit outcome `reverted []`.
There is no selected-function or list-membership premise. The proof covers all
finite calldata, every value and every execution gas budget: sufficient gas
reverts with the original world, and insufficient gas is exceptional with the
same rollback. Creation retains the exact runtime, code-deposit gas and a
successful deployment witness, then composes calls against the world actually
produced. Existing metering, frame and deployment lemmas are reused; the
nonempty-contract certificate retains its function-witness requirement.
The exact compiler method-identifier map must be empty, and unsupported source
in any declaration remains rejected. An empty method map alone cannot certify
runtime behavior or deployment.

`SolidityNoReturn.Source` describes exactly empty `{}` bodies with no return
values, explicit pure/view/payable mutability and unused uint256/bytes4
parameters. A `bytes4` value uses the high four bytes of its 32-byte ABI word;
the remaining 28 bytes must be zero. A complete selected call validates every
parameter even when the body does not use it. Short arguments, malformed
padding, unknown selectors and forbidden value revert; success returns exactly
zero bytes. Extra trailing calldata remains permitted. This is not admission
of nonempty no-return bodies, state-reading view expressions or dynamic ABI.

`SolidityMethodContract` composes these methods with existing expression methods
through `SolidityDispatch`: every method keeps a canonical-call witness, selectors
must be unique, and the complete runtime starts at PC zero for every sized input.
The original expression-contract definitions and statements are retained;
their proofs now consume the same dispatch, metering and deployment lemmas.
Neither an empty body nor an unused parameter removes a runtime obligation.
The complete unchanged OpenZeppelin 5.0.2 `ERC165MissingData` unit is 168 bytes,
SHA-256 `134040e5061063097ee712a3ba9ee0ab9448ed6ed0bfd60563d081267b3a5b65`.
Its original request/settings are outside the selected Cancun artifact claim.
The [ABI fixed-byte encoding](https://docs.solidity.org/en/latest/abi-spec.html#formal-specification-of-the-encoding)
informs the admitted layout; it does not establish our source-adapter or
compiler-correctness obligations. Exact emitted traces check both acceptance
and rejection, including padding, against this explicit source model.

The same Cancun semantic model, exact execution/code-deposit gas policy and
post-admission creation boundary apply. Transaction admission/fees, creator
nonce/address derivation, explicit constructors, storage and external calls remain
outside this route. Proof generation still bounds runtime/creation size to
1024/2048 bytes and may reject correct artifacts, including unfamiliar layouts.
As in [verified translation validation](https://xavierleroy.org/publi/validation-regalloc.pdf),
sound acceptance does not require a proof of the transformation algorithm or
complete acceptance of its outputs. General frontend/backend passes and the
compiler-wide final claim remain open in the map.

Run `python3 test/lean/check_compiler_contracts.py --corpus --jobs 4 --output <new-dir>`.
The gate binds exact requests, responses, tool and source identities; checks every
contract and corruption control; and replays all certificate dependencies in fresh
packages. The single-function corpus remains the regression gate for shared
source admission, bytecode proof generation and creation composition.

The payable slice uses the complete unchanged 490-byte OpenZeppelin 4.9.0
`contracts/mocks/proxy/ClashingImplementation.sol`, SHA-256
`c1060582801a54099373bf47dd2e1ba55de1f391223695108264b5f1f64aeafd`.
Its `admin()` is payable and `delegatedFunction()` is pure. The certificate covers
both functions with IPFS/CBOR metadata, complete creation and installed runtime;
the retained 282-source Osaka request remains uncertified. Archive/request/source
identities are pinned; missing upstream provenance is not invented. Mixed
checked/unchecked payable expressions and a wholly payable contract exercise
argument guards, panic, rollback and dispatch without a global value guard.
Four additional controls change each method's payability, erase the actual
nonpayable value guard, and erase a payable body's checked panic.

The contract corpus includes the complete 186-byte
`contracts/mocks/token/ERC20ExcessDecimalsMock.sol` from the retained
OpenZeppelin 5.6.1 request, whose source SHA-256 is
`f529e1171a2a93c8718f4d6731713889950238ebe69e344f21f72bf4af1f5446`.
`compiler_contract_corpus.py` pins the archive, request, provenance and source
identities. It preserves the retained source contents, including the corpus's
preexisting wildcard-pragma normalization, and records the source-key change to
`Function.sol`. The selected unit is recompiled under this route's Cancun/no-CBOR
settings. The original Osaka request and its other 337 sources are not certified;
their omission, original settings digest and capture transforms remain explicit
in the manifest and case report. No diagnostic source variant replaces the unit.
Its source/native maximum, public selector and creation-image controls remain
required. The shared storage regression includes a public reader initialized to
the same maximum.

The complete 215-byte `contracts/mocks/proxy/BadBeacon.sol` unit from the same
request has source SHA-256
`dbb600bc91b91a4ad052b0ea71ea9c216401786348afdd5ad4f9e78e9dc4e2d0`.
Its selected artifact is `BadBeaconNotContract`; `BadBeaconNoImpl` remains in
the parsed source but its artifact is not certified. The original source key and
Osaka settings, the certificate's explicit target/Cancun settings, and the other
337 omitted units remain distinct in the retained provenance. No stripped
diagnostic variant replaces the source. Its required corruption controls include wrong
address literal/value, 20-byte return, nonzero upper address bits, and a different
valid selected contract with the same selector. Runtime mutations update the
creation image too, so an installation mismatch cannot hide a semantic failure.
Zero and maximum-address fixtures, all prior function/contract/storage regressions,
complete non-vacuous creation/call certificates and fresh replay remain required.

The complete 493-byte `contracts/mocks/ClashingImplementation.sol` from the
retained OpenZeppelin 4.7.0 request has source SHA-256
`ddf71a32153b06df754b85593077e3b3871799f47aab407f6f6a86d9e204b737`.
Both `admin()` and `delegatedFunction()` belong to the selected certificate.
The archive, request and unchanged source bytes are pinned; the legacy archive
has no provenance sidecar, so upstream commit and capture transforms are recorded
as unknown. The original settings and other 269 units remain uncertified.
Acceptance now requires fifteen complete contract artifacts and twenty-six
semantic corruption controls, including changed source literals, noncanonical
boolean value two and a shortened boolean ABI return. Boolean true/false and
bare-address boundary fixtures exercise the extension; all prior controls,
function/storage regression gates and fresh replay remain required.
The additional metadata-bearing artifacts cover the complete retained contract
and checked ADD/SUB/MUL. New controls preserve creation while truncating or
changing the advertised runtime trailer, and retain both byte images while
changing the source's boolean result. No altered source variant replaces the
complete corpus unit for acceptance. The original Osaka request and its other
269 source units remain uncertified.

## Complete word and Boolean storage artifact route

`artifact.solidityStorage` checks the ordinary Solidity pipeline's exact creation
and runtime bytes against an independently admitted complete source contract.
It reuses word expressions, checked arithmetic, ABI selectors and the existing
Cancun stateful EVM model. The source statement spine admits one to eight
private `uint256`/`bool` declarations, up to eight external or public functions,
and an optional payable `receive()` entry. At least one callable entry is required.
Bodies admit sequential assignments, braced `if`/`else` arms, branch joins,
word or empty returns and bare `revert()`. Word-return functions require explicit
return/revert on every path; no-return functions and receive also allow fallthrough
and bare return. Conditions read Boolean fields/arguments or compare word expressions using `==`,
`!=`, `<`, `<=`, `>` or `>=`, and compose them with `!`, `&&`, `||`, parentheses
and Boolean literals. Boolean equality, word truthiness and expression side effects
remain unsupported. Each function has at most eight arguments, eight
assignments, four branches, 32 statements and 128 combined word/condition nodes. Pure/view
restrictions, declaration scope and all source text are checked; unsupported
constructs reject.

The statement evaluator follows Solidity's
[control-flow rules](https://docs.soliditylang.org/en/latest/control-structures.html):
conditions are Boolean, only the selected arm executes, and returns skip the
remaining statements. The admitted word expressions have no side effects and
only one possible panic code, so unspecified operand evaluation order is
unobservable. `Condition.eval` follows the specified
[Boolean short-circuit rules](https://docs.solidity.org/en/latest/types.html#booleans):
the left operand evaluates first; false `&&` and true `||` skip the right operand,
including its possible panic. The typed parser uses Solidity's
[operator precedence](https://docs.solidity.org/en/latest/cheatsheet.html#order-of-precedence-of-operators),
distinguishing grouped words from conditions without backtracking. Condition
panics stop before either arm. Proof hints split atomic comparisons and arithmetic
guards, including atoms in potentially skipped operands; these total logical
partitions never replace the short-circuit source evaluator. Proof hints substitute
the current store separately along each path, including statements after joins.
Per-path lemmas compose by exhaustive cases into the unconditional function
theorem; path conditions are not certificate assumptions. More than 64 proof
partitions or a symbolic expression exceeding 8192 characters rejects explicitly.

Storage starts at slot zero in declaration order, following Solidity's
[storage layout specification](https://docs.soliditylang.org/en/latest/internals/layout_in_storage.html).
Boolean fields pack into successive low-order bytes; each full word aligns to a
fresh slot when the previous slot is partially occupied. Lean derives locations
from the typed declaration list, without compiler layout metadata. A Boolean
read normalizes any nonzero byte; a write stores zero or one while preserving
all neighboring and unused bits. Other narrow types, inheritance, custom layout
and transient storage remain unsupported. Expressions read the current store after preceding assignments; overflow
panics retain their exact bytes, and a failed frame rolls back earlier writes.

The shared typed ABI admits Boolean argument words only when exactly zero or one.
Complete dispatch distinguishes empty calldata (receive), one to three bytes
(rejection), unknown selectors (rejection), and selected methods with their own
payability, length and canonicality checks. Receive is payable and accepts only
empty calldata. Fallback functions and Boolean return values remain unsupported.

Declaration initializers evaluate checked word expressions in declaration order
from zero storage, including earlier, forward and self references. All names
resolve against the complete source declaration inventory, with at most eight
initializers and 128 combined initializer expression nodes. Boolean declaration
initializers remain unsupported; Boolean assignments in constructors are admitted.
This follows the
[viaIR initialization order](https://docs.soliditylang.org/en/latest/ir-breaking-changes.html):
zero initialization precedes variable initialization and the constructor body.
An optional parameterless constructor runs afterward, following the
[constructor initialization rules](https://docs.soliditylang.org/en/latest/contracts.html#constructors).
It reuses the same assignments, comparisons and statement evaluator, permits
bare early returns and may be payable. Its entire body is either checked or
unchecked; initializers remain checked in both cases. It has the same statement,
write, branch and expression-node limits as a function. Declarations must come
first; the constructor may appear among the external functions. Constructor
arguments, inheritance, initializer/body calls and context reads remain unsupported.
Absent an explicit constructor, the model uses an empty nonpayable body.

`SolidityStorage.Constructor.certify` is the composed certificate: complete source dispatch,
every function's body, exact initcode/runtime identity, all creation failure
observations, initializer and constructor effects on the entire store, and calls
in the resulting world. Initialization and constructor endpoints share the
`Creation.certify` frame and installation proof. Successful source creation has a fresh deployment witness with
sufficient gas. An initializer that panics instead requires its exact revert
bytes and rollback; a successful deployment is not assumed. Nonpayable rejection,
execution/SSTORE-sentry failure and code-deposit failure retain their frame
observations, including nonce preparation and transaction rollback. The source
evaluator's zero starting store is discharged from the existing fresh-target
admission, not imposed on later calls. Each function also has a canonical valid
ABI-call witness. Runtime proofs
quantify over arbitrary original/current storage, warm slots, signed refunds and
static mode. Successful returns preserve the entire store, including undeclared
slots. Reverts and exceptions restore the world and transaction observations.
The shared model implements [static-write restrictions](https://eips.ethereum.org/EIPS/eip-214)
and the [SSTORE gas sentry](https://eips.ethereum.org/EIPS/eip-2200).

The source relation observes return/revert bytes and persistent storage, with
gas opaque at source level. The *same exact target trace* determines execution
gas for every budget, access warming and signed refunds, including rollback.
It does not require optimization to preserve the source's sequence of accesses:
the overwrite fixtures check eliminated earlier stores, including initializers
overwritten by constructor code after an intervening write. `write_shadow`
proves that whole-store equality even if the two keys alias. RHS arithmetic precedes
the static-write exception in the source model. An optimizer that removes such
a write or changes exception precedence may be rejected by this conservative
profile. The native `static_store_before_revert` fixture records this boundary:
the compiler removes a Boolean store before unconditional empty revert, while the
source model faults at that store in static mode. Its certificate must reject;
the gate retains the actual request/response separately from artificial mutations.
This is not a confirmed compiler bug. Acceptance is sound for its declared
relation; it is not complete.

The frozen trust assumptions are unchanged: `lean.kernel`, `model.adequacy` and
`artifact.binding`. The source parser remains trusted. Host allocation/layout
proofs are not premises of this artifact route. General frontend/backend passes,
external calls, mappings, loops, constructor arguments and general constructor bodies, transaction admission,
fees and address derivation remain open. Calls admit calldata below 2^64 bytes;
proof generation caps creation/runtime at 2048/1024 bytes with runtime at the
tail when the return-copy hint is used. Statically reverting creation code may
omit that image; the complete execution proof must still establish source
reversion, and every successful creation trace must return the exact runtime.
Unsupported instructions, exhausted proof budgets or any failed check
reject the artifact rather than manufacture completeness.

Run `python3 test/lean/check_compiler_storage.py --corpus --jobs 4 --output <new-dir>`.
The 49-contract corpus includes sequential reads, overflow after a preceding
write, overwritten stores, clear/getters, static mode, eight slots/arguments,
nested branches, joined writes, early returns, condition panics, four branches,
initializer dependencies, forward/self reads, zero initializers and initializer
panic; explicit constructor writes, dependencies, branches, early exit, checked
panic, unchecked wrap and payability; compound Boolean precedence, grouping,
negation, checked/unchecked operands, skipped/reached panics and constructor
short-circuiting. It also includes the complete unchanged OpenZeppelin 5.6.1
`EtherReceiverMock`, packed neighboring flags, mixed word/Boolean layout,
payable setters, receive-only dispatch, early empty returns, explicit reverts
and constructor rollback. Fifty-five mutation controls corrupt source/store/dispatch behavior, branch
predicates, joined reads, early returns, initialization, panic bytes or the creation
image, constructor order, payability and arithmetic mode, Boolean operators,
grouping, negation and eager evaluation, Boolean canonicality, packed-byte
clearing/location, receive routing and empty return/revert behavior. The additional
native rejection described above must fail semantically, without a resource or
syntax failure being accepted as evidence. Independent model theorems check skipped
and reached operands, left-operand panic propagation, skipped arms, return order, static-write
behavior, initialization order, deployment gas boundaries and rollback.
Fresh kernel replay checks complete dependencies in bounded
batches; the existing function and contract gates cover shared admission and
proof generation. CI runs all three routes. These are scoped artifact endpoints,
not a claim that the whole compiler is verified.

## Recursive optimizer failure artifacts

`artifact.graphFailure` makes the reached graph on allocation failure a checked
artifact. `Compiler.Validation.Failure.certify` proves that each accepted
observation preserves all successfully returned source-prefix IDs and every
captured cache binding, for every word environment. The entire reached graph
must evaluate, including representatives created by recursive calls before an
outer call fails. The theorem requires exact progress: a completed observation
has all input results; an OOM observation has a strict prefix. It does not
invent rollback or treat a failed compilation as successful.

`check_compiler_graph_failures.py` consumes hash-bound production observations.
The opt-in graph adapter first measures a successful run, then fails every
counted compiler allocation in order. Resizing/remapping always fails, forcing
growth through counted allocations. Metadata and serialization use a separate
allocator; their failures reject capture. All representatives and cache entries
are read before the actual interner is destroyed. Allocation balance after
destruction is a native diagnostic, not a kernel memory-safety theorem. The
existing successful-graph and word-block routes reuse the same request driver
and graph projection, without the failure sweep.

The gate checks complete cut coverage and replays fresh kernel certificates for
each source graph's observation family. It rejects missing cuts, stale inputs,
unsupported outcomes and resource limits. Semantic corruption controls alter
earlier results, partial cache entries and progress while retaining an admitted
artifact shape. The frozen `artifact.binding` assumption still includes native
capture and prefix completeness; `model.adequacy` covers the pure word model.
These certificates do not prove native ownership, other allocator schedules,
arbitrary future graph mutation, full recursive implementation preservation or
source-to-bytecode correctness. The general optimizer obligation remains open.

## Maintaining coverage

Run `python3 test/lean/check_verification_map.py`. It checks references, dependency
closure, claim categories and the exact registered Yul step inventory. Its JSON
summary distinguishes closed contracts/models, scoped artifact routes and
complete production operations. It does **not** replay proofs or turn declared
coverage into a certificate. The referenced acceptance gates remain required.

The report groups each production entry point by its declared closed, partial
and open scopes, deduplicating functions shared by several obligations. It
reports unresolved transitive dependencies for each prioritized milestone and
selects the first unfinished priority. Scope identifiers refer back to the map's
supported semantics, assumptions, unsupported cases and acceptance contracts;
they are not unrestricted function-level verification claims. Final-claim
implementation dependencies and scoped artifact-validator routes are reported
separately. No current artifact is accepted by this inventory check, and no
percentage is computed from an explicitly incomplete inventory.

The map currently inventories major viaIR boundaries and all registered Yul
steps, not every compiler helper or configuration. Its explicit inventory gaps
must be closed before claiming compiler-wide coverage. Registry membership does
not mean a step executed for a particular request. Per-artifact acceptance must
continue binding the actual artifacts and settings.

After normalization/recursive composition, prioritize frontend lowering and EVM
backend connections, using artifact validators where implementation proofs would
delay useful coverage. Expand the exporter described in
[the restricted AIR tooling](../lean/zig_air/README.md) only for concrete functions blocking these
obligations; a general Zig translator is not a prerequisite.
