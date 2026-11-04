#!/usr/bin/env python3
"""Check the memory-identity boundary of native empty-key publication.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import copy
import json
from pathlib import Path
import sys

import check_owned_keys_physical as physical
from check_word_swap import ROOT, lean_check, prove
from build_toolchain import digest, run, write_json
from check_zig_air_proofs import mutation_check
from lean_control_matrix import ControlPlan
from check_zig_air_memory_proofs import without_imports
import extract_graph_init
import extract_owned_keys
import check_native_invocation as expressions
from constructor_joint_checks import app, path
from native_resource_admission_checks import telescope
from native_checkpoint_constructor_checks import numeral
from assembly_item_creation_checks import checked_controls

MODULE = 'Compiler.Extraction.InternerPublicationMemoryBoundaryTests'
NS = physical.NS
PUBLICATION = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication.'
TESTS = NS + 'MemoryBoundaryTests.'
CORE = [NS + 'run_empty_memory'] + [PUBLICATION + n for n in (
    'empty_memory', 'empty_map_size', 'changed_map_size_not_identity', 'first_map_entry_not_identity')]
REGRESSIONS = [TESTS + n for n in ('captured_count_layout', 'nonempty_changes_memory', 'empty_changes_effects')]
CLAIMS = physical.CLAIMS + CORE + REGRESSIONS
MODES = ('Debug', 'ReleaseSafe', 'ReleaseFast')
ALLOCATIONS = {'allocations', 'deallocations', 'allocated_bytes', 'freed_bytes', 'resizes', 'induced_failure'}
SNAPSHOT = {'owner_address', 'map_size_address', 'map_size', 'map_capacity', 'map_available', 'map_metadata',
            'map_unlocked', 'representative_count', 'representative_capacity', 'representative_storage',
            'representative_item', 'cached_id', 'allocator'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def fields(value, expected, label):
    require(type(value) is dict and set(value) == expected, label + ': unexpected fields')


def natural(value):
    return type(value) is int and 0 <= value < 2**64


def allocations(value):
    fields(value, ALLOCATIONS, 'allocator')
    require(all(natural(value[k]) for k in ALLOCATIONS - {'induced_failure'}) and
            type(value['induced_failure']) is bool, 'allocator: invalid counters')


def check_profile(value, mode):
    """Validate all retained observations; no mutation is inferred from pointers alone."""
    fields(value, {'schema', 'zigVersion', 'mode', 'backend', 'arch', 'os', 'pointer_bits', 'owner_size', 'observation'}, 'profile')
    require(value['schema'] == 'oksolc.native-map-memory-boundary.v1' and value['zigVersion'] == '0.17.0' and
            value['mode'] == mode and value['backend'] == 'stage2_llvm', 'profile: wrong compiler/settings')
    require(value['arch'] == 'aarch64' and value['os'] == 'macos' and type(value['pointer_bits']) is int and
            value['pointer_bits'] == 64, 'profile: outside captured native ABI')
    size, offset = (56, 48) if mode == 'ReleaseFast' else (72, 64)
    require(type(value['owner_size']) is int and value['owner_size'] == size, 'profile: wrong owner layout')
    observed = value['observation']
    fields(observed, {'id', 'opcode', 'argument_count', 'cases', 'teardown'}, 'observation')
    require(all(type(observed[k]) is int for k in ('id', 'opcode', 'argument_count')) and
            [observed[k] for k in ('id', 'opcode', 'argument_count')] == [0, 88, 0], 'observation: wrong native input')
    require(type(observed['cases']) is list and len(observed['cases']) == 3, 'observation: incomplete cases')
    cases = observed['cases']
    for case, name in zip(cases, ('first-bucket-oom', 'first-bucket-success', 'cached-force')):
        fields(case, {'name', 'before', 'after', 'failure'}, 'case')
        require(case['name'] == name, 'case: wrong order')
        for state in (case['before'], case['after']):
            fields(state, SNAPSHOT, 'snapshot')
            allocations(state['allocator'])
            require(all(natural(state[k]) for k in SNAPSHOT - {'allocator', 'cached_id', 'map_unlocked'}),
                    'snapshot: invalid integer')
            require(state['map_unlocked'] is True, 'snapshot: native map lock retained')
            require(state['cached_id'] is None or (type(state['cached_id']) is int and state['cached_id'] == 0),
                    'snapshot: wrong cached id')
            require(state['owner_address'] > 0 and state['map_size_address'] - state['owner_address'] == offset,
                    'snapshot: wrong count field offset')
            require(state['representative_count'] == 1 and state['representative_capacity'] > 0 and
                    state['representative_storage'] > 0 and state['representative_item'] > 0,
                    'snapshot: missing native representative')
    seed = cases[0]['before']
    frame = SNAPSHOT - {'map_size', 'map_capacity', 'map_available', 'map_metadata', 'cached_id', 'allocator'}
    for case in cases:
        for state in (case['before'], case['after']):
            require(all(state[k] == seed[k] for k in frame), 'snapshot: representative/owner frame changed')
    require([seed[k] for k in ('map_size', 'map_capacity', 'map_available', 'map_metadata', 'cached_id')] ==
            [0, 0, 0, 0, None], 'seed: map was already populated')
    a = seed['allocator']
    require(a['allocations'] == 2 and a['deallocations'] == a['freed_bytes'] == a['resizes'] == 0 and
            a['allocated_bytes'] > 0 and a['induced_failure'] is False, 'seed: unexpected allocations')
    oom = copy.deepcopy(seed)
    oom['allocator']['induced_failure'] = True
    require(cases[0]['failure'] == 'OutOfMemory' and cases[0]['after'] == oom,
            'oom: refusal must retain map and allocations')
    require(cases[1]['before'] == oom and cases[1]['failure'] is None, 'success: retry did not follow refusal')
    created = cases[1]['after']
    require([created[k] for k in ('map_size', 'map_capacity', 'map_available', 'cached_id')] == [1, 8, 5, 0] and
            created['map_metadata'] > 0, 'success: native map did not publish one entry')
    allocated = created['allocator']
    require(allocated['allocations'] == 3 and allocated['allocated_bytes'] > a['allocated_bytes'] and
            all(allocated[k] == oom['allocator'][k] for k in ALLOCATIONS - {'allocations', 'allocated_bytes'}),
            'success: expected exactly one bucket allocation')
    cached = copy.deepcopy(created)
    cached['allocator']['induced_failure'] = False
    require(cases[2]['before'] == cached and cases[2]['after'] == cached and cases[2]['failure'] is None,
            'hit: cached force changed native state or attempted allocation')
    allocations(observed['teardown'])
    final = {**cached['allocator'], 'deallocations': 3, 'freed_bytes': allocated['allocated_bytes']}
    require(observed['teardown'] == final, 'teardown: allocations leaked or unexpected effects occurred')
    return {'mode': mode, 'ownerBytes': size, 'countOffset': offset, 'oomRetainsEmptyMap': True,
            'successfulCount': [0, 1], 'bucketAllocations': 1, 'cachedForceAllocations': 0, 'allAllocationsFreed': True}


def observation_controls(profiles):
    """Corrupt actual captured observations, never a substitute execution fixture."""
    records = []
    for mode, original in profiles.items():
        changes = (
            ('missing-oom', ('observation', 'cases', 0, 'failure'), None),
            ('unchanged-count', ('observation', 'cases', 1, 'after', 'map_size'), 0),
            ('boolean-count', ('observation', 'cases', 1, 'after', 'map_size'), True),
            ('changed-frame', ('observation', 'cases', 1, 'after', 'representative_item'), 1),
            ('allocation-on-hit', ('observation', 'cases', 2, 'after', 'allocator', 'induced_failure'), True),
            ('leak', ('observation', 'teardown', 'deallocations'), 2),
            ('wrong-layout', ('owner_size',), 0),
        )
        for name, path, replacement in changes:
            value = copy.deepcopy(original)
            target = value
            for key in path[:-1]:
                target = target[key]
            require(target[path[-1]] != replacement or type(target[path[-1]]) is not type(replacement),
                    'ineffective observation control: ' + name)
            target[path[-1]] = replacement
            try:
                check_profile(value, mode)
            except ValueError as error:
                records.append({'mode': mode, 'name': name, 'rejection': str(error)})
            else:
                raise ValueError('accepted corrupted native observation: ' + name)
    return records


def boundary_controls(output, env, lean):
    source = (ROOT / 'lean/Compiler/Extraction/InternerPublicationMemoryBoundary.lean').read_text()
    tests = without_imports((ROOT / 'lean/Compiler/Extraction/InternerPublicationMemoryBoundaryTests.lean').read_text())
    source = 'import Compiler.Extraction.OwnedKeysPhysicalTests\n' + source + '\n' + tests
    records = [mutation_check(output, 'boundary-unchanged', source, True, env, lean)]
    mutations = (
        ('drop-empty-guard', '(empty : key.arguments = [])', '(empty : True)'),
        ('zero-inserted-count', '(.int false 32 1)', '(.int false 32 0)'),
        ('forget-allocator-effect', 'empty.memory.effects := by', '(run (probe false) external 7 emptyKey ⟨2, 5⟩ empty).2.memory.effects := by'),
    )
    for name, before, after in mutations:
        require(before in source, 'missing boundary mutation: ' + name)
        records.append(mutation_check(output, 'boundary-' + name, source.replace(before, after, 1), False, env, lean))
    return checked_controls(output, records)


def audit_boundary(rows):
    """Bind the compiled claims to actual arguments and both native field observations."""
    indexed = {row['theorem']: row for row in rows}
    normalization = 'Compiler.Extraction.Memory.Arguments.Normalization.'
    world = normalization + 'OwnedCall.World.memory'
    session = normalization + 'Session.memory'
    count = 'Compiler.Extraction.ExpressionMap.readSize'
    parameters = ['σ', 'hostProbe', 'host', 'allocator', 'source', 'key', 'owned', 'id', 'before', 'empty']
    dependencies = {
        CORE[0]: {NS + 'run', NS + 'operations', normalization + 'free_empty'},
        CORE[1]: {CORE[0], PUBLICATION + 'publish', PUBLICATION + 'commit'},
        CORE[2]: {CORE[1], count},
        CORE[3]: {CORE[2]},
        CORE[4]: {CORE[3]},
        REGRESSIONS[0]: {'Compiler.Extraction.RepresentativeArray.Owner.layout',
                         'Compiler.Extraction.RepresentativeArray.Owner.expressionsOffset',
                         'Compiler.Extraction.ExpressionMap.sizeOffset'},
        REGRESSIONS[1]: {NS + 'Tests.replacement'},
        REGRESSIONS[2]: {NS + 'Tests.empty_sentinel'},
    }
    for name, needed in dependencies.items():
        require(needed <= set(indexed[name]['dependencies']), 'boundary lost composition: ' + name)
    for name in CORE:
        require(not any(part.endswith('Tests') for dep in indexed[name]['dependencies'] for part in dep.split('.')),
                'general boundary depends on a fixture')
        value = indexed[name]['statement']
        fields, lets, root, context = telescope(value)
        expected = (['σ', 'probe', 'external', 'allocator', 'key', 'incoming', 'before', 'empty']
                    if name == CORE[0] else parameters[:])
        if name in CORE[2:]:
            expected += ['safety', 'owner']
        if name in CORE[3:]:
            expected += ['nativeAfter'] + (['changed'] if name == CORE[3] else ['initial', 'inserted'])
        require(list(fields) == expected and not lets, 'boundary gained a premise or replaced its inputs: ' + name)
        term, scope = fields['empty']
        empty = app(value, term, 'Eq')
        path(value, empty[-2], scope, ('Compiler.Extraction.Cache.Key.arguments',), 'key')
        app(value, empty[-1], 'List.nil')

        def before_memory(term, scope):
            path(value, term, scope, (session, NS + 'State.memory' if name == CORE[0] else world), 'before')

        def after_memory(term, scope):
            term = app(value, term, session)[-1]
            term = app(value, term, NS + 'State.memory' if name == CORE[0] else world)[-1]
            term = app(value, term, 'Prod.snd')[-1]
            call = app(value, term, NS + 'run' if name == CORE[0] else PUBLICATION + 'publish')
            require([expressions.named(value, a, scope) for a in call] == expected[:expected.index('empty')],
                    'boundary changed actual execution arguments')

        def read_count(term, scope, memory):
            args = app(value, term, count)
            require(len(args) == 3 and expressions.named(value, args[0], scope) == 'safety' and
                    expressions.named(value, args[2], scope) == 'owner', 'boundary changed native count address')
            memory(args[1], scope)

        def native_memory(term, scope):
            require(expressions.named(value, term, scope) == 'nativeAfter', 'boundary rebound native post-state')

        conclusion = app(value, root, 'Ne' if name in CORE[3:] else 'Eq')
        if name == CORE[2]:
            read_count(conclusion[-2], context, after_memory)
            read_count(conclusion[-1], context, before_memory)
        else:
            after_memory(conclusion[-2], context)
            (native_memory if name in CORE[3:] else before_memory)(conclusion[-1], context)
        if name == CORE[3]:
            term, scope = fields['changed']
            comparison = app(value, term, 'Ne')
            read_count(comparison[-2], scope, native_memory)
            read_count(comparison[-1], scope, before_memory)
        if name == CORE[4]:
            for field, number, memory in (('initial', 0, before_memory), ('inserted', 1, native_memory)):
                term, scope = fields[field]
                equality = app(value, term, 'Eq')
                read_count(equality[-2], scope, memory)
                scalar = app(value, app(value, equality[-1], 'Except.ok')[-1], 'Compiler.ZigAir.Memory.Value.scalar')[-1]
                integer = app(value, scalar, 'Compiler.ZigAir.Scalar.Value.int')
                require(expressions.named(value, integer[0], scope) == 'Bool.false', 'boundary changed count signedness')
                numeral(value, integer[1], 32)
                numeral(value, integer[2], number)
    for name in REGRESSIONS:
        fields, lets, _, _ = telescope(indexed[name]['statement'])
        require(not fields and not lets, 'boundary regression gained a premise')
    layout = indexed[REGRESSIONS[0]]['statement']
    term = app(layout, layout['root'], 'Eq')[-1]
    for number in (72, 64, 56):
        pair = app(layout, term, 'Prod.mk')
        numeral(layout, pair[-2], number)
        term = pair[-1]
    numeral(layout, term, 48)
    return {'checkedStatements': CORE + REGRESSIONS, 'actualPublicationMemoryFramed': True,
            'countObservationsRequired': [0, 1], 'nativeMapRefinementDerived': False}


def inputs():
    result = physical.inputs(caller=True)
    for name in ('native_map_memory.zig', 'expression_map_buckets.zig', 'expression_map_equality.zig', 'expression_map_probe.zig', 'expression_hash_input.zig', 'wyhash_local.zig', 'wyhash_hash.zig', 'wyhash_air.zig', 'expression_hash_air.zig', 'representative_array_layout.zig'):
        path = ROOT / 'test/lean' / name
        result[str(path.relative_to(ROOT))] = digest(path)
    return result


def std_inputs(lib):
    result = {str(path.relative_to(lib)): digest(path) for path in sorted(lib.rglob('*.zig'))}
    require(bool(result), 'missing Zig library inputs')
    return result


def check(args):
    if args.wyhash_hash and getattr(args, 'air_toolchain', None) is None:
        raise ValueError('hash preflight/accept requires --air-toolchain for captured initializer binding')
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {'schema': 'oksolc.native-map-memory-acceptance.v1', 'status': 'failed', 'jobs': 4,
              'proofTimeoutSecondsPerPhase': args.proof_timeout,
              'scope': 'empty-key publication memory frame and source-bound first native map insertion observations',
              'memoryIdentityBoundaryVerified': False, 'nativeHashMapVerified': False,
              'nativeGraphMapFieldFrameVerified': False,
              'nativeGraphPrivateReservationFrameVerified': False,
              'nativeBucketReservationGeometryVerified': False,
              'nativeBucketHeaderInitializationVerified': False,
              'nativeBucketAllocationVerified': False,
              'nativeMapLocalDeclarationVerified': False,
              'nativeMapLocalLockVerified': False,
              'nativeMapMetadataInitializationVerified': False,
              'nativeMapPreRehashInitializationVerified': False,
              'nativeMapCapacityPreparationVerified': False,
              'nativeMapKeyAssignmentVerified': False,
              'nativeMapEntryAssignmentVerified': False,
              'nativeSelectedNewSlotPublicationVerified': False,
              'nativeSelectedAbsentTableCorrespondenceVerified': False,
              'nativePostHashProbeVerified': False,
              'nativeReceiverSearchVerified': False,
              'nativeHashInputBytesVerified': False,
              'wyhashLocalCellTailVerified': False,
              'wyhashLongKeyLocalFinalizationVerified': False,
              'wyhashCompleteLocalHashConsumed': False,
              'composedProductionTheoremVerified': False, 'wholeCompilerVerified': False,
              'remaining': ['prove a projection of native private map storage or extend the publication interface',
                            'native bucket/probing/key-pointer refinement and preservation',
                            'full native admission, production composition and termination']}
    try:
        require(args.proof_timeout > 0, 'proof phase timeout must be positive')
        module, roots = MODULE, CLAIMS
        include_wyhash_final = args.wyhash_final or args.wyhash_hash
        include_wyhash_local = args.wyhash_local or include_wyhash_final
        include_hash_input = args.hash_input or include_wyhash_local
        include_search = args.receiver_search or include_hash_input
        include_probing = args.probing or include_search
        include_candidates = args.candidates or include_probing
        include_tables = args.tables or include_candidates
        include_insertions = args.insertions or include_tables
        include_entries = args.entries or include_insertions
        include_keys = args.keys or include_entries
        include_capacity = args.capacity or include_keys
        include_ready = args.ready or include_capacity
        include_metadata = args.metadata or include_ready
        include_locks = args.locks or include_metadata
        include_locals = args.locals or include_locks
        include_receivers = args.receivers or include_locals
        include_headers = args.headers or include_receivers
        include_buckets = args.buckets or include_headers
        include_regions = args.regions or include_buckets
        include_writes = args.writes or include_regions
        if include_writes:
            import native_map_write_checks as writes
            module, roots = writes.MODULE, roots + writes.CLAIMS
            report['scope'] += '; arbitrary valid map-field writes preserve existing native graph/query/ownership facts'
        if include_regions:
            import native_private_region_checks as regions
            module, roots = regions.MODULE, roots + regions.CLAIMS
            report['scope'] += '; private region reservation preserves those facts for every outcome, retaining native memory and allocator effects'
        if include_buckets:
            import native_bucket_reservation_checks as buckets
            module, roots = buckets.MODULE, roots + buckets.CLAIMS
            report['scope'] += '; source-bound native bucket request geometry consumes the private reservation frame'
        if include_headers:
            import native_bucket_storage_checks as headers
            module, roots = headers.MODULE, roots + headers.CLAIMS
            report['scope'] += '; actual private header fields are initialized in the typed allocation, preserving native graph facts'
        if include_receivers:
            import native_map_allocation_checks as allocation
            module, roots = allocation.MODULE, roots + allocation.CLAIMS
            report['scope'] += '; complete bucket allocate publishes metadata into its admitted standalone receiver'
        if include_locals:
            import native_map_local_checks as local
            module, roots = local.MODULE, roots + local.CLAIMS
            report['scope'] += '; local stack declaration and defaults derive the receiver consumed by bucket allocation after grow guards'
        if include_locks:
            import native_map_lock_checks as locks
            module, roots = locks.MODULE, roots + locks.CLAIMS
            report['scope'] += '; local lock consumes the derived defaults preserved through allocation'
        if include_metadata:
            import native_map_metadata_checks as metadata
            module, roots = metadata.MODULE, roots + metadata.CLAIMS
            report['scope'] += '; actual metadata/capacity reads derive packed-byte clearing and retain the native graph frame'
        if include_ready:
            import native_map_ready_checks as ready
            module, roots = ready.MODULE, roots + ready.CLAIMS
            report['scope'] += '; complete pre-rehash initialization derives insertion room and empty logical lookup'
        if include_capacity:
            import native_map_capacity_checks as capacity
            module, roots = capacity.MODULE, roots + capacity.CLAIMS
            report['scope'] += '; actual capacity/countdown reads derive capacity selection and grow guards before preparation'
        if include_keys:
            import native_map_key_checks as keys
            module, roots = keys.MODULE, roots + keys.CLAIMS
            report['scope'] += '; checked native key assignment preserves graph facts and derives all field readbacks'
        if include_entries:
            import native_map_entry_checks as entries
            module, roots = entries.MODULE, roots + entries.CLAIMS
            report['scope'] += '; complete defined key/ID assignment derives both readbacks and retains metadata and graph facts'
        if include_insertions:
            import native_map_insertion_checks as insertions
            module, roots = insertions.MODULE, roots + insertions.CLAIMS
            report['scope'] += '; selected new-slot counter, metadata, undefined and publication effects preserve native graph facts'
        if include_tables:
            import native_map_table_checks as tables
            module, roots = tables.MODULE, roots + tables.CLAIMS
            report['scope'] += '; selected absent-key publication derives native/logical table correspondence from original binding and custody'
            report['remaining'] = ['derive hashing/probe selection, absence and slot admission from actual execution',
                                   'general existing-table/caller admission, growth rehash/owner installation and replacement retirement',
                                   'full native admission, production composition and termination']
        if include_candidates:
            import native_map_candidate_checks as candidates
            module, roots = candidates.MODULE, roots + candidates.CLAIMS
            report['scope'] += '; native argument/key equality and selected lookup candidate derived from original table and custody'
        if include_probing:
            import native_map_probe_checks as probing
            module, roots = probing.MODULE, roots + probing.CLAIMS
            report['scope'] += '; complete post-hash probing derives absence and vacancy and maintains routing through new-slot publication'
            report['remaining'] = ['native Wyhash producer and capacity/size-zero caller prefix',
                                   'general initial/countdown admission, rehash/owner installation and replacement retirement',
                                   'full native admission, production composition and termination']
        if include_search:
            import native_map_search_checks as search
            module, roots = search.MODULE, roots + search.CLAIMS
            report['scope'] += '; source receiver reads supply count, capacity, bucket and repeated search observations around the explicit hash boundary'
            report['remaining'][0] = 'native incremental Wyhash producer; withHash is an explicit composition boundary'
        if include_hash_input:
            import native_hash_input_checks as hash_input
            module, roots = hash_input.MODULE, roots + hash_input.CLAIMS
            report['scope'] += '; actual hash byte inputs and arithmetic budget derived from original caller custody'
            report['remaining'][0] = 'native incremental Wyhash execution, including partial local initialization; the byte-input digest remains an explicit boundary'
        if include_wyhash_local:
            import native_wyhash_local_checks as wyhash
            module, roots = wyhash.MODULE, roots + wyhash.CLAIMS
            report['scope'] += '; typed partial local copy and finalization tail without initialized a/b premises'
            report['remaining'][0] = 'native incremental Wyhash buffers, update/final1 rounds and local heap admission; the complete digest remains open'
        if include_wyhash_final:
            import native_wyhash_final_checks as wyhash_final
            module, roots = wyhash_final.MODULE, roots + wyhash_final.CLAIMS
            report['scope'] += '; complete long-key local finalization from original initialized buffer regions, with derived scratch and tail words'
            report['remaining'][0] = 'native incremental Wyhash initialization/update and local heap admission; the complete digest remains open'
        if args.wyhash_hash:
            import native_wyhash_memory_checks as wyhash_hash
            module, roots = wyhash_hash.MODULE, roots + wyhash_hash.CLAIMS
            report['scope'] += '; complete local hashing and scoped heap allocation/cleanup consumed by stateful lookup/publication'
            report['remaining'][0] = 'extracted AIR instruction-order refinement of the scoped hash adapter, including update/copy/byte access and intermediate private stores; native hash producer remains open'
        report['inputs'], report['leanInputs'] = inputs(), lean_check.source_inputs()
        zig, lib = args.zig.resolve(), args.zig_lib_dir.resolve()
        report['zigSha256'], report['stdInputs'] = digest(zig), std_inputs(lib)
        report['graphBinding'] = extract_graph_init.check()
        report['stdBinding'] = extract_graph_init.check_std(lib)
        require(extract_owned_keys.extract(extract_owned_keys.SOURCE.read_bytes()) == extract_owned_keys.OUTPUT.read_bytes(),
                'publication source admission is stale')
        env, _, tools = lean_check.toolchain(args.lean_bin, 4)
        report['tools'] = tools
        run(output, 'source-admission', [sys.executable, 'test/lean/test_compiler_owned_keys.py'], cwd=ROOT, env=env)
        run(output, 'preflight', [tools['lake']['path'], 'build', module, 'Contract.Check.Declarations'], cwd=ROOT / 'lean', env=env)
        report['audit'] = physical.audit(output, env, tools['lean']['path'], module, roots)
        report['boundaryAudit'] = audit_boundary(json.loads((output / 'audit.json').read_bytes())['claims'])
        if include_writes:
            report['mapWritesAudit'] = writes.audit(json.loads((output / 'audit.json').read_bytes())['claims'])
        if include_regions:
            report['privateRegionsAudit'] = regions.audit(json.loads((output / 'audit.json').read_bytes())['claims'])
        if include_buckets:
            report['bucketAudit'] = buckets.audit(json.loads((output / 'audit.json').read_bytes())['claims'])
        if include_headers:
            report['headerAudit'] = headers.audit(json.loads((output / 'audit.json').read_bytes())['claims'])
        if include_receivers:
            report['allocationAudit'] = allocation.audit(json.loads((output / 'audit.json').read_bytes())['claims'])
            report['allocationSourceControls'] = allocation.source_controls(lib)
        if include_locals:
            report['localAudit'] = local.audit(json.loads((output / 'audit.json').read_bytes())['claims'])
            report['localSourceBinding'] = local.source_binding(lib)
            report['localSourceControls'] = local.source_controls(lib)
        if include_locks:
            report['lockAudit'] = locks.audit(json.loads((output / 'audit.json').read_bytes())['claims'])
            report['lockSourceBinding'] = locks.source_binding(lib)
            report['lockSourceControls'] = locks.source_controls(lib)
        if include_metadata:
            report['metadataAudit'] = metadata.audit(json.loads((output / 'audit.json').read_bytes())['claims'])
            report['metadataSourceBinding'] = metadata.source_binding(lib)
            report['metadataSourceControls'] = metadata.source_controls(lib)
        if include_ready:
            report['readyAudit'] = ready.audit(json.loads((output / 'audit.json').read_bytes())['claims'])
            report['readySourceBinding'] = ready.source_binding(lib)
            report['readySourceControls'] = ready.source_controls(lib)
        if include_capacity:
            report['capacityAudit'] = capacity.audit(json.loads((output / 'audit.json').read_bytes())['claims'])
            report['capacitySourceBinding'] = capacity.source_binding(lib)
            report['capacitySourceControls'] = capacity.source_controls(lib)
        if include_keys:
            report['keyAudit'] = keys.audit(json.loads((output / 'audit.json').read_bytes())['claims'])
            report['keySourceBinding'] = keys.source_binding(lib)
            report['keySourceControls'] = keys.source_controls(lib)
        if include_entries:
            report['entryAudit'] = entries.audit(json.loads((output / 'audit.json').read_bytes())['claims'])
            report['entrySourceBinding'] = entries.source_binding(lib)
            report['entrySourceControls'] = entries.source_controls(lib)
        if include_insertions:
            report['insertionAudit'] = insertions.audit(json.loads((output / 'audit.json').read_bytes())['claims'])
            report['insertionSourceBinding'] = insertions.source_binding(lib)
            report['insertionSourceControls'] = insertions.source_controls(lib)
        if include_tables:
            report['tableAudit'] = tables.audit(json.loads((output / 'audit.json').read_bytes())['claims'])
            report['tableInterfaces'] = tables.interfaces(output, env, tools['lean']['path'])
        if include_candidates:
            report['candidateAudit'] = candidates.audit(json.loads((output / 'audit.json').read_bytes())['claims'])
            report['candidateAuditControls'] = candidates.audit_controls(json.loads((output / 'audit.json').read_bytes())['claims'])
            report['candidateInterfaces'] = candidates.interfaces(output, env, tools['lean']['path'])
            report['candidateSourceBinding'] = candidates.source_binding(lib)
            report['candidateSourceControls'] = candidates.source_controls(lib)
        if include_probing:
            report['probeAudit'] = probing.audit(json.loads((output / 'audit.json').read_bytes())['claims'])
            report['probeAuditControls'] = probing.audit_controls(json.loads((output / 'audit.json').read_bytes())['claims'])
            report['probeInterfaces'] = probing.interfaces(output, env, tools['lean']['path'])
            report['probeSourceBinding'] = probing.source_binding(lib)
            report['probeSourceControls'] = probing.source_controls(lib)
        if include_search:
            report['searchAudit'] = search.audit(json.loads((output / 'audit.json').read_bytes())['claims'])
            report['searchAuditControls'] = search.audit_controls(json.loads((output / 'audit.json').read_bytes())['claims'])
            report['searchInterfaces'] = search.interfaces(output, env, tools['lean']['path'])
            report['searchSourceBinding'] = search.source_binding(lib)
            report['searchSourceControls'] = search.source_controls(lib)
        if include_hash_input:
            report['hashInputAudit'] = hash_input.audit(json.loads((output / 'audit.json').read_bytes())['claims'])
            report['hashInputAuditControls'] = hash_input.audit_controls(json.loads((output / 'audit.json').read_bytes())['claims'])
            report['hashInputInterfaces'] = hash_input.interfaces(output, env, tools['lean']['path'])
            report['hashInputSourceBinding'] = hash_input.source_binding(lib)
            report['hashInputSourceControls'] = hash_input.source_controls(lib)
        if include_wyhash_local:
            report['wyhashLocalAudit'] = wyhash.audit(json.loads((output / 'audit.json').read_bytes())['claims'])
            report['wyhashLocalAuditControls'] = wyhash.audit_controls(json.loads((output / 'audit.json').read_bytes())['claims'])
            report['wyhashLocalInterfaces'] = wyhash.interfaces(output, env, tools['lean']['path'])
            report['wyhashLocalSourceBinding'] = wyhash.source_binding(lib)
            report['wyhashLocalSourceControls'] = wyhash.source_controls(lib)
        if include_wyhash_final:
            report['wyhashFinalAudit'] = wyhash_final.audit(json.loads((output / 'audit.json').read_bytes())['claims'])
            report['wyhashFinalAuditControls'] = wyhash_final.audit_controls(json.loads((output / 'audit.json').read_bytes())['claims'])
            report['wyhashFinalInterfaces'] = wyhash_final.interfaces(output, env, tools['lean']['path'])
            report['wyhashFinalSourceBinding'] = wyhash_final.source_binding(lib)
            report['wyhashFinalSourceControls'] = wyhash_final.source_controls(lib)
        if args.wyhash_hash:
            report['wyhashHashAudit'] = wyhash_hash.audit(json.loads((output / 'audit.json').read_bytes())['claims'])
            report['wyhashHashAuditControls'] = wyhash_hash.audit_controls(json.loads((output / 'audit.json').read_bytes())['claims'])
            report['wyhashHashInterfaces'] = wyhash_hash.interfaces(output, env, tools['lean']['path'])
            report['wyhashHashSourceBinding'] = wyhash_hash.source_binding(lib)
            report['wyhashHashSourceControls'] = wyhash_hash.source_controls(lib)
        control_plan = ControlPlan(output, env, tools['lean']['path'])
        controls = physical.controls(output, env, control_plan)
        controls += boundary_controls(output, env, control_plan)
        if include_writes:
            controls += writes.controls(output, env, control_plan)
        if include_regions:
            controls += regions.controls(output, env, control_plan)
        if include_buckets:
            controls += buckets.controls(output, env, control_plan)
        if include_headers:
            controls += headers.controls(output, env, control_plan)
        if include_receivers:
            controls += allocation.controls(output, env, control_plan)
        if include_locals:
            controls += local.controls(output, env, control_plan)
        if include_locks:
            controls += locks.controls(output, env, control_plan)
        if include_metadata:
            controls += metadata.controls(output, env, control_plan)
        if include_ready:
            controls += ready.controls(output, env, control_plan)
        if include_capacity:
            controls += capacity.controls(output, env, control_plan)
        if include_keys:
            controls += keys.controls(output, env, control_plan)
        if include_entries:
            controls += entries.controls(output, env, control_plan)
        if include_insertions:
            controls += insertions.controls(output, env, control_plan)
        if include_tables:
            controls += tables.controls(output, env, control_plan)
        if include_candidates:
            controls += candidates.controls(output, env, control_plan)
        if include_probing:
            controls += probing.controls(output, env, control_plan)
        if include_search:
            controls += search.controls(output, env, control_plan)
        if include_hash_input:
            controls += hash_input.controls(output, env, control_plan)
        if include_wyhash_local:
            controls += wyhash.controls(output, env, control_plan)
        if include_wyhash_final:
            controls += wyhash_final.controls(output, env, control_plan)
        if args.wyhash_hash:
            controls += wyhash_hash.controls(output, env, control_plan)
        report['controls'], report['controlMatrix'] = control_plan.seal(controls).run(args.control_workers)
        report['captures'] = []
        profiles = {}
        for mode in MODES:
            binary = output / ('native-' + mode)
            run(output, 'build-' + mode, [zig, 'build-exe', '-j4', '--zig-lib-dir', lib, '-fllvm', '-O', mode,
                '--dep', 'compiler', '-Mroot=' + str(ROOT / 'test/lean/native_map_memory.zig'), '-O', mode,
                '-Mcompiler=' + str(ROOT / 'src/modules.zig'), '--cache-dir', output / 'zig-cache',
                '--global-cache-dir', output / 'global-cache', '-femit-bin=' + str(binary)], cwd=ROOT, env=env)
            run(output, 'run-' + mode, [binary], cwd=ROOT, env=env)
            raw = (output / ('run-' + mode + '.stdout')).read_bytes()
            observation = output / ('observation-' + mode + '.json')
            observation.write_bytes(raw)
            report['captures'].append({'mode': mode, 'binarySha256': digest(binary),
                                       'observationSha256': digest(observation)})
            profiles[mode] = json.loads(raw)
            require(not (output / ('run-' + mode + '.stderr')).read_bytes(), 'native observation wrote stderr')
        report['profiles'] = [check_profile(value, mode) for mode, value in profiles.items()]
        report['observationControls'] = observation_controls(profiles)
        if include_buckets:
            report['bucketReservation'] = buckets.capture(output, zig, lib, env, header=include_headers)
        if include_capacity:
            run(output, 'capacity-parser-tests', [sys.executable, 'test/lean/test_native_map_capacity.py'], cwd=ROOT, env=env)
            report['capacityRequests'] = capacity.capture(output, env)
        if include_keys:
            run(output, 'key-parser-tests', [sys.executable, 'test/lean/test_native_map_key.py'], cwd=ROOT, env=env)
            report['keyAssignment'] = keys.capture(output, env)
        if include_entries:
            run(output, 'entry-parser-tests', [sys.executable, 'test/lean/test_native_map_entry.py'], cwd=ROOT, env=env)
            report['entryAssignment'] = entries.capture(output, env)
        if include_insertions:
            run(output, 'insertion-parser-tests', [sys.executable, 'test/lean/test_native_map_insertion.py'], cwd=ROOT, env=env)
            report['newSlotPublication'] = insertions.capture(output, env)
        if include_tables:
            run(output, 'table-parser-tests', [sys.executable, 'test/lean/test_native_map_table.py'], cwd=ROOT, env=env)
            report['tablePublication'] = tables.capture(output, env)
        if include_candidates:
            run(output, 'candidate-parser-tests', [sys.executable, 'test/lean/test_native_map_candidate.py'], cwd=ROOT, env=env)
            report['candidateEquality'] = candidates.capture(output, env)
        if include_probing:
            run(output, 'probe-parser-tests', [sys.executable, 'test/lean/test_native_map_probe.py'], cwd=ROOT, env=env)
            report['probeExecution'] = probing.capture(output, env)
        if include_search:
            run(output, 'search-parser-tests', [sys.executable, 'test/lean/test_native_map_search.py'], cwd=ROOT, env=env)
            report['searchExecution'] = search.capture(output, env)
        if include_hash_input:
            run(output, 'hash-input-parser-tests', [sys.executable, 'test/lean/test_native_hash_input.py'], cwd=ROOT, env=env)
            report['hashInputExecution'] = hash_input.capture(output, env)
        if include_wyhash_local:
            run(output, 'wyhash-local-parser-tests', [sys.executable, 'test/lean/test_native_wyhash_local.py'], cwd=ROOT, env=env)
            report['wyhashLocalExecution'] = wyhash.capture(output, env)
        if include_wyhash_final:
            run(output, 'wyhash-final-parser-tests', [sys.executable, 'test/lean/test_native_wyhash_final.py'], cwd=ROOT, env=env)
            report['wyhashFinalExecution'] = wyhash_final.capture(output, env)
        if args.wyhash_hash:
            run(output, 'wyhash-hash-parser-tests', [sys.executable, 'test/lean/test_native_wyhash_hash.py'], cwd=ROOT, env=env)
            report['wyhashHashExecution'] = wyhash_hash.capture(output, env)
            report['wyhashInitializerAir'] = wyhash_hash.initializer.capture(output, args.air_toolchain, lib)
        if not args.preflight:
            proof, artifacts = prove.check_module(module, roots, lean_bin=args.lean_bin, jobs=4,
                                                 timeout=args.proof_timeout, fresh=True)
            directory = output / 'proof'
            directory.mkdir()
            for name, data in artifacts.items():
                (directory / name).write_bytes(data)
            write_json(directory / 'report.json', proof)
            report['proofReportSha256'] = digest(directory / 'report.json')
            require(proof.get('status') == 'passed' and proof.get('freshKernelReplay') is True and
                    proof.get('replayIncludesImports') is True and proof.get('auditedDeclarations') == roots,
                    'memory boundary audit or fresh kernel replay failed')
        require(inputs() == report['inputs'] and lean_check.source_inputs() == report['leanInputs'] and
                digest(zig) == report['zigSha256'] and std_inputs(lib) == report['stdInputs'], 'acceptance inputs changed')
        report.update(status='preflight-passed' if args.preflight else 'passed',
                      memoryIdentityBoundaryVerified=not args.preflight, auditedDeclarations=len(roots),
                      nativeGraphMapFieldFrameVerified=include_writes and not args.preflight,
                      nativeGraphPrivateReservationFrameVerified=include_regions and not args.preflight,
                      nativeBucketReservationGeometryVerified=include_buckets and not args.preflight,
                      nativeBucketHeaderInitializationVerified=include_headers and not args.preflight,
                      nativeBucketAllocationVerified=include_receivers and not args.preflight,
                      nativeMapLocalDeclarationVerified=include_locals and not args.preflight,
                      nativeMapLocalLockVerified=include_locks and not args.preflight,
                      nativeMapMetadataInitializationVerified=include_metadata and not args.preflight,
                      nativeMapPreRehashInitializationVerified=include_ready and not args.preflight,
                      nativeMapCapacityPreparationVerified=include_capacity and not args.preflight,
                      nativeMapKeyAssignmentVerified=include_keys and not args.preflight,
                      nativeMapEntryAssignmentVerified=include_entries and not args.preflight,
                      nativeSelectedNewSlotPublicationVerified=include_insertions and not args.preflight,
                      nativeSelectedAbsentTableCorrespondenceVerified=include_tables and not args.preflight,
                      nativeLookupCandidateVerified=include_candidates and not args.preflight,
                      nativePostHashProbeVerified=include_probing and not args.preflight,
                      nativeReceiverSearchVerified=include_search and not args.preflight,
                      nativeHashInputBytesVerified=include_hash_input and not args.preflight,
                      wyhashLocalCellTailVerified=include_wyhash_local and not args.preflight,
                      wyhashLongKeyLocalFinalizationVerified=include_wyhash_final and not args.preflight,
                      wyhashCompleteLocalHashConsumed=args.wyhash_hash and not args.preflight)
    finally:
        write_json(output / 'report.json', report)
    print('Memory boundary ' + report['status'] + '; native hash-map refinement and production composition remain open.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-bin', type=Path)
    parser.add_argument('--zig', type=Path, required=True)
    parser.add_argument('--zig-lib-dir', type=Path, required=True)
    parser.add_argument('--air-toolchain', type=Path, help='capture toolchain report for hash initialization')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--preflight', action='store_true', help='cached proof/control/native checks only; no acceptance claim')
    parser.add_argument('--control-workers', type=int, choices=range(1, 5), default=4,
                        help='one bounded control pool; parallel controls use one Lean thread each')
    parser.add_argument('--proof-timeout', type=int, default=600,
                        help='bounded seconds per proof build/audit/fresh-replay phase (default: 600)')
    parser.add_argument('--writes', action='store_true', help='include general native map-field writes and graph preservation')
    parser.add_argument('--regions', action='store_true', help='also include private region reservation and map-field composition')
    parser.add_argument('--buckets', action='store_true', help='also bind native bucket allocation geometry to the private reservation frame')
    parser.add_argument('--headers', action='store_true', help='also derive private header initialization from the actual typed allocation')
    parser.add_argument('--receivers', action='store_true', help='also complete bucket allocate through standalone receiver publication')
    parser.add_argument('--locals', action='store_true', help='also derive the local declaration/defaults consumed by bucket allocation')
    parser.add_argument('--locks', action='store_true', help='also derive grow temporary-map locking from allocation-preserved defaults')
    parser.add_argument('--metadata', action='store_true', help='also derive packed metadata clearing from the actual locked allocation prefix')
    parser.add_argument('--ready', action='store_true', help='also derive complete pre-rehash initialization, insertion room and empty lookup')
    parser.add_argument('--capacity', action='store_true', help='also derive capacity selection and guards from actual map reads before preparation')
    parser.add_argument('--keys', action='store_true', help='also derive complete native key-field assignment and readback')
    parser.add_argument('--entries', action='store_true', help='also derive the complete defined key/ID assignment tail')
    parser.add_argument('--insertions', action='store_true', help='also derive the selected new-slot suffix through complete key/ID publication')
    parser.add_argument('--tables', action='store_true', help='also derive native/logical table correspondence for selected absent-key publication')
    parser.add_argument('--wyhash-local', action='store_true', help='also check partial scalar copy and the native local finalization tail; complete Wyhash remains open')
    parser.add_argument('--wyhash-hash', action='store_true', help='also check complete local hashing and scoped heap consumers; extracted AIR hash refinement remains open')
    parser.add_argument('--wyhash-final', action='store_true', help='also check complete long-key local finalization from the initialized buffer; incremental update and local heap admission remain open')
    parser.add_argument('--hash-input', action='store_true', help='also derive actual hash input bytes and arithmetic budget; native Wyhash remains open')
    parser.add_argument('--receiver-search', action='store_true', help='also derive receiver-based search and publication around the explicit hash boundary')
    parser.add_argument('--probing', action='store_true', help='also derive complete post-hash probing and compose new-slot publication')
    parser.add_argument('--candidates', action='store_true', help='also derive native key equality and lookup candidate from original table and custody')
    check(parser.parse_args())
