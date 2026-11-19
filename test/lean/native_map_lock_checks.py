"""Check grow's derived local lock, retaining allocation and field frames.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import hashlib
import check_native_invocation as expressions
from constructor_joint_checks import app
from native_resource_admission_checks import telescope
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check
from check_zig_air_memory_proofs import without_imports
from check_word_swap import ROOT
from native_map_write_checks import GRAPH, require
from native_map_allocation_checks import MAP, INIT
from native_map_local_checks import LOCAL
import native_map_local_checks as local

MODULE = 'Compiler.Extraction.ExpressionMapLocalLockTests'
TESTS = GRAPH + 'MapLockTests.'
CLAIMS = [INIT + 'load_frame_at', GRAPH + 'Facts.allocate_buckets_framed', GRAPH + 'Facts.prepare_buckets_framed']
CLAIMS += [LOCAL + n for n in ('lock_verified', 'lock_rejected', 'lock_without_safety')]
CLAIMS += [GRAPH + n for n in ('Facts.lock_buckets', 'lockBuckets_oom', 'lockBuckets_rejected', 'lockBuckets_exhausted')]
CLAIMS += [TESTS + n for n in ('from_initialized_owner', 'oom_keeps_defaults', 'exhausted_keeps_input')]


def source_binding(lib, native=None, debug=None):
    binding = local.source_binding(lib, native)
    debug = (lib / 'std/debug.zig').read_bytes() if debug is None else debug
    marker = b'pub const SafetyLock = struct {'
    require(debug.count(marker) == 1, 'missing or ambiguous SafetyLock')
    start = debug.index(marker)
    # The source tokenizer intentionally supports a subset of Zig. Unrelated
    # debug formatting contains other tokens; bind the complete file hash and
    # parse this uniquely named top-level declaration only.
    end = debug.index(b'\n};', start) + len(b'\n};')
    declaration = debug[start:end]
    local.admission.storage.function(declaration, 'pub const SafetyLock =').expect('''struct {
        state: State = if (runtime_safety) .unlocked else .unknown,
        pub const State = if (runtime_safety) enum(usize) {
            unlocked = 0, exclusive = math.maxInt(usize), _,''')
    local.admission.storage.function(declaration, 'pub fn lock(l: *SafetyLock) void').expect('''{
        if (!runtime_safety) return;
        assert(l.state == .unlocked);
        l.state = .exclusive;
    }''')
    digest = hashlib.sha256(debug).hexdigest()
    require(digest == local.admission.extract_graph_init.STD['debug.zig'], 'unreviewed SafetyLock source')
    return {**binding, 'debugSha256': digest, 'scope': 'local declaration, allocation and lock after grow guards',
            'metadataClearingVerified': False, 'sourceAdapterFormallyVerified': False}


def source_controls(lib):
    native = (lib / 'std/hash_map.zig').read_bytes()
    debug = (lib / 'std/debug.zig').read_bytes()
    records = []
    for owner, before, after in (
        ('native', b'map.pointer_stability.lock();', b'map.pointer_stability.unlock();'),
        ('debug', b'exclusive = math.maxInt(usize),', b'exclusive = 1,'),
        ('debug', b'assert(l.state == .unlocked);\n        l.state = .exclusive;',
         b'assert(l.state == .exclusive);\n        l.state = .exclusive;'),
        ('debug', b'l.state = .exclusive;', b'l.state = .unlocked;'),
        ('debug', b'pub fn lock(l: *SafetyLock) void {\n        if (!runtime_safety) return;',
         b'pub fn lock(l: *SafetyLock) void {\n        if (runtime_safety) return;'),
    ):
        source = native if owner == 'native' else debug
        require(source.count(before) == 1, 'ambiguous map lock source control')
        changed = source.replace(before, after, 1)
        try:
            source_binding(lib, native=changed if owner == 'native' else native,
                           debug=changed if owner == 'debug' else debug)
        except (ValueError, local.admission.storage.Unsupported) as error:
            records.append({'source': owner, 'mutation': before.decode(), 'rejection': str(error)})
        else:
            raise ValueError('accepted changed map lock: ' + before.decode())
    return records


def audit(rows):
    indexed = {row['theorem']: row for row in rows}
    dependencies = {
        INIT + 'load_frame_at': {'Compiler.ZigAir.Memory.load_disjoint_after_store', INIT + 'Slot.leaves'},
        INIT + 'read_frame_value': {INIT + 'load_frame_at'},
        LOCAL + 'read_other': {INIT + 'load_frame_at'},
        GRAPH + 'Facts.allocate_buckets_framed': {INIT + 'load_frame_at', GRAPH + 'Facts.reserve_header_framed', MAP + 'Receiver.publish_verified'},
        GRAPH + 'Facts.allocate_buckets': {GRAPH + 'Facts.allocate_buckets_framed'},
        GRAPH + 'Facts.prepare_buckets_framed': {GRAPH + 'Facts.declare_map', GRAPH + 'Facts.allocate_buckets_framed'},
        GRAPH + 'Facts.prepare_buckets': {GRAPH + 'Facts.prepare_buckets_framed'},
        LOCAL + 'lock_verified': {INIT + 'store_value_at_total', INIT + 'load_frame_at'},
        GRAPH + 'Facts.lock_buckets': {GRAPH + 'Facts.prepare_buckets_framed', LOCAL + 'lock_verified', GRAPH + 'Facts.local_map_frame'},
        GRAPH + 'lockBuckets_exhausted': {GRAPH + 'prepareBuckets_exhausted'},
        TESTS + 'from_initialized_owner': {GRAPH + 'Facts.lock_buckets', GRAPH + 'Tests.initialized_from_execution'},
        TESTS + 'oom_keeps_defaults': {GRAPH + 'MapLocalTests.oom_prefix', GRAPH + 'lockBuckets_oom'},
        TESTS + 'exhausted_keeps_input': {GRAPH + 'MapLocalTests.exhausted_keeps_input'},
    }
    for name, needed in dependencies.items():
        require(needed <= set(indexed[name]['dependencies']), 'map lock lost composition: ' + name)
        if not name.startswith(TESTS):
            require(not any(part.endswith('Tests') for dep in indexed[name]['dependencies'] for part in dep.split('.')),
                    'map lock core depends on a fixture')
    common = ['σ', 'safety', 'allocator', 'owner', 'capacity', 'data', 'before', 'rows', 'facts']
    preparation = common + ['room', 'bucketCapacity', 'positive', 'base', 'allocate', 'effects', 'response', 'fits', 'apart']
    expected = {
        INIT + 'load_frame_at': ['place', 'runtimeSafety', 'state', 'after', 'lifetime', 'value', 'written', 'queried',
                                'valueType', 'different', 'readWritable', 'stored'],
        GRAPH + 'Facts.allocate_buckets_framed': common + ['receiver', 'localCell', 'found', 'typed', 'writable',
            'bucketCapacity', 'positive', 'base', 'allocate', 'effects', 'response', 'fits'],
        GRAPH + 'Facts.prepare_buckets_framed': preparation,
        GRAPH + 'Facts.lock_buckets': preparation,
        LOCAL + 'lock_verified': ['safety', 'before', 'receiver', 'cell', 'valid', 'found', 'typed', 'writable', 'unlocked'],
        LOCAL + 'lock_rejected': ['before', 'receiver', 'value', 'read', 'held'],
        LOCAL + 'lock_without_safety': ['before', 'receiver'],
        GRAPH + 'lockBuckets_oom': ['σ', 'safety', 'capacity', 'allocate', 'before', 'prepared', 'oom'],
        GRAPH + 'lockBuckets_rejected': ['σ', 'safety', 'capacity', 'allocate', 'before', 'prepared', 'bucket', 'fault', 'ran', 'rejected'],
        GRAPH + 'lockBuckets_exhausted': ['σ', 'safety', 'before', 'capacity', 'allocate', 'valid', 'room'],
        TESTS + 'from_initialized_owner': ['safety', 'meaning'],
        TESTS + 'oom_keeps_defaults': ['safety', 'meaning'],
        TESTS + 'exhausted_keeps_input': ['safety'],
    }
    for name, binders in expected.items():
        value = indexed[name]['statement']; fields, _, root, scope = telescope(value)
        require(list(fields) == binders, 'map lock gained initialization/success/final-state premises: ' + name)
        if name == GRAPH + 'Facts.lock_buckets':
            witness = value['nodes'][app(value, root, 'Exists')[-1]]
            require(witness[:2] == ['lambda', 'after'], 'lock prefix lost actual resulting state')
            first, rest = app(value, witness[4], 'And')
            equation = app(value, first, 'Eq')
            require([expressions.named(value, a, scope + ['after']) for a in app(value, equation[-2], GRAPH + 'lockBuckets')] ==
                    ['σ', 'safety', 'bucketCapacity', 'allocate', 'before'], 'lock prefix changed original inputs')
            facts, _ = app(value, rest, 'And')
            require(expressions.named(value, app(value, facts, GRAPH + 'Facts')[-2], scope + ['after']) == 'after',
                    'lock prefix proves facts for another state')
        if name in (GRAPH + 'lockBuckets_rejected', GRAPH + 'lockBuckets_oom', GRAPH + 'lockBuckets_exhausted'):
            result = app(value, app(value, root, 'Eq')[-1], 'Prod.mk')
            require(expressions.named(value, result[-1], scope) == ('before' if name.endswith('exhausted') else 'prepared'),
                    'lock failure discarded the reached prefix')
    return {'checkedDependencies': sorted(dependencies), 'checkedStatements': sorted(expected),
            'localLockDerivedFromDeclaration': True, 'allocationFieldFrameShared': True,
            'capacityGuardsVerified': False, 'metadataClearingVerified': False, 'nativeHashMapVerified': False}


def controls(output, env, lean):
    directory = ROOT / 'lean/Compiler/Extraction'
    source = 'import Compiler.Extraction.ExpressionMapLocalAllocationTests\n'
    source += without_imports((directory / 'ExpressionMapLocalLock.lean').read_text())
    records = [mutation_check(output, 'map-lock-core-unchanged', source, True, env, lean),
               mutation_check(output, 'map-lock-fixtures-unchanged', source + '\n' +
                   without_imports((directory / 'ExpressionMapLocalLockTests.lean').read_text()), True, env, lean)]
    for name, before, after in (
        ('shared-count', 'def exclusive : Value := .scalar (.int false 64 18446744073709551615)', 'def exclusive : Value := .scalar (.int false 64 1)'),
        ('wrong-field', 'let current ← load before (field safety receiver .lock)', 'let current ← load before (field safety receiver .size)'),
        ('erase-guard', 'if current ≠ .scalar (.int false 64 0)', 'if False'),
        ('erase-store', 'else store before (field safety receiver .lock) exclusive', 'else .ok before'),
        ('ignore-mode', 'if !safety then return before', 'if False then return before'),
        ('wrong-receiver', 'match ExpressionMap.Local.lock safety before.memory.memory.nextId prepared.memory.memory with',
         'match ExpressionMap.Local.lock safety (before.memory.memory.nextId + 1) prepared.memory.memory with'),
        ('discard-lock', '| .ok memory => (.ok (some bucket), { prepared with memory := { prepared.memory with memory } })',
         '| .ok memory => (.ok (some bucket), prepared)'),
        ('discard-prefix', '| .error fault => (.error fault, prepared)', '| .error fault => (.error fault, before)'),
    ):
        require(source.count(before) == 1, 'ambiguous map lock mutation: ' + name)
        changed = source.replace(before, after, 1)
        # The max-word regression binds the numeric tag independently of the model definition.
        if name == 'shared-count':
            changed += '\n' + without_imports((directory / 'ExpressionMapLocalLockTests.lean').read_text())
        records.append(mutation_check(output, 'map-lock-' + name, changed, False, env, lean))
    return checked_controls(output, records)
