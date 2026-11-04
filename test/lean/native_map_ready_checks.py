"""Check complete native map initialization before grow's rehash loop.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as expressions
from constructor_joint_checks import app, path
from native_resource_admission_checks import telescope
from native_checkpoint_constructor_checks import numeral
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check
from check_zig_air_memory_proofs import without_imports
from check_word_swap import ROOT
from native_map_write_checks import GRAPH, require
from native_map_allocation_checks import MAP, INIT
from native_map_local_checks import LOCAL
import native_map_metadata_checks as metadata

MODULE = 'Compiler.Extraction.ExpressionMapReadyTests'
AVAILABLE = LOCAL + 'Availability.'
TESTS = GRAPH + 'MapReadyTests.'
CLAIMS = [LOCAL + 'store_value_verified', MAP + 'empty_get']
CLAIMS += [AVAILABLE + n for n in ('word_exact', 'positive', 'initialize_verified')]
CLAIMS += [LOCAL + 'EmptyReady.' + n for n in ('count_read', 'lookup', 'insertion_room')]
CLAIMS += [GRAPH + n for n in ('Facts.ready_buckets', 'readyBuckets_oom', 'readyBuckets_rejected', 'readyBuckets_exhausted')]
CLAIMS += [TESTS + n for n in ('from_initialized_owner', 'oom_keeps_prefix', 'exhausted_keeps_input',
                              'source_word_boundaries', 'assigned_count_readback', 'readonly_rejected', 'missing_receiver_rejected')]


def source_binding(lib, native=None):
    native = (lib / 'std/hash_map.zig').read_bytes() if native is None else native
    binding = metadata.source_binding(lib, native)
    function = metadata.admission.buckets.storage.function
    function(native, 'pub const HashMapUnmanaged =').expect('''Custom; fn Custom(comptime K: type, comptime V: type,
        comptime Context: type, comptime max_load_percentage: u64,) type {''')
    function(native, 'fn grow(self: *Self, allocator: Allocator, new_capacity: Size, ctx: Context) Allocator.Error!void').expect('''{
        @branchHint(.cold);
        const new_cap = @max(new_capacity, minimal_capacity);
        assert(new_cap > self.capacity());
        assert(std.math.isPowerOfTwo(new_cap));
        var map: Self = .{};
        try map.allocate(allocator, new_cap);
        errdefer comptime unreachable;
        map.pointer_stability.lock();
        map.initMetadatas();
        map.available = @truncate((new_cap * max_load_percentage) / 100);''')
    function(native, 'fn getIndex(self: Self, key: anytype, ctx: anytype) ?usize').expect('''{
        if (self.size == 0) { @branchHint(.cold); return null; }
        const hash: Hash = ctx.hash(key);''')
    return {**binding, 'scope': 'grow after capacity guards through complete temporary-map initialization, before rehash',
            'arithmeticBits': 64, 'storedBits': 32, 'loadPercentage': 80,
            'capacityGuardsVerified': False, 'nonemptyProbingVerified': False, 'sourceAdapterFormallyVerified': False}


def source_controls(lib):
    native = (lib / 'std/hash_map.zig').read_bytes(); records = []
    assignment = b'map.available = @truncate((new_cap * max_load_percentage) / 100);'
    parameter = b'fn Custom(\n    comptime K: type,\n    comptime V: type,\n    comptime Context: type,\n    comptime max_load_percentage: u64,'
    guard = b'fn getIndex(self: Self, key: anytype, ctx: anytype) ?usize {\n            if (self.size == 0) {'
    for before, after in (
        (parameter, parameter.replace(b'u64', b'u32')),
        (assignment, assignment.replace(b'map.available', b'self.available')),
        (assignment, b'map.available = 0;'),
        (assignment, b'map.available = @truncate((new_cap / 100) * max_load_percentage);'),
        (assignment, assignment.replace(b'/ 100', b'/ 80')),
        (guard, guard.replace(b'self.size == 0', b'self.size == 1')),
    ):
        require(native.count(before) == 1, 'ambiguous pre-rehash source control')
        try: source_binding(lib, native.replace(before, after, 1))
        except (ValueError, metadata.admission.buckets.storage.Unsupported) as error:
            records.append({'mutation': before.decode(), 'rejection': str(error)})
        else: raise ValueError('accepted changed pre-rehash initialization')
    return records


def audit(rows):
    indexed = {row['theorem']: row for row in rows}
    dependencies = {
        LOCAL + 'store_value_verified': {INIT + 'store_value_at_total', INIT + 'load_frame_at'},
        LOCAL + 'writes_verified': {LOCAL + 'store_value_verified'},
        LOCAL + 'lock_verified': {LOCAL + 'store_value_verified'},
        AVAILABLE + 'initialize_verified': {LOCAL + 'store_value_verified', 'Compiler.ZigAir.Memory.root_fieldPointer'},
        AVAILABLE + 'positive': {AVAILABLE + 'word_exact'},
        LOCAL + 'EmptyReady.count_read': {'Compiler.ZigAir.Memory.root_fieldPointer'},
        LOCAL + 'EmptyReady.lookup': {LOCAL + 'EmptyReady.count_read', MAP + 'getEmptyFrom'},
        MAP + 'empty_get': {MAP + 'getEmptyFrom'},
        LOCAL + 'EmptyReady.insertion_room': {AVAILABLE + 'positive'},
        GRAPH + 'Facts.ready_buckets': {GRAPH + 'Facts.clear_buckets', AVAILABLE + 'initialize_verified', GRAPH + 'Facts.local_map_frame'},
        GRAPH + 'readyBuckets_exhausted': {GRAPH + 'clearBuckets_exhausted'},
        TESTS + 'from_initialized_owner': {GRAPH + 'Facts.ready_buckets', LOCAL + 'EmptyReady.lookup'},
        TESTS + 'oom_keeps_prefix': {GRAPH + 'MapMetadataTests.oom_keeps_defaults', GRAPH + 'readyBuckets_oom'},
    }
    for name, needed in dependencies.items():
        require(needed <= set(indexed[name]['dependencies']), 'map initialization lost composition: ' + name)
    for name in CLAIMS:
        if not name.startswith(TESTS):
            require(not any(part.endswith('Tests') for dep in indexed[name]['dependencies'] for part in dep.split('.')),
                    'map initialization core depends on a fixture')
    common = ['σ', 'safety', 'allocator', 'owner', 'capacity', 'data', 'before', 'rows', 'facts']
    ready = ['safety', 'receiver', 'bucket', 'capacity', 'base', 'state', 'ready']
    binders = {
        LOCAL + 'store_value_verified': ['safety', 'before', 'id', 'cell', 'slot', 'value', 'valueType', 'valueValid', 'active', 'valid', 'found', 'typed', 'writable'],
        MAP + 'empty_get': ['α', 'runtimeSafety', 'state', 'owner', 'key', 'loaded'],
        AVAILABLE + 'word_exact': ['capacity'],
        AVAILABLE + 'positive': ['capacity', 'minimum'],
        AVAILABLE + 'initialize_verified': ['safety', 'receiver', 'capacity', 'before', 'cell', 'valid', 'found', 'typed', 'writable'],
        LOCAL + 'EmptyReady.count_read': ready,
        LOCAL + 'EmptyReady.lookup': ready + ['key'],
        LOCAL + 'EmptyReady.insertion_room': ready + ['minimum', 'index', 'inside'],
        GRAPH + 'Facts.ready_buckets': common + ['room', 'bucketCapacity', 'positive', 'base', 'allocate', 'effects', 'response', 'fits', 'apart'],
        GRAPH + 'readyBuckets_oom': ['σ', 'safety', 'capacity', 'allocate', 'before', 'cleared', 'oom'],
        GRAPH + 'readyBuckets_rejected': ['σ', 'safety', 'capacity', 'allocate', 'before', 'cleared', 'bucket', 'fault', 'ran', 'rejected'],
        GRAPH + 'readyBuckets_exhausted': ['σ', 'safety', 'before', 'capacity', 'allocate', 'valid', 'room'],
    }
    for name in CLAIMS:
        if name.startswith(TESTS):
            binders[name] = (['safety', 'meaning'] if name.endswith(('from_initialized_owner', 'oom_keeps_prefix'))
                             else [] if name.endswith('source_word_boundaries') else ['safety'])
    for name, expected in binders.items():
        value = indexed[name]['statement']; fields, _, root, scope = telescope(value)
        require(list(fields) == expected, 'map initialization gained state/outcome/arithmetic premises: ' + name)
        if name == GRAPH + 'Facts.ready_buckets':
            witness = value['nodes'][app(value, root, 'Exists')[-1]]
            require(witness[:2] == ['lambda', 'after'], 'initialization lost actual resulting state')
            equation, rest = app(value, witness[4], 'And')
            require([expressions.named(value, a, scope + ['after']) for a in app(value, app(value, equation, 'Eq')[-2], GRAPH + 'readyBuckets')] ==
                    ['σ', 'safety', 'bucketCapacity', 'allocate', 'before'], 'initialization changed original execution inputs')
            facts, rest = app(value, rest, 'And')
            require(expressions.named(value, app(value, facts, GRAPH + 'Facts')[-2], scope + ['after']) == 'after',
                    'initialization proves facts for another state')
            _, rest = app(value, rest, 'And'); _, rest = app(value, rest, 'And')
            representation = app(value, rest, LOCAL + 'EmptyReady')
            require(expressions.named(value, representation[0], scope + ['after']) == 'safety' and
                    expressions.named(value, representation[3], scope + ['after']) == 'bucketCapacity' and
                    expressions.named(value, representation[4], scope + ['after']) == 'base', 'preparation changed capacity/region')
            cursor_path = ('Compiler.ZigAir.Memory.State.nextId',
                           'Compiler.Extraction.Memory.Arguments.Normalization.Session.memory',
                           'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.World.memory')
            path(value, representation[1], scope + ['after'], cursor_path, 'before')
            bucket = app(value, representation[2], 'HAdd.hAdd')
            require(len(bucket) == 6 and all(expressions.named(value, a, scope + ['after']) == 'Nat' for a in bucket[:3]),
                    'preparation changed the bucket identity arithmetic')
            path(value, bucket[-2], scope + ['after'], cursor_path, 'before')
            numeral(value, bucket[-1], 1)
            path(value, representation[-1], scope + ['after'],
                 ('Compiler.Extraction.Memory.Arguments.Normalization.Session.memory',
                  'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.World.memory'), 'after')
        if name == LOCAL + 'EmptyReady.lookup':
            equation = app(value, root, 'Eq')
            require([expressions.named(value, a, scope) for a in app(value, equation[-2], LOCAL + 'getEmpty')] ==
                    ['safety', 'state', 'receiver', 'key'], 'empty lookup changed the native inputs')
            projection = app(value, app(value, equation[-1], 'Except.ok')[-1], 'Compiler.Extraction.OwnedKeys.view')
            require(expressions.named(value, projection[-1], scope) == 'key', 'empty lookup rebound its logical key')
            table = value['nodes'][projection[-2]]
            require(table[0] == 'lambda', 'empty lookup no longer projects the empty table')
            app(value, table[4], 'Option.none')
        if name in (GRAPH + 'readyBuckets_oom', GRAPH + 'readyBuckets_rejected', GRAPH + 'readyBuckets_exhausted'):
            result = app(value, app(value, root, 'Eq')[-1], 'Prod.mk')
            require(expressions.named(value, result[-1], scope) == ('before' if name.endswith('exhausted') else 'cleared'),
                    'map initialization discarded its reached failure prefix')
    return {'checkedDependencies': sorted(dependencies), 'checkedStatements': sorted(binders),
            'localStoreProofShared': True, 'availableArithmeticDerived': True, 'emptyLookupUsesExistingTable': True,
            'completePreRehashInitializationDerived': True, 'capacityGuardsVerified': False, 'nativeHashMapVerified': False}


def controls(output, env, lean):
    directory = ROOT / 'lean/Compiler/Extraction'
    source = 'import Compiler.Extraction.ExpressionMapMetadataTests\n'
    for name in ('ExpressionMapAvailability.lean', 'ExpressionMapReady.lean'):
        source += without_imports((directory / name).read_text()) + '\n'
    fixture = without_imports((directory / 'ExpressionMapReadyTests.lean').read_text())
    records = [mutation_check(output, 'map-ready-core-unchanged', source, True, env, lean),
               mutation_check(output, 'map-ready-fixtures-unchanged', source + fixture, True, env, lean)]
    for name, before, after in (
        ('narrow-product', '((capacity.setWidth 64 * (80 : BitVec 64)) / 100).setWidth 32', '((capacity * 80).setWidth 64 / 100).setWidth 32'),
        ('divide-first', '((capacity.setWidth 64 * (80 : BitVec 64)) / 100).setWidth 32', '((capacity.setWidth 64 / 100) * 80).setWidth 32'),
        ('wrong-percentage', '((capacity.setWidth 64 * (80 : BitVec 64)) / 100).setWidth 32', '((capacity.setWidth 64 * (100 : BitVec 64)) / 100).setWidth 32'),
        ('wrong-field', 'def slot : Slot := .available', 'def slot : Slot := .size'),
        ('countdown-lookup', 'def countSlot : Slot := .size', 'def countSlot : Slot := .available'),
        ('wrong-receiver', 'ExpressionMap.Local.Availability.assign safety before.memory.memory.nextId capacity cleared.memory.memory with',
         'ExpressionMap.Local.Availability.assign safety (before.memory.memory.nextId + 1) capacity cleared.memory.memory with'),
        ('discard-assignment', '| .ok memory => (.ok (some bucket), { cleared with memory := { cleared.memory with memory } })',
         '| .ok memory => (.ok (some bucket), cleared)'),
        ('discard-failure-prefix', '| .error fault => (.error fault, cleared)', '| .error fault => (.error fault, before)'),
    ):
        require(source.count(before) == 1, 'ambiguous initialization control: ' + name)
        records.append(mutation_check(output, 'map-ready-' + name, source.replace(before, after, 1), False, env, lean))
    # Bind the skipped store to its direct readback outcome as well as the
    # composed discarded-memory control above. Keeping this operational check
    # separate avoids normalizing a huge false store equation in the proof.
    operation = 'import Compiler.Extraction.ExpressionMapMetadataTests\n'
    operation += without_imports((directory / 'ExpressionMapAvailability.lean').read_text()).split('theorem initialize_verified', 1)[0]
    operation += 'end Compiler.Extraction.ExpressionMap.Local.Availability\n'
    readback = fixture.split('theorem assigned_count_readback', 1)[1].split('/-- Selector and write faults', 1)[0]
    # Give the pretty-printer enough depth to report the computed false
    # proposition; the same bound applies to the unchanged operational check.
    operation += 'namespace ' + TESTS[:-1] + '\nset_option maxRecDepth 4096 in\ntheorem assigned_count_readback' + readback + '\nend ' + TESTS[:-1] + '\n'
    records.append(mutation_check(output, 'map-ready-write-outcome-unchanged', operation, True, env, lean))
    before = '  store before selected (value capacity)'
    require(operation.count(before) == 1, 'ambiguous skipped assignment')
    records.append(mutation_check(output, 'map-ready-skip-assignment', operation.replace(before, '  .ok before', 1), False, env, lean))
    return checked_controls(output, records)
