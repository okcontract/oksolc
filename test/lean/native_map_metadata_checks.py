"""Check actual packed metadata clearing composed with the native grow prefix.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as expressions
from constructor_joint_checks import app, path
from native_resource_admission_checks import telescope
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check
from check_zig_air_memory_proofs import without_imports
from check_word_swap import ROOT
from native_map_write_checks import GRAPH, require
from native_map_allocation_checks import MAP
from native_bucket_storage_checks import BUCKETS, HEADER
import native_map_lock_checks as locks
import generate_map_bucket_storage as admission

MODULE = 'Compiler.Extraction.ExpressionMapMetadataTests'
METADATA = BUCKETS + 'Metadata.'
TESTS = GRAPH + 'MapMetadataTests.'
CLAIMS = [BUCKETS + 'metadata_layout', MAP + 'Receiver.read_eq_of_lookup', GRAPH + 'Facts.private_map_frame']
CLAIMS += [METADATA + n for n in ('byte_views', 'store_total', 'read_other', 'header_frame', 'fill_verified',
    'zero_free_unused', 'Filled.free_unused', 'read_capacity', 'byte_array', 'prepare_verified', 'clear_verified')]
CLAIMS += [GRAPH + n for n in ('Facts.clear_buckets', 'clearBuckets_oom', 'clearBuckets_rejected', 'clearBuckets_exhausted')]
CLAIMS += [TESTS + n for n in ('from_initialized_owner', 'oom_keeps_defaults', 'exhausted_keeps_input',
    'initially_uninitialized', 'partial_rejection', 'readonly_rejected', 'wrong_extent_rejected')]


def source_binding(lib, native=None):
    native = (lib / 'std/hash_map.zig').read_bytes() if native is None else native
    binding = locks.source_binding(lib, native)
    function = admission.buckets.storage.function
    function(native, 'const Metadata =').expect(admission.METADATA_SOURCE)
    function(native, 'fn initMetadatas(self: *Self) void').expect('''{
        @memset(@as([*]u8, @ptrCast(self.metadata.?))[0 .. @sizeOf(Metadata) * self.capacity()], 0);
    }''')
    marker = b'fn header(self: Self) *Header'
    require(native.count(marker) == 1, 'missing or ambiguous unmanaged header')
    unmanaged = native[native.index(marker):]
    function(unmanaged, marker.decode()).expect('''{
        return @ptrCast(@as([*]Header, @ptrCast(@alignCast(self.metadata.?))) - 1);
    }''')
    function(unmanaged, 'pub fn capacity(self: Self) Size').expect('''{
        if (self.metadata == null) return 0;
        return self.header().capacity;
    }''')
    function(native, 'fn grow(self: *Self, allocator: Allocator, new_capacity: Size, ctx: Context) Allocator.Error!void').expect('''{
        @branchHint(.cold);
        const new_cap = @max(new_capacity, minimal_capacity);
        assert(new_cap > self.capacity());
        assert(std.math.isPowerOfTwo(new_cap));
        var map: Self = .{};
        try map.allocate(allocator, new_cap);
        errdefer comptime unreachable;
        map.pointer_stability.lock();
        map.initMetadatas();''')
    return {**binding, 'scope': 'grow after capacity guards through initMetadatas; actual nonnull capacity/header reads',
            'packedBacking': 'u8', 'clearedByte': 0, 'capacityGuardsVerified': False,
            'sourceAdapterFormallyVerified': False, 'nativeHashMapVerified': False}


def source_controls(lib):
    native = (lib / 'std/hash_map.zig').read_bytes(); records = []
    for before, after in (
        (b'map.initMetadatas();', b'self.initMetadatas();'),
        (b'@sizeOf(Metadata) * self.capacity()], 0);', b'@sizeOf(Metadata) * self.capacity()], 1);'),
        (b'@sizeOf(Metadata) * self.capacity()], 0);', b'@sizeOf(Metadata) * 8], 0);'),
        (b'@ptrCast(@alignCast(self.metadata.?))) - 1', b'@ptrCast(@alignCast(self.metadata.?))) - 2'),
        (b'return self.header().capacity;', b'return 8;'),
        (b'return self.used == 1;', b'return self.used == 0;'),
        (b'const free: FingerPrint = 0;', b'const free: FingerPrint = 1;'),
    ):
        require(native.count(before) == 1, 'ambiguous metadata source control')
        try: source_binding(lib, native.replace(before, after, 1))
        except (ValueError, admission.buckets.storage.Unsupported) as error:
            records.append({'mutation': before.decode(), 'rejection': str(error)})
        else: raise ValueError('accepted changed metadata initialization')
    return records


def audit(rows):
    indexed = {row['theorem']: row for row in rows}
    dependencies = {
        GRAPH + 'Facts.private_map_frame': {GRAPH + 'Facts.frame'},
        GRAPH + 'Facts.local_map_frame': {GRAPH + 'Facts.private_map_frame'},
        MAP + 'Receiver.read_eq_of_lookup': {'Compiler.ZigAir.Memory.load_eq_of_lookup', 'Compiler.ZigAir.Memory.fieldPointer_eq_of_lookup'},
        METADATA + 'store_total': {METADATA + 'store_byte_total'},
        METADATA + 'fill_verified': {METADATA + n for n in ('store_total', 'read_other', 'header_frame')},
        METADATA + 'read_capacity': {'Compiler.ZigAir.Memory.fieldPointer_of_access', BUCKETS + 'storage_layout'},
        METADATA + 'byte_array': {MAP + 'Receiver.metadata_view', 'Compiler.ZigAir.Memory.access_subregion'},
        METADATA + 'prepare_verified': {METADATA + 'read_capacity', METADATA + 'byte_array'},
        METADATA + 'clear_verified': {METADATA + 'prepare_verified', METADATA + 'fill_verified'},
        GRAPH + 'Facts.clear_buckets': {GRAPH + 'Facts.lock_buckets', GRAPH + 'Facts.private_map_frame',
            METADATA + 'clear_verified', METADATA + 'Filled.free_unused', MAP + 'Receiver.read_eq_of_lookup'},
        GRAPH + 'clearBuckets_exhausted': {GRAPH + 'lockBuckets_exhausted'},
        TESTS + 'from_initialized_owner': {GRAPH + 'Facts.clear_buckets', GRAPH + 'Tests.initialized_from_execution'},
        TESTS + 'oom_keeps_defaults': {GRAPH + 'MapLockTests.oom_keeps_defaults', GRAPH + 'clearBuckets_oom'},
        TESTS + 'exhausted_keeps_input': {GRAPH + 'MapLockTests.exhausted_keeps_input'},
    }
    for name, needed in dependencies.items():
        require(needed <= set(indexed[name]['dependencies']), 'metadata clearing lost composition: ' + name)
    for name in CLAIMS:
        if not name.startswith(TESTS):
            require(not any(part.endswith('Tests') for dep in indexed[name]['dependencies'] for part in dep.split('.')),
                    'metadata clearing core depends on a fixture')
    original = ['σ', 'safety', 'allocator', 'owner', 'capacity', 'data', 'before', 'rows', 'facts']
    valid = ['safety', 'receiver', 'before', 'id', 'cell', 'capacity', 'positive', 'valid', 'found', 'typed', 'writable', 'metadata', 'header']
    binders = {
        GRAPH + 'Facts.private_map_frame': original + ['kind', 'receiver', 'localCell', 'found', 'typed', 'memory', 'valid', 'shape', 'frame'],
        MAP + 'Receiver.read_eq_of_lookup': ['safety', 'before', 'after', 'receiver', 'same'],
        METADATA + 'fill_verified': ['id', 'index', 'count', 'capacity', 'before', 'cell', 'bounded', 'valid', 'found', 'typed', 'writable'],
        METADATA + 'prepare_verified': valid,
        METADATA + 'clear_verified': valid,
        GRAPH + 'Facts.clear_buckets': original + ['room', 'bucketCapacity', 'positive', 'base', 'allocate', 'effects', 'response', 'fits', 'apart'],
        GRAPH + 'clearBuckets_oom': ['σ', 'safety', 'capacity', 'allocate', 'before', 'locked', 'oom'],
        GRAPH + 'clearBuckets_rejected': ['σ', 'safety', 'capacity', 'allocate', 'before', 'locked', 'bucket', 'memory', 'fault', 'ran', 'rejected'],
        GRAPH + 'clearBuckets_exhausted': ['σ', 'safety', 'before', 'capacity', 'allocate', 'valid', 'room'],
    }
    for name in CLAIMS:
        if name.startswith(TESTS):
            binders[name] = (['safety', 'meaning'] if name.endswith(('from_initialized_owner', 'oom_keeps_defaults'))
                             else ['safety'] if name.endswith('exhausted_keeps_input') else [])
    for name, expected in binders.items():
        value = indexed[name]['statement']; fields, _, root, scope = telescope(value)
        require(list(fields) == expected, 'metadata clearing gained initialization/success/final-state premises: ' + name)
        if name in (METADATA + 'fill_verified', METADATA + 'clear_verified', GRAPH + 'Facts.clear_buckets'):
            witness = value['nodes'][app(value, root, 'Exists')[-1]]
            require(witness[:2] == ['lambda', 'after'], 'metadata clearing lost actual resulting state')
            first, rest = app(value, witness[4], 'And')
            operation, wanted = {
                METADATA + 'fill_verified': (METADATA + 'fill', ['id', 'count', 'index', 'before']),
                METADATA + 'clear_verified': (METADATA + 'clear', ['safety', 'receiver', 'before']),
                GRAPH + 'Facts.clear_buckets': (GRAPH + 'clearBuckets', ['σ', 'safety', 'bucketCapacity', 'allocate', 'before']),
            }[name]
            equation = app(value, first, 'Eq')
            require([expressions.named(value, a, scope + ['after']) for a in app(value, equation[-2], operation)] == wanted,
                    'metadata clearing changed original execution inputs')
            if name == GRAPH + 'Facts.clear_buckets':
                facts, _ = app(value, rest, 'And')
                require(expressions.named(value, app(value, facts, GRAPH + 'Facts')[-2], scope + ['after']) == 'after',
                        'metadata clearing proves facts for another state')
        if name == GRAPH + 'clearBuckets_oom' or name == GRAPH + 'clearBuckets_exhausted':
            result = app(value, app(value, root, 'Eq')[-1], 'Prod.mk')
            require(expressions.named(value, result[-1], scope) == ('locked' if name.endswith('oom') else 'before'),
                    'metadata failure discarded its reached prefix')
        if name == GRAPH + 'clearBuckets_rejected':
            result = app(value, app(value, root, 'Eq')[-1], 'Prod.mk')
            world = app(value, result[-1], 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.World.mk')
            path(value, world[-2], scope, ('Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.World.graph',), 'locked')
            session = value['nodes'][world[-1]]
            require(session[0] == 'let', 'metadata rejection lost the reached session')
            path(value, session[3], scope, ('Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.World.memory',), 'locked')
            local_scope = scope + [session[1]]
            fields = app(value, session[4], 'Compiler.Extraction.Memory.Arguments.Normalization.Session.mk')
            require(expressions.named(value, fields[-2], local_scope) == 'memory', 'metadata rejection erased partial byte stores')
            for field, selector in ((fields[-3], 'heap'), (fields[-1], 'effects')):
                path(value, field, local_scope, ('Compiler.Extraction.Memory.Arguments.Normalization.Session.' + selector,), session[1])
    return {'checkedDependencies': sorted(dependencies), 'checkedStatements': sorted(binders),
            'actualMetadataAndCapacityReadsDerived': True, 'packedByteClearingDerived': True,
            'privateStorageFrameShared': True, 'capacityGuardsVerified': False,
            'nativeHashMapVerified': False, 'sourceAdapterFormallyVerified': False}


def controls(output, env, lean):
    directory = ROOT / 'lean/Compiler/Extraction'
    source = 'import Compiler.Extraction.ExpressionMapLocalLockTests\n'
    for name in ('ExpressionMapMetadataFill.lean', 'ExpressionMapMetadata.lean', 'ExpressionMapMetadataInitialization.lean'):
        source += without_imports((directory / name).read_text()) + '\n'
    fixtures = without_imports((directory / 'ExpressionMapMetadataTests.lean').read_text())
    records = [mutation_check(output, 'map-metadata-core-unchanged', source, True, env, lean),
               mutation_check(output, 'map-metadata-fixtures-unchanged', source + '\n' + fixtures, True, env, lean)]
    for name, before, after, fixture in (
        ('nonzero-byte', 'def zero : Value := .scalar (.int false 8 0)', 'def zero : Value := .scalar (.int false 8 1)', False),
        ('byte-offset', '⟨id, 24 + index⟩\n', '⟨id, 25 + index⟩\n', False),
        ('skip-last-byte', '| .ok (id, count) => fill id count 0 before', '| .ok (id, count) => fill id (count - 1) 0 before', False),
        ('fabricated-capacity', '  load state field\n', '  .ok (.scalar (.int false 32 8))\n', False),
        ('used-bit', 'bits.toNat / 128 == 1', 'bits.toNat / 128 == 0', False),
        ('free-byte', 'bits == 0', 'bits == 1', False),
        ('discard-partial-fill', '| .error fault => (.error fault, before)', '| .error fault => (.error fault, { before with heap := [] })', True),
        ('wrong-receiver', 'Metadata.clear safety ⟨before.memory.memory.nextId, 0⟩ locked.memory.memory\n',
         'Metadata.clear safety ⟨before.memory.memory.nextId + 1, 0⟩ locked.memory.memory\n', False),
        ('discard-cleared-memory', '(cleared.map (fun _ => some bucket), { locked with memory := { locked.memory with memory } })',
         '(cleared.map (fun _ => some bucket), locked)', False),
        ('unchecked-extent', '  let .pointer _ selected ← Header.arrayPointer state metadataType capacity address | .error .unsupported\n',
         '  let selected := address\n', True),
    ):
        # The fill error branch also occurs in clear; select the first to retain
        # the independently checked preparation-failure behavior.
        require(source.count(before) == (2 if name == 'discard-partial-fill' else 1), 'ambiguous metadata control: ' + name)
        changed = source.replace(before, after, 1) + ('\n' + fixtures if fixture else '')
        records.append(mutation_check(output, 'map-metadata-' + name, changed, False, env, lean))
    return checked_controls(output, records)
