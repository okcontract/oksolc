"""Check local map declaration consumed by complete bucket allocation.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as expressions
from constructor_joint_checks import app
from native_resource_admission_checks import telescope
from native_checkpoint_constructor_checks import numeral
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check
from check_zig_air_memory_proofs import without_imports
from check_word_swap import ROOT
from native_map_write_checks import GRAPH, require
from native_map_allocation_checks import MAP, INIT
from native_bucket_reservation_checks import BUCKETS
import generate_map_bucket_layout as admission

MODULE = 'Compiler.Extraction.ExpressionMapLocalAllocationTests'
LOCAL = MAP + 'Local.'
TESTS = GRAPH + 'MapLocalTests.'
CLAIMS = [LOCAL + n for n in ('read_other', 'writes_verified', 'declare_verified', 'declare_region', 'declare_exhausted')]
CLAIMS += [GRAPH + n for n in ('Facts.declare_map', 'Facts.prepare_buckets', 'Facts.prepare_buckets_oom', 'prepareBuckets_exhausted')]
CLAIMS += [TESTS + n for n in ('room', 'declared_defaults', 'from_initialized_owner', 'captured_prefix', 'oom_prefix',
                              'exhausted_keeps_input', 'region_below_cursor')]


def source_binding(lib, native=None):
    native = (lib / 'std/hash_map.zig').read_bytes() if native is None else native
    # A scoped, reviewed source adapter, not a claim of verified Zig translation.
    # Keep the preceding guards visible; the theorem starts after them.
    admission.storage.function(native, 'fn grow(self: *Self, allocator: Allocator, new_capacity: Size, ctx: Context) Allocator.Error!void').expect('''{
        @branchHint(.cold);
        const new_cap = @max(new_capacity, minimal_capacity);
        assert(new_cap > self.capacity());
        assert(std.math.isPowerOfTwo(new_cap));
        var map: Self = .{};
        try map.allocate(allocator, new_cap);
        errdefer comptime unreachable;
        map.pointer_stability.lock();''')
    admission.storage.function(native, 'metadata: ?[*]Metadata =').expect('''null,
        size: Size = 0, available: Size = 0, pointer_stability: std.debug.SafetyLock = .{},''')
    return {**admission.source_binding(lib, native=native), 'scope': 'local declaration and allocation after grow guards',
            'capacityGuardsVerified': False, 'laterGrowStatementsVerified': False, 'sourceAdapterFormallyVerified': False}


def source_controls(lib):
    native = (lib / 'std/hash_map.zig').read_bytes()
    records = []
    for before, after in (
        (b'var map: Self = .{};', b'var map: Self = undefined;'),
        (b'try map.allocate(allocator, new_cap);', b'try self.allocate(allocator, new_cap);'),
        (b'size: Size = 0,', b'size: Size = 1,'),
        (b'available: Size = 0,', b'available: Size = 1,'),
    ):
        require(native.count(before) == 1, 'ambiguous map declaration source control')
        try:
            source_binding(lib, native.replace(before, after, 1))
        except (ValueError, admission.storage.Unsupported) as error:
            records.append({'mutation': before.decode(), 'rejection': str(error)})
        else:
            raise ValueError('accepted changed map declaration: ' + before.decode())
    return records


def audit(rows):
    indexed = {row['theorem']: row for row in rows}
    dependencies = {
        LOCAL + 'writes_verified': {INIT + 'store_value_at_total', LOCAL + 'read_other'},
        LOCAL + 'declare_verified': {LOCAL + 'writes_verified', 'Compiler.ZigAir.Memory.allocate_preserves_valid',
                                     'Compiler.ZigAir.Memory.allocate_retains_shape'},
        LOCAL + 'declare_region': {LOCAL + 'declare_verified'},
        GRAPH + 'Facts.declare_map': {LOCAL + 'declare_verified', GRAPH + 'Facts.frame',
                                    'Compiler.Extraction.Memory.Arguments.Normalization.Valid.private_memory_frame'},
        GRAPH + 'Facts.prepare_buckets': {GRAPH + 'Facts.prepare_buckets_framed', GRAPH + 'Facts.declare_map',
                                         GRAPH + 'Facts.allocate_buckets_framed', LOCAL + 'declare_region'},
        GRAPH + 'Facts.prepare_buckets_oom': {GRAPH + 'Facts.declare_map', GRAPH + 'allocateBuckets_oom'},
        GRAPH + 'prepareBuckets_exhausted': {LOCAL + 'declare_exhausted'},
        TESTS + 'declared_defaults': {LOCAL + 'declare_verified'},
        TESTS + 'from_initialized_owner': {GRAPH + 'Facts.prepare_buckets', GRAPH + 'Tests.initialized_from_execution'},
        TESTS + 'oom_prefix': {GRAPH + 'Facts.prepare_buckets_oom'},
        TESTS + 'exhausted_keeps_input': {GRAPH + 'prepareBuckets_exhausted'},
        TESTS + 'region_below_cursor': {LOCAL + 'declare_region'},
    }
    for name, needed in dependencies.items():
        require(needed <= set(indexed[name]['dependencies']), 'local declaration lost composition: ' + name)
        if not name.startswith(TESTS):
            require(not any(part.endswith('Tests') for dep in indexed[name]['dependencies'] for part in dep.split('.')),
                    'local declaration core depends on a fixture')
    common = ['σ', 'safety', 'allocator', 'owner', 'capacity', 'data', 'before', 'rows', 'facts', 'room']
    binders = {
        LOCAL + 'read_other': ['safety', 'id', 'before', 'after', 'written', 'queried', 'different', 'stored'],
        LOCAL + 'writes_verified': ['safety', 'id', 'selected', 'active', 'before', 'cell', 'valid', 'found', 'typed', 'writable'],
        LOCAL + 'declare_verified': ['safety', 'before', 'valid', 'room'],
        LOCAL + 'declare_region': ['safety', 'before', 'valid', 'room', 'layout', 'base', 'fits', 'apart'],
        LOCAL + 'declare_exhausted': ['safety', 'before', 'valid', 'room'],
        GRAPH + 'Facts.declare_map': common,
        GRAPH + 'Facts.prepare_buckets': common + ['bucketCapacity', 'positive', 'base', 'allocate', 'effects', 'response',
                                                   'fits', 'apart'],
        GRAPH + 'Facts.prepare_buckets_oom': common + ['bucketCapacity', 'positive', 'allocate', 'effects', 'response'],
        GRAPH + 'prepareBuckets_exhausted': ['σ', 'safety', 'before', 'capacity', 'allocate', 'valid', 'room'],
    }
    for name in CLAIMS:
        if name.startswith(TESTS):
            binders[name] = ['safety', 'meaning'] if name.endswith(('from_initialized_owner', 'oom_prefix')) else ['safety']
    for name, expected in binders.items():
        value = indexed[name]['statement']; fields, _, root, scope = telescope(value)
        require(list(fields) == expected, 'local declaration gained receiver/success/final-state premises: ' + name)
        if name == GRAPH + 'Facts.prepare_buckets':
            witness = value['nodes'][app(value, root, 'Exists')[-1]]
            require(witness[:2] == ['lambda', 'after'], 'prefix lost actual resulting state')
            equation = app(value, app(value, witness[4], 'And')[0], 'Eq')
            require([expressions.named(value, a, scope + ['after']) for a in app(value, equation[-2], GRAPH + 'prepareBuckets')] ==
                    ['σ', 'safety', 'bucketCapacity', 'allocate', 'before'], 'prefix changed original native inputs')
        if name == GRAPH + 'prepareBuckets_exhausted':
            result = app(value, app(value, root, 'Eq')[-1], 'Prod.mk')
            require(expressions.named(value, result[-1], scope) == 'before', 'stack exhaustion changed the original state')
        if 'response' in fields:
            response, context = fields['response']; call = app(value, response, 'Eq')[-2]
            head, args = expressions.applied(value, call)
            require(head[0] == 'bound' and context[-int(head[1])-1] == 'allocate' and len(args) == 3, 'wrong allocation host')
            request = app(value, app(value, args[0], 'BitVec.toNat')[-1], BUCKETS + 'sourceRequest')
            require(expressions.named(value, request[-1], context) == 'bucketCapacity', 'prefix lost native request arithmetic')
            numeral(value, args[1], 16)
    return {'checkedDependencies': sorted(dependencies), 'checkedStatements': sorted(binders),
            'localDeclarationDerived': True, 'bucketAllocationConsumesDerivedReceiver': True,
            'capacityGuardsVerified': False, 'metadataClearingVerified': False, 'nativeHashMapVerified': False}


def controls(output, env, lean):
    directory = ROOT / 'lean/Compiler/Extraction'
    source = 'import Compiler.Extraction.ExpressionMapAllocationTests\n'
    for name in ('ExpressionMapLocal.lean', 'ExpressionMapLocalAllocation.lean'):
        source += without_imports((directory / name).read_text()) + '\n'
    records = [mutation_check(output, 'map-local-core-unchanged', source, True, env, lean),
               mutation_check(output, 'map-local-fixtures-unchanged', source +
                   without_imports((directory / 'ExpressionMapLocalAllocationTests.lean').read_text()), True, env, lean)]
    for name, before, after in (
        ('missing-count', '[.metadata, .size, .available]', '[.metadata, .available]'),
        ('missing-lock', 'if safety then [.lock] else []', 'if safety then [] else []'),
        ('skip-store', '| .ok after => writes safety id rest after', '| .ok after => writes safety id rest state'),
        ('skip-allocation', 'writes safety before.nextId (slots safety) allocated', 'writes safety before.nextId (slots safety) before'),
        ('wrong-receiver', 'capacity receiver.allocation allocate declared', 'capacity (receiver.allocation + 1) allocate declared'),
        ('discard-declaration', 'capacity receiver.allocation allocate declared', 'capacity receiver.allocation allocate before'),
        ('erase-stack-rejection', '| .error fault => (.error fault, declared)', '| .error fault => (.ok none, declared)'),
        ('overlap-stack', 'base + layout.bytes ≤ stackBase before ∨ stackEnd safety before ≤ base', 'True'),
    ):
        require(source.count(before) == 1, 'ambiguous local declaration control: ' + name)
        records.append(mutation_check(output, 'map-local-' + name, source.replace(before, after, 1), False, env, lean))
    return checked_controls(output, records)
