"""Check native capacity selection consumed by temporary-map preparation.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import json
import resource
import signal
import subprocess
import time
import check_native_invocation as expressions
from constructor_joint_checks import app, path
from native_resource_admission_checks import telescope
from native_checkpoint_constructor_checks import numeral
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check
from check_zig_air_memory_proofs import without_imports
from check_word_swap import ROOT
from build_toolchain import digest, run, write_json
from native_map_write_checks import GRAPH, require
from native_map_allocation_checks import MAP
import native_map_ready_checks as ready
import generate_map_bucket_layout as buckets

MODULE = 'Compiler.Extraction.ExpressionMapCapacityTests'
CAPACITY = MAP + 'Capacity.'
ESTABLISHED = GRAPH.removesuffix('NativeGraph.') + 'GraphInit.Ownership.Established.'
TESTS = GRAPH + 'MapCapacityTests.'
CLAIMS = [CAPACITY + n for n in ('expanded_exact', 'promoted_exact', 'exponent_bound', 'ceil_verified',
    'for_size_verified', 'ceil_rejected', 'for_size_rejected', 'power_guard', 'grow_word', 'select_room',
    'select_growth', 'select_memory_room', 'Observed.select_growth', 'observed_empty', 'local_read', 'ready_observed')]
CLAIMS += [ESTABLISHED + 'capacity_observed']
CLAIMS += [GRAPH + n for n in ('Facts.prepare_growth', 'prepareGrowth_prefix', 'prepareGrowth_enough', 'prepareGrowth_rejected')]
CLAIMS += [TESTS + n for n in ('observed_from_initialization', 'from_initialized_owner', 'no_growth_retains_input',
    'oom_keeps_prefix', 'allocated_capacity_reads', 'native_word_boundaries', 'invalid_countdown_and_sum', 'selection_boundaries', 'missing_receiver_rejected')]
COUNTS = {0: 0, 1: 8, 6: 8, 7: 16, 13: 32, 1717986918: 2147483648}


def source_binding(lib, native=None, math=None):
    native = (lib / 'std/hash_map.zig').read_bytes() if native is None else native
    math = (lib / 'std/math.zig').read_bytes() if math is None else math
    binding = ready.source_binding(lib, native)
    function = buckets.storage.function
    function(native, 'fn capacityForSize(size: Size) Size').expect('''{
        var new_cap: u32 = @intCast((@as(u64, size) * 100) / max_load_percentage + 1);
        new_cap = math.ceilPowerOfTwo(u32, new_cap) catch unreachable; return new_cap; }''')
    function(native, 'fn load(self: Self) Size').expect('''{
        const max_load = (self.capacity() * max_load_percentage) / 100;
        assert(max_load >= self.available); return @as(Size, @truncate(max_load - self.available)); }''')
    function(native, 'fn growIfNeeded(self: *Self, allocator: Allocator, new_count: Size, ctx: Context) Allocator.Error!void').expect('''{
        if (new_count > self.available) { try self.grow(allocator, capacityForSize(self.load() + new_count), ctx); } }''')
    function(native, 'fn values(self: Self) [*]V').expect('''{ return self.header().values; }
        pub fn capacity(self: Self) Size {
        if (self.metadata == null) return 0; return self.header().capacity; }''')
    function(math, 'pub fn ceilPowerOfTwoPromote(comptime T: type, value: T)').expect('''
        @Int(@typeInfo(T).int.signedness, @typeInfo(T).int.bits + 1) {
        comptime assert(@typeInfo(T) == .int); comptime assert(@typeInfo(T).int.signedness == .unsigned);
        assert(value != 0); const PromotedType = @Int(@typeInfo(T).int.signedness, @typeInfo(T).int.bits + 1);
        const ShiftType = std.math.Log2Int(PromotedType);
        return @as(PromotedType, 1) << @as(ShiftType, @intCast(@typeInfo(T).int.bits - @clz(value - 1))); }''')
    function(math, 'pub fn ceilPowerOfTwo(comptime T: type, value: T)').expect('''(error{Overflow}!T) {
        comptime assert(@typeInfo(T) == .int); const info = @typeInfo(T).int; comptime assert(info.signedness == .unsigned);
        const PromotedType = @Int(info.signedness, info.bits + 1); const overflowBit = @as(PromotedType, 1) << info.bits;
        const x = ceilPowerOfTwoPromote(T, value); if (overflowBit & x != 0) { return error.Overflow; }
        return @as(T, @intCast(x)); }''')
    function(math, 'pub fn isPowerOfTwo(int: anytype) bool').expect('''{ assert(int > 0); return (int & (int - 1)) == 0; }''')
    return {**binding, 'scope': 'growIfNeeded capacity reads/selection and temporary-map initialization, before rehash',
            'ordinaryMaximumSize': 1717986918, 'capacityGuardsVerified': True,
            'nativeHashMapVerified': False, 'sourceAdapterFormallyVerified': False}


def source_controls(lib):
    originals = {'native': (lib / 'std/hash_map.zig').read_bytes(), 'math': (lib / 'std/math.zig').read_bytes()}
    records = []
    for field, before, after in (
        ('native', b'(@as(u64, size) * 100)', b'(@as(u32, size) * 100)'),
        ('native', b'/ max_load_percentage + 1)', b'/ max_load_percentage)'),
        ('native', b'math.ceilPowerOfTwo(u32, new_cap)', b'math.floorPowerOfTwo(u32, new_cap)'),
        ('native', b'if (new_count > self.available)', b'if (new_count >= self.available)'),
        ('native', b'@truncate(max_load - self.available)', b'@truncate(max_load + self.available)'),
        ('native', b'if (self.metadata == null) return 0;', b'if (self.metadata == null) return 1;'),
        ('math', b'@clz(value - 1)', b'@clz(value)'),
        ('math', b'const PromotedType = @Int(info.signedness, info.bits + 1);', b'const PromotedType = @Int(info.signedness, info.bits);'),
        ('math', b'if (overflowBit & x != 0)', b'if (overflowBit & x == 0)'),
        ('math', b'return (int & (int - 1)) == 0;', b'return (int & (int - 1)) != 0;'),
    ):
        require(originals[field].count(before) == 1, 'ambiguous capacity source control')
        changed = {**originals, field: originals[field].replace(before, after, 1)}
        try: source_binding(lib, **changed)
        except (ValueError, buckets.storage.Unsupported) as error:
            records.append({'source': field, 'mutation': before.decode(), 'rejection': str(error)})
        else: raise ValueError('accepted changed capacity computation')
    return records


def audit(rows):
    indexed = {row['theorem']: row for row in rows}
    dependencies = {
        CAPACITY + 'exponent_bound': {'BitVec.clz_eq_zero_iff', 'BitVec.toNat_lt_two_pow_sub_clz'},
        CAPACITY + 'for_size_verified': {CAPACITY + 'expanded_exact', CAPACITY + 'ceil_verified'},
        CAPACITY + 'for_size_rejected': {CAPACITY + 'expanded_exact', CAPACITY + 'ceil_rejected'},
        CAPACITY + 'select_growth': {CAPACITY + 'for_size_verified', CAPACITY + 'grow_word', CAPACITY + 'power_guard', ready.AVAILABLE + 'word_exact'},
        CAPACITY + 'Observed.select_growth': {CAPACITY + 'select_growth'},
        CAPACITY + 'ready_observed': {CAPACITY + 'local_read', MAP + 'Buckets.Metadata.read_capacity'},
        ESTABLISHED + 'capacity_observed': {CAPACITY + 'observed_empty'},
        GRAPH + 'Facts.prepare_growth': {GRAPH + 'Facts.ready_buckets', GRAPH + 'prepareGrowth_prefix', CAPACITY + 'Observed.select_growth'},
        GRAPH + 'prepareGrowth_enough': {CAPACITY + 'select_memory_room'},
        TESTS + 'observed_from_initialization': {ESTABLISHED + 'capacity_observed', GRAPH.removesuffix('NativeGraph.') + 'GraphInit.Ownership.Tests.initial_ownership_from_execution'},
        TESTS + 'from_initialized_owner': {GRAPH + 'Facts.prepare_growth', TESTS + 'observed_from_initialization'},
        TESTS + 'oom_keeps_prefix': {ready.TESTS + 'oom_keeps_prefix', GRAPH + 'prepareGrowth_prefix', CAPACITY + 'Observed.select_growth'},
        TESTS + 'allocated_capacity_reads': {CAPACITY + 'ready_observed', CAPACITY + 'Observed.select_growth'},
    }
    for name, needed in dependencies.items():
        require(needed <= set(indexed[name]['dependencies']), 'capacity proof lost composition: ' + name)
    for name in CLAIMS:
        if not name.startswith(TESTS):
            require(not any(part.endswith('Tests') for dep in indexed[name]['dependencies'] for part in dep.split('.')),
                    'capacity core depends on a fixture')
    common = ['σ', 'safety', 'allocator', 'owner', 'capacity', 'data', 'before', 'rows', 'facts']
    binders = {
        CAPACITY + 'expanded_exact': ['size'], CAPACITY + 'promoted_exact': ['value'],
        CAPACITY + 'exponent_bound': ['value', 'positive', 'bounded'],
        CAPACITY + 'ceil_verified': ['safety', 'value', 'positive', 'bounded'],
        CAPACITY + 'for_size_verified': ['safety', 'size', 'bounded'],
        CAPACITY + 'ceil_rejected': ['safety', 'value', 'large'], CAPACITY + 'for_size_rejected': ['safety', 'size', 'large'],
        CAPACITY + 'power_guard': ['capacity', 'power'], CAPACITY + 'grow_word': ['capacity'],
        CAPACITY + 'select_room': ['safety', 'capacity', 'available', 'additional', 'room'],
        CAPACITY + 'select_growth': ['safety', 'capacity', 'available', 'additional', 'countdown', 'needed', 'bounded'],
        CAPACITY + 'select_memory_room': ['place', 'safety', 'state', 'receiver', 'available', 'additional', 'read', 'room'],
        CAPACITY + 'Observed.select_growth': ['place', 'safety', 'state', 'receiver', 'capacity', 'available', 'observed', 'additional', 'countdown', 'needed', 'bounded'],
        CAPACITY + 'observed_empty': ['safety', 'state', 'receiver', 'observed'],
        CAPACITY + 'local_read': ['safety', 'state', 'receiver', 'slot', 'cell', 'valid', 'found', 'typed', 'ordinary'],
        CAPACITY + 'ready_observed': ['safety', 'receiver', 'bucket', 'capacity', 'base', 'state', 'ready', 'positive'],
        ESTABLISHED + 'capacity_observed': ['σ', 'safety', 'allocator', 'before', 'after', 'owner', 'sentinel', 'meaning', 'established'],
        GRAPH + 'Facts.prepare_growth': common + ['place', 'receiver', 'oldCapacity', 'available', 'additional', 'observed', 'countdown',
            'needed', 'bounded', 'room', 'base', 'allocate', 'effects', 'response', 'fits', 'apart'],
        GRAPH + 'prepareGrowth_enough': ['σ', 'place', 'safety', 'receiver', 'available', 'additional', 'allocate', 'before', 'read', 'room'],
        GRAPH + 'prepareGrowth_prefix': ['σ', 'place', 'safety', 'receiver', 'additional', 'allocate', 'before', 'selected', 'result', 'after', 'selection', 'ran'],
        GRAPH + 'prepareGrowth_rejected': ['σ', 'place', 'safety', 'receiver', 'additional', 'allocate', 'before', 'fault', 'rejected'],
    }
    for name in CLAIMS:
        if name.startswith(TESTS): binders[name] = ['safety'] if name.endswith(('native_word_boundaries', 'invalid_countdown_and_sum', 'selection_boundaries', 'missing_receiver_rejected')) else ['safety', 'meaning']
    for name, wanted in binders.items():
        value = indexed[name]['statement']; fields, _, root, scope = telescope(value)
        require(list(fields) == wanted, 'capacity proof gained outcome/guard premises: ' + name)
        if name == GRAPH + 'Facts.prepare_growth':
            witness = value['nodes'][app(value, root, 'Exists')[-1]]
            require(witness[:2] == ['lambda', 'after'], 'capacity preparation lost actual post-state')
            equation, rest = app(value, witness[4], 'And')
            require([expressions.named(value, a, scope + ['after']) for a in app(value, app(value, equation, 'Eq')[-2], GRAPH + 'prepareGrowth')] ==
                    ['σ', 'place', 'safety', 'receiver', 'additional', 'allocate', 'before'], 'capacity preparation changed execution inputs')
            facts, rest = app(value, rest, 'And')
            require(expressions.named(value, app(value, facts, GRAPH + 'Facts')[-2], scope + ['after']) == 'after', 'capacity preparation uses another graph')
            representation, _ = app(value, rest, 'And'); representation = app(value, representation, ready.LOCAL + 'EmptyReady')
            require([expressions.named(value, a, scope + ['after']) for a in app(value, representation[3], CAPACITY + 'target')] ==
                    ['oldCapacity', 'available', 'additional'], 'capacity preparation replaced the computed size')
            require(expressions.named(value, representation[0], scope + ['after']) == 'safety' and
                    expressions.named(value, representation[4], scope + ['after']) == 'base', 'capacity preparation changed its region')
            cursor_path = ('Compiler.ZigAir.Memory.State.nextId',
                           'Compiler.Extraction.Memory.Arguments.Normalization.Session.memory',
                           'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.World.memory')
            path(value, representation[1], scope + ['after'], cursor_path, 'before')
            bucket = app(value, representation[2], 'HAdd.hAdd')
            path(value, bucket[-2], scope + ['after'], cursor_path, 'before')
            numeral(value, bucket[-1], 1)
            path(value, representation[-1], scope + ['after'],
                 ('Compiler.Extraction.Memory.Arguments.Normalization.Session.memory',
                  'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.World.memory'), 'after')
            result = app(value, app(value, equation, 'Eq')[-1], 'Prod.mk')
            require(expressions.named(value, result[-1], scope + ['after']) == 'after', 'capacity execution returned another state')
            prepared = app(value, app(value, result[-2], 'Except.ok')[-1], GRAPH + 'GrowthPreparation.prepared')
            require(expressions.named(value, prepared[0], scope + ['after']) ==
                    expressions.named(value, representation[3], scope + ['after']), 'capacity execution returned another size')
            address = app(value, prepared[1], 'Compiler.ZigAir.Memory.Address.mk')
            require(expressions.named(value, address[0], scope + ['after']) ==
                    expressions.named(value, representation[2], scope + ['after']), 'capacity execution returned another bucket')
            numeral(value, address[1], 0)
            observed, context = fields['observed']
            observed = app(value, observed, CAPACITY + 'Observed')
            require([expressions.named(value, observed[i], context) for i in (0, 1, 3, 4, 5)] ==
                    ['place', 'safety', 'receiver', 'oldCapacity', 'available'], 'capacity preparation rebound its input reads')
            path(value, observed[2], context,
                 ('Compiler.Extraction.Memory.Arguments.Normalization.Session.memory',
                  'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.World.memory'), 'before')
        if name in (GRAPH + 'prepareGrowth_enough', GRAPH + 'prepareGrowth_rejected'):
            result = app(value, app(value, root, 'Eq')[-1], 'Prod.mk')
            require(expressions.named(value, result[-1], scope) == 'before', 'capacity preflight changed the original state')
        if name == GRAPH + 'prepareGrowth_prefix':
            result = app(value, app(value, root, 'Eq')[-1], 'Prod.mk')
            require(expressions.named(value, result[-1], scope) == 'after', 'capacity outcome discarded its reached prefix')
            mapped = app(value, result[-2], 'Except.map')
            require(expressions.named(value, mapped[-1], scope) == 'result' and
                    [expressions.named(value, a, scope) for a in app(value, mapped[-2], GRAPH + 'GrowthPreparation.ofBucket')] ==
                    ['selected'], 'capacity prefix changed its actual outcome')
            ran, context = fields['ran']; ran = app(value, ran, 'Eq')
            require([expressions.named(value, a, context) for a in app(value, ran[-2], GRAPH + 'readyBuckets')] ==
                    ['σ', 'safety', 'selected', 'allocate', 'before'], 'capacity prefix changed its native preparation')
            require([expressions.named(value, a, context) for a in app(value, ran[-1], 'Prod.mk')[-2:]] ==
                    ['result', 'after'], 'capacity prefix rebound its reached outcome')
    return {'checkedDependencies': sorted(dependencies), 'checkedStatements': sorted(binders),
            'capacitySelectionAndGuardsDerived': True, 'actualFieldReadsConsumed': True,
            'preparedCapacityPremiseRemoved': True, 'countdownAndWordDomainRemainExplicit': True, 'nativeHashMapVerified': False}


def controls(output, env, lean):
    directory = ROOT / 'lean/Compiler/Extraction'
    source = 'import Compiler.Extraction.ExpressionMapReadyTests\n'
    for name in ('ExpressionMapCapacity.lean', 'ExpressionMapCapacityMemory.lean', 'ExpressionMapCapacityTests.lean'):
        source += without_imports((directory / name).read_text()) + '\n'
    records = [mutation_check(output, 'map-capacity-unchanged', source, True, env, lean)]
    for name, before, after in (
        ('wrong-expansion', '(size.setWidth 64 * 100) / 80 + 1', '(size.setWidth 64 * 100) / 100 + 1'),
        ('missing-increment', '(size.setWidth 64 * 100) / 80 + 1', '(size.setWidth 64 * 100) / 80'),
        ('wrong-rounding', '32 - (value - 1).clz.toNat\ndef promoted', '32 - value.clz.toNat\ndef promoted'),
        ('overflow-bit', 'if BitVec.twoPow 33 32 &&& rounded ≠ 0 then', 'if BitVec.twoPow 33 32 &&& rounded = 0 then'),
        ('no-minimum', 'if capacity.toNat < 8 then 8 else capacity', 'if capacity.toNat < 8 then 1 else capacity'),
        ('countdown-equality', 'if maximum.toNat < available.toNat then', 'if maximum.toNat ≤ available.toNat then'),
        ('wrong-available-field', '← readField place safety state receiver .available |', '← readField place safety state receiver .size |'),
        ('nonnull-default', '| none => .ok 0\n', '| none => .error .unsupported\n'),
        ('wrong-receiver', 'Capacity.selectMemory place safety before.memory.memory receiver additional with',
         'Capacity.selectMemory place safety before.memory.memory (receiver + 1) additional with'),
        ('enough-is-oom', '| .ok none => (.ok .enough, before)', '| .ok none => (.ok .outOfMemory, before)'),
        ('discard-prefix', '(result.map (GrowthPreparation.ofBucket capacity), after)', '(result.map (GrowthPreparation.ofBucket capacity), before)'),
    ):
        require(source.count(before) == 1, 'ambiguous capacity control: ' + name)
        records.append(mutation_check(output, 'map-capacity-' + name, source.replace(before, after, 1), False, env, lean))
    return checked_controls(output, records)


def check_request(record, count):
    buckets.fields(record, ('schema', 'requested_count', 'outcome', 'request', 'capacity', 'available', 'count',
        'metadata_null', 'unlocked', 'attempts', 'allocations', 'frees', 'resizes', 'remaps'), 'capacity request')
    require(count in COUNTS and record['schema'] == 'oksolc.expression-map-capacity.v1', 'wrong capacity request schema/scope')
    integers = ('requested_count', 'capacity', 'available', 'count', 'attempts', 'allocations', 'frees', 'resizes', 'remaps')
    require(all(buckets.natural(record[k]) for k in integers) and record['requested_count'] == count, 'wrong capacity request/count')
    buckets.fields(record['request'], ('base', 'bytes', 'alignment'), 'capacity allocation')
    require(all(buckets.natural(v) for v in record['request'].values()), 'invalid capacity allocation integers')
    capacity = COUNTS[count]
    expected = {'base': 0, 'bytes': buckets.geometry(capacity)[2] if count else 0, 'alignment': 16 if count else 0}
    require(record['request'] == expected and record['outcome'] == ('OutOfMemory' if count else None), 'wrong computed capacity or outcome')
    require((record['capacity'], record['available'], record['count']) == (0, 0, 0) and record['metadata_null'] is True and
            record['unlocked'] is True, 'rejected capacity request changed the original map')
    require((record['attempts'], record['allocations'], record['frees'], record['resizes'], record['remaps']) ==
            (int(count != 0), 0, 0, 0, 0), 'unexpected capacity allocator effects')
    return {'count': count, 'capacityFromRequest': capacity, 'request': expected, 'outcome': record['outcome']}


def no_core():
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def capture(output, env):
    records, corruptions, rejected = [], [], []
    for mode in ('Debug', 'ReleaseSafe', 'ReleaseFast'):
        binary = output / ('buckets-' + mode)
        for count in COUNTS:
            name = 'capacity-' + mode + '-' + str(count)
            run(output, name, [binary, str(count)], cwd=ROOT, env=env)
            raw = (output / (name + '.stdout')).read_bytes()
            require(len(raw) <= 4096 and not (output / (name + '.stderr')).read_bytes(), 'unbounded or noisy capacity observation')
            profile = json.loads(raw)
            records.append({'mode': mode, 'binarySha256': digest(binary), 'observationSha256': digest(output / (name + '.stdout')),
                            **check_request(profile, count)})
            if count == 1:
                for field, replacement in (('outcome', None), ('available', 6), ('unlocked', False), ('attempts', 0), ('requested_count', True)):
                    changed = copy.deepcopy(profile); changed[field] = replacement
                    try: check_request(changed, count)
                    except ValueError as error: corruptions.append({'mode': mode, 'field': field, 'rejection': str(error)})
                    else: raise ValueError('accepted corrupt capacity observation')
        # ReleaseFast has undefined behavior beyond the ordinary domain. Do not
        # turn it into an allocator result or execute that undefined behavior.
        if mode == 'ReleaseFast': continue
        for count, reason in ((1717986919, 'attempt to unwrap error: Overflow'), (4294967295, 'integer does not fit in destination type')):
            name = 'capacity-' + mode + '-' + str(count); started = time.monotonic()
            response = subprocess.run([str(binary), str(count)], cwd=output, env=env, stdout=subprocess.PIPE,
                                      stderr=subprocess.PIPE, timeout=30, preexec_fn=no_core)
            (output / (name + '.stdout')).write_bytes(response.stdout); (output / (name + '.stderr')).write_bytes(response.stderr)
            record = {'mode': mode, 'count': count, 'expectedRejection': reason, 'exitCode': response.returncode,
                      'binarySha256': digest(binary), 'stderrSha256': digest(output / (name + '.stderr')), 'seconds': time.monotonic() - started}
            write_json(output / (name + '.process.json'), record)
            require(response.returncode == -signal.SIGABRT and not response.stdout and len(response.stderr) <= 65536 and
                    reason.encode() in response.stderr and b'in capacityForSize' in response.stderr and b'/std/hash_map.zig:' in response.stderr,
                    'native capacity rejection changed or did not reach its intended boundary')
            rejected.append(record)
    return {'observations': records, 'observationControls': corruptions, 'nativeRejections': rejected,
            'releaseFastNonordinaryExecuted': False}
