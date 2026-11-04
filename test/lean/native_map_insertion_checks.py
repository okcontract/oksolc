"""Check the complete selected new-slot storage and publication route.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import json
from pathlib import Path
import native_map_entry_checks as entries
from native_map_key_checks import GRAPH, BUCKETS, KEY, require, app, path, telescope, expressions
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check
from check_zig_air_memory_proofs import without_imports
from check_word_swap import ROOT
from build_toolchain import digest, run

MODULE = 'Compiler.Extraction.ExpressionMapNewTests'
MAP = 'Compiler.Extraction.ExpressionMap.'
META = BUCKETS + 'Metadata.'
ENTRY = BUCKETS + 'Entry.'
COUNTER = MAP + 'Counter.'
INSERT = MAP + 'Insertion.'
TESTS = GRAPH + 'MapNewTests.'
MEMORY = 'Compiler.ZigAir.Memory.'
CLAIMS = [META + 'store_byte_total'] + [ENTRY + n for n in ('writePointers_steps', 'write_pointers_verified')]
CLAIMS += [COUNTER + n for n in ('pointer_eq', 'read_eq', 'Stored.native_frame', 'Stored.read', 'Stored.others',
    'Stored.header', 'adjust_steps', 'adjust_verified', 'adjust_rejected', 'next_exact')]
CLAIMS += [META + n for n in ('packed_exact', 'read_byte_of_load', 'read_byte_frame', 'observe_read_byte', 'read_byte_free',
    'store_outside', 'mark_verified', 'Marked.headers')]
CLAIMS += [ENTRY + n for n in ('reset_verified', 'Reset.native_frame', 'Reset.outside', 'Reset.headers', 'Reset.metadata')]
CLAIMS += [INSERT + 'Layout.' + n for n in ('apart', 'counter', 'bucket_frame', 'marked', 'reset', 'assigned',
    'counter_frame', 'bucket_read_frame', 'of_ready')]
CLAIMS += [INSERT + n for n in ('prepare_steps', 'prepare_verified', 'publish_steps', 'publish_verified', 'Published.cursors')]
CLAIMS += [GRAPH + n for n in ('Facts.counter_stored', 'Facts.new_publication_frame', 'publishNewSlot_prefix', 'Facts.publish_new_slot')]
CLAIMS += [TESTS + n for n in ('from_initialized_owner', 'stale_value', 'prepared_pointers', 'erased_key', 'erased_value',
    'prepared_counters', 'prepared_metadata', 'published', 'readback', 'final_counters', 'final_metadata', 'neighbor_metadata',
    'underflow_rejected', 'metadata_rejection_prefix', 'rejected_metadata_keeps_decrement', 'size_rejection_prefix', 'rejected_size_keeps_erasure')]

NEW_SLOT = '''{
    const hash: Hash = ctx.hash(key);
    const mask = self.capacity() - 1;
    const fingerprint = Metadata.takeFingerprint(hash);
    var limit = self.capacity();
    var idx = @as(usize, @truncate(hash & mask));
    var first_tombstone_idx: usize = self.capacity();
    var metadata = self.metadata.? + idx;
    while (!metadata[0].isFree() and limit != 0) {
        if (metadata[0].isUsed() and metadata[0].fingerprint == fingerprint) {
            const test_key = &self.keys()[idx];
            if (ctx.eql(key, test_key.*)) {
                return GetOrPutResult{ .key_ptr = test_key, .value_ptr = &self.values()[idx], .found_existing = true, };
            }
        } else if (first_tombstone_idx == self.capacity() and metadata[0].isTombstone()) {
            first_tombstone_idx = idx;
        }
        limit -= 1;
        idx = (idx + 1) & mask;
        metadata = self.metadata.? + idx;
    }
    if (first_tombstone_idx < self.capacity()) {
        idx = first_tombstone_idx;
        metadata = self.metadata.? + idx;
    }
    self.available -= 1;
    metadata[0].fill(fingerprint);
    const new_key = &self.keys()[idx];
    const new_value = &self.values()[idx];
    new_key.* = undefined;
    new_value.* = undefined;
    self.size += 1;
    return GetOrPutResult{ .key_ptr = new_key, .value_ptr = new_value, .found_existing = false, };
}'''
SIGNATURE = 'pub fn getOrPutAssumeCapacityAdapted(self: *Self, key: anytype, ctx: anytype) GetOrPutResult'
CONTEXT = 'pub fn getOrPutContext(self: *Self, allocator: Allocator, key: K, ctx: Context) Allocator.Error!GetOrPutResult'


def source_binding(lib, native=None):
    native = (Path(lib) / 'std/hash_map.zig').read_bytes() if native is None else native
    function = entries.keys.admission.storage.function
    function(native, 'pub fn fill(self: *Metadata, fp: FingerPrint) void').expect('{ self.used = 1; self.fingerprint = fp; }')
    require(native.count(b'\nfn Custom(') == 1, 'ambiguous unmanaged hash-map owner')
    unmanaged = native[native.index(b'\nfn Custom('):]
    function(unmanaged, SIGNATURE).expect(NEW_SLOT)
    function(native, CONTEXT).expect('''{
        const gop = try self.getOrPutContextAdapted(allocator, key, ctx, ctx);
        if (!gop.found_existing) { gop.key_ptr.* = key; }
        return gop;
    }''')
    binding = entries.source_binding(lib, native=native)
    return {**binding, 'scope': 'selected new-slot suffix, getOrPutContext key assignment, and publishOwned stores',
            'selectedNewSlotSourceAdmitted': True, 'probingVerified': False, 'logicalTableTransitionVerified': False,
            'sourceAdapterFormallyVerified': False, 'nativeHashMapVerified': False}


def source_controls(lib):
    native = (Path(lib) / 'std/hash_map.zig').read_bytes(); records = []
    for signature, end, before, after in (
        (SIGNATURE, 'pub fn getOrPutValue(', 'self.available -= 1;', 'self.available += 1;'),
        (SIGNATURE, 'pub fn getOrPutValue(', 'metadata[0].fill(fingerprint);', 'metadata[1].fill(fingerprint);'),
        (SIGNATURE, 'pub fn getOrPutValue(', 'const new_key = &self.keys()[idx];', 'const new_key = &self.keys()[0];'),
        (SIGNATURE, 'pub fn getOrPutValue(', 'const new_value = &self.values()[idx];', 'const new_value = &self.values()[0];'),
        (SIGNATURE, 'pub fn getOrPutValue(', 'new_key.* = undefined;', 'new_key.* = key;'),
        (SIGNATURE, 'pub fn getOrPutValue(', 'new_value.* = undefined;', 'new_value.* = 0;'),
        (SIGNATURE, 'pub fn getOrPutValue(', 'self.size += 1;', 'self.size -= 1;'),
        (SIGNATURE, 'pub fn getOrPutValue(', '.found_existing = false,', '.found_existing = true,'),
        ('pub fn fill(self: *Metadata', 'pub fn remove(', 'self.used = 1;', 'self.used = 0;'),
        ('pub fn fill(self: *Metadata', 'pub fn remove(', 'self.fingerprint = fp;', 'self.fingerprint = 0;'),
        (CONTEXT, 'pub fn getOrPutAdapted(', 'if (!gop.found_existing)', 'if (gop.found_existing)'),
        (CONTEXT, 'pub fn getOrPutAdapted(', 'gop.key_ptr.* = key;', 'gop.key_ptr.* = undefined;'),
    ):
        owner = native.index(b'\nfn Custom(')
        require(native[owner:].count(signature.encode()) == 1, 'ambiguous source owner')
        start = native.index(signature.encode(), owner); stop = native.index(end.encode(), start)
        body = native[start:stop]
        require(before.encode() in body, 'missing new-slot source mutation')
        changed = native[:start] + body.replace(before.encode(), after.encode(), 1) + native[stop:]
        try: source_binding(lib, changed)
        except (ValueError, entries.keys.admission.storage.Unsupported) as error:
            records.append({'source': signature, 'mutation': after, 'rejection': str(error)})
        else: raise ValueError('accepted changed selected new-slot source')
    return records


def audit(rows):
    indexed = {row['theorem']: row for row in rows}
    dependencies = {
        META + 'store_byte_total': {META + 'byte_views', MEMORY + 'store_subobject_total'},
        META + 'mark_verified': {META + 'store_byte_total', META + 'packed_exact', META + 'store_outside'},
        ENTRY + 'reset_verified': {MEMORY + 'invalidate_of_access', KEY + 'access_entry', entries.VALUES + 'access_entry'},
        ENTRY + 'write_pointers_verified': {KEY + 'assign_verified', entries.VALUES + 'store_total', ENTRY + 'writePointers_steps'},
        COUNTER + 'adjust_verified': {MAP + 'Initialization.store_value_at_total', COUNTER + 'pointer_eq', COUNTER + 'read_eq', COUNTER + 'adjust_steps'},
        INSERT + 'prepare_verified': {COUNTER + 'adjust_verified', META + 'mark_verified', ENTRY + 'reset_verified', INSERT + 'prepare_steps'},
        INSERT + 'publish_verified': {INSERT + 'prepare_verified', KEY + 'assign_verified', ENTRY + 'write_pointers_verified', INSERT + 'publish_steps', COUNTER + 'next_exact'},
        GRAPH + 'Facts.counter_stored': {GRAPH + 'Facts.map_frame', GRAPH + 'Facts.local_map_frame'},
        GRAPH + 'Facts.new_publication_frame': {GRAPH + 'Facts.counter_stored', GRAPH + 'Facts.private_map_frame'},
        GRAPH + 'Facts.publish_new_slot': {INSERT + 'publish_verified', GRAPH + 'Facts.new_publication_frame', GRAPH + 'publishNewSlot_prefix'},
        TESTS + 'from_initialized_owner': {entries.keys.capacity.TESTS + 'from_initialized_owner', INSERT + 'Layout.of_ready',
            GRAPH + 'Facts.publish_new_slot', META + 'read_byte_free', INSERT + 'Published.cursors'},
        TESTS + 'underflow_rejected': {COUNTER + 'adjust_rejected'},
    }
    for name, required in dependencies.items():
        require(required <= set(indexed[name]['dependencies']), 'new-slot proof lost composition: ' + name)
    for name in CLAIMS:
        if not name.startswith(TESTS):
            require(not any(part.endswith('Tests') for dep in indexed[name]['dependencies'] for part in dep.split('.')),
                    'new-slot core depends on a fixture')
    original = ['σ', 'safety', 'allocator', 'owner', 'capacity', 'data', 'before', 'rows', 'facts']
    binders = {
        INSERT + 'prepare_verified': ['place', 'safety', 'receiver', 'capacity', 'bucket', 'index', 'fp', 'before', 'layout',
            'available', 'size', 'bits', 'inside', 'availableRead', 'sizeRead', 'metadataRead', 'room', 'bounded'],
        INSERT + 'publish_verified': ['place', 'safety', 'receiver', 'capacity', 'bucket', 'index', 'fp', 'before', 'layout',
            'available', 'size', 'bits', 'inside', 'availableRead', 'sizeRead', 'metadataRead', 'room', 'bounded', 'key', 'arguments', 'id', 'length'],
        GRAPH + 'Facts.publish_new_slot': original + ['place', 'receiver', 'bucketCapacity', 'bucket', 'index', 'embedded', 'layout',
            'fp', 'available', 'size', 'bits', 'inside', 'availableRead', 'sizeRead', 'metadataRead', 'room', 'bounded', 'key', 'arguments', 'id', 'length'],
        GRAPH + 'publishNewSlot_prefix': ['σ', 'place', 'safety', 'receiver', 'bucketCapacity', 'bucket', 'index', 'fp', 'key',
            'arguments', 'id', 'before', 'result', 'memory', 'ran'],
        TESTS + 'from_initialized_owner': ['safety', 'meaning', 'index', 'fp', 'key', 'arguments', 'id', 'length'],
    }
    for name, wanted in binders.items():
        value = indexed[name]['statement']; fields, _, root, scope = telescope(value)
        require(list(fields) == wanted, 'new-slot theorem gained a prepared/outcome premise: ' + name)
        if name == GRAPH + 'publishNewSlot_prefix':
            entries.keys.audit_prefix(value, root, scope, GRAPH + 'publishNewSlot',
                ['σ', 'place', 'safety', 'receiver', 'bucketCapacity', 'bucket', 'index', 'fp', 'key', 'arguments', 'id', 'before'])
        if name in (INSERT + 'publish_verified', GRAPH + 'Facts.publish_new_slot'):
            native = name.startswith(GRAPH)
            layout, context = fields['layout']
            args = app(value, layout, INSERT + 'Layout')
            require([expressions.named(value, a, context) for a in args[:-1]] ==
                    ['place', 'safety', 'receiver', 'bucket', 'bucketCapacity' if native else 'capacity'], 'new-slot layout changed its source receiver')
            if native:
                path(value, args[-1], context, ('Compiler.Extraction.Memory.Arguments.Normalization.Session.memory',
                    'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.World.memory'), 'before')
            else: require(expressions.named(value, args[-1], context) == 'before', 'new-slot layout assumes a post-state')
            witness = value['nodes'][app(value, root, 'Exists')[-1]]
            require(witness[:2] == ['lambda', 'after'], 'new-slot theorem lost actual final state')
            scope = scope + ['after']; equation, rest = app(value, witness[4], 'And'); equation = app(value, equation, 'Eq')
            expected = (['σ'] if native else []) + ['place', 'safety', 'receiver', 'bucketCapacity' if native else 'capacity',
                'bucket', 'index', 'fp', 'key', 'arguments', 'id', 'before']
            function = GRAPH + 'publishNewSlot' if native else INSERT + 'publish'
            require([expressions.named(value, a, scope) for a in app(value, equation[-2], function)] == expected, 'new-slot execution rebound original inputs')
            result = app(value, equation[-1], 'Prod.mk')
            require(expressions.named(value, result[-1], scope) == 'after', 'new-slot execution discarded final memory')
            if native:
                facts, rest = app(value, rest, 'And')
                require(expressions.named(value, app(value, facts, GRAPH + 'Facts')[-2], scope) == 'after', 'new-slot facts concern another state')
                rest, _ = app(value, rest, 'And')
            post = app(value, rest, INSERT + 'Published')
            require([expressions.named(value, a, scope) for a in post[:-2]] == ['place', 'safety', 'receiver', 'bucket', 'index',
                'bucketCapacity' if native else 'capacity', 'fp', 'available', 'size', 'key', 'arguments', 'id'], 'new-slot observations rebound a location, counter or entry')
            for arg, state in zip(post[-2:], ('before', 'after')):
                if native:
                    path(value, arg, scope, ('Compiler.Extraction.Memory.Arguments.Normalization.Session.memory',
                        'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.World.memory'), state)
                else: require(expressions.named(value, arg, scope) == state, 'new-slot observations concern another state')
    return {'checkedDependencies': sorted(dependencies), 'checkedStatements': sorted(binders),
            'selectedNewSlotStoresDerived': True, 'capturedPointersConsumed': True, 'nativeGraphFramesReused': True,
            'probingVerified': False, 'logicalTableTransitionVerified': False, 'nativeHashMapVerified': False}


def controls(output, env, lean):
    directory = ROOT / 'lean/Compiler/Extraction'
    source = 'import Compiler.Extraction.ExpressionMapEntryTests\nimport Compiler.ZigAir.MemoryInvalidationFrame\n'
    for name in ('ExpressionMapCounter.lean', 'ExpressionMapMetadataWrite.lean', 'ExpressionMapEntryReset.lean',
                 'ExpressionMapInsertionLayout.lean', 'ExpressionMapNewSlot.lean', 'ExpressionMapNewPublication.lean',
                 'ExpressionMapNewMemory.lean'):
        source += without_imports((directory / name).read_text()) + '\n'
    fixtures = without_imports((directory / 'ExpressionMapNewTests.lean').read_text())
    core_fixture = fixtures.split('open Compiler.ZigAir.Memory\nopen MapKeyTests')[0] + '\nend ' + TESTS.removesuffix('.') + '\n'
    records = [mutation_check(output, 'new-slot-unchanged', source + core_fixture, True, env, lean),
               mutation_check(output, 'new-slot-fixtures-unchanged', source + fixtures, True, env, lean)]
    for name, before, after in (
        ('used-bit', '128 + bits.toNat % 128', 'bits.toNat % 128'),
        ('fingerprint', 'bits.toNat / 128 * 128 + fp.toNat', 'bits.toNat / 128 * 128'),
        ('decrement', '| .available, value => value - 1#32', '| .available, value => value + 1#32'),
        ('increment', '| .size, value => value + 1#32', '| .size, value => value - 1#32'),
        ('counter-fault', '(.error (Capacity.rejected safety), before)', '(.error .outOfMemory, before)'),
        ('key-undefined', 'match undefine before keyPointer with', 'match (Except.ok before : Except Fault State) with'),
        ('value-undefined', '| .ok middle => match undefine middle valuePointer with', '| .ok middle => match (Except.ok middle : Except Fault State) with'),
        ('discard-reset', '| .ok middle => match undefine middle valuePointer with', '| .ok middle => match undefine before valuePointer with'),
        ('skip-available', 'match Counter.adjust place safety receiver .available before with', 'match (Except.ok (), before) with'),
        ('skip-metadata', '| (.ok (), down) => match Metadata.mark bucket index fp down with', '| (.ok (), down) => match (Except.ok (), down) with'),
        ('value-pointer', 'match Values.entryPointer marked capacity bucket index with', 'match Values.entryPointer marked capacity bucket (index + 1) with'),
        ('skip-reset', '| .ok valuePointer => match Entry.reset keyPointer valuePointer marked with', '| .ok valuePointer => match (Except.ok (), marked) with'),
        ('skip-size', '| (.ok (), erased) => match Counter.adjust place safety receiver .size erased with', '| (.ok (), erased) => match (Except.ok (), erased) with'),
        ('existing-flag', '(.ok ⟨keyPointer, valuePointer, false⟩, counted)', '(.ok ⟨keyPointer, valuePointer, true⟩, counted)'),
        ('discard-marked-prefix', '| (.error fault, marked) => (.error fault, marked)', '| (.error fault, _marked) => (.error fault, before)'),
        ('discard-erased-prefix', '| (.error fault, counted) => (.error fault, counted)', '| (.error fault, _counted) => (.error fault, before)'),
        ('skip-context-key', 'match KeyFields.writes entry.keyPointer key arguments KeyFields.order counted with', 'match (Except.ok (), counted) with'),
        ('discard-context-key', 'key arguments id installed\n', 'key arguments id counted\n'),
        ('wrong-id', 'key arguments id installed\n', 'key arguments (id + 1) installed\n'),
        ('discard-world', '\n  (result, { before with memory := { before.memory with memory } })\n', '\n  (result, before)\n'),
    ):
        require(before in source, 'missing new-slot mutation: ' + name)
        # Only failure-prefix mutations need concrete fault executions. Other
        # changes are rejected by general obligations, avoiding huge evaluated
        # counterexamples from unrelated raw fixture assertions.
        client = fixtures if name in ('discard-marked-prefix', 'discard-erased-prefix') else core_fixture
        records.append(mutation_check(output, 'new-slot-' + name, source.replace(before, after, 1) + client, False, env, lean))
    return checked_controls(output, records)


def check_observation(record):
    scalars = {'id': 4275878552, 'lookup_id': 4275878552, 'index': 5, 'fingerprint': 2, 'metadata_before': 0,
               'metadata_after': 130, 'available_before': 6, 'available_after': 5, 'count_before': 0}
    entries.keys.admission.fields(record, ('schema', 'key', 'found_existing', 'pointers_retained', *scalars), 'new slot')
    require(record['schema'] == 'oksolc.expression-map-new-slot.v1', 'wrong new-slot schema')
    require(all(type(record[k]) is int and record[k] == v for k, v in scalars.items()), 'wrong new-slot counter, metadata or entry')
    require(record['found_existing'] is False and record['pointers_retained'] is True, 'wrong new-slot result or captured pointers')
    entries.keys.check_observation(record['key'], value_retained=False, count=1)
    return record


def capture(output, env):
    records, corruptions = [], []
    for mode in ('Debug', 'ReleaseSafe', 'ReleaseFast'):
        binary = output / ('buckets-' + mode); name = 'new-slot-' + mode
        run(output, name, [binary, 'insert'], cwd=ROOT, env=env)
        raw = (output / (name + '.stdout')).read_bytes()
        require(len(raw) <= 4096 and not (output / (name + '.stderr')).read_bytes(), 'unbounded or noisy new-slot capture')
        record = check_observation(json.loads(raw))
        records.append({'mode': mode, 'binarySha256': digest(binary), 'observationSha256': digest(output / (name + '.stdout')), 'observed': record,
                        'packedFieldCases': 256 * 128})
        for field, replacement in (('id', 37), ('lookup_id', None), ('index', 0), ('fingerprint', 0), ('metadata_before', 1),
                                  ('metadata_after', 2), ('available_before', 5), ('available_after', 6), ('count_before', 1),
                                  ('found_existing', True), ('pointers_retained', False), ('count', 2),
                                  ('neighbor_retained', False), ('argument_pointer_retained', False)):
            changed = copy.deepcopy(record)
            if field in ('count', 'neighbor_retained', 'argument_pointer_retained'): changed['key'][field] = replacement
            else: changed[field] = replacement
            try: check_observation(changed)
            except ValueError as error: corruptions.append({'mode': mode, 'field': field, 'rejection': str(error)})
            else: raise ValueError('accepted corrupt new-slot observation')
    return {'captures': records, 'observationControls': corruptions,
            'scope': 'native first-insertion regression; hash/probing and logical table correspondence are not thereby proved'}
