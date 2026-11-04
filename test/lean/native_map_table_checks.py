"""Check native/logical table correspondence for selected absent-key publication.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import json
import native_map_insertion_checks as insertion
from native_map_key_checks import GRAPH, BUCKETS, require, app, path, telescope, expressions
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check
from check_zig_air_memory_proofs import without_imports
from check_word_swap import ROOT
from build_toolchain import digest, run

MODULE = 'Compiler.Extraction.ExpressionMapTableTests'
TABLE = insertion.MAP + 'Table.'
INSERT = insertion.INSERT
OWNED = 'Compiler.Extraction.OwnedKeys.'
BASE = 'Compiler.Extraction.Memory.Arguments.Normalization.'
WORLD = BASE + 'OwnedCall.World.'
PUB = BASE + 'OwnedCall.Publication.'
TESTS = GRAPH + 'MapTableTests.'
CLAIMS = [INSERT + 'Published.' + n for n in ('outside', 'foreign', 'metadata_other', 'stored_other')]
CLAIMS += [TABLE + n for n in ('EntryView.unique', 'EntryView.of_live', 'EntryView.frame', 'occupied_iff',
    'count_le', 'count_bound', 'count_room', 'byte_of_used', 'used_frame', 'Binding.of_ready',
    'count_changed', 'publication_count', 'Binding.after_new_slot')]
CLAIMS += [GRAPH + n for n in ('prepareGrowth_keys', 'Facts.store_absent', 'Facts.publish_absent', 'publishSelectedNew_rejected', 'Facts.publish_selected_new')]
CLAIMS += [TESTS + n for n in ('empty_custody', 'repeated_from_initialized_owner', 'argument_view',
    'wrong_arguments_rejected', 'phantom_entry_rejected', 'uninitialized_metadata_rejected', 'ghost_only_entry_rejected',
    'wrong_size_rejected', 'wrong_slot_rejected', 'unowned_arguments_rejected')]


def native_path(value, node, scope, state):
    path(value, node, scope, (BASE + 'Session.memory', WORLD + 'memory'), state)


def keys_path(value, node, scope, state):
    path(value, node, scope, (PUB + 'Effects.keys', BASE + 'Session.effects', WORLD + 'memory'), state)


def binding_at(value, node, scope, state):
    args = app(value, node, TABLE + 'Binding')
    require([expressions.named(value, a, scope) for a in args[:5]] ==
            ['place', 'safety', 'receiver', 'bucket', 'bucketCapacity'], 'table binding changed receiver or capacity')
    native_path(value, args[-2], scope, state)
    keys_path(value, args[-1], scope, state)


def audit(rows):
    indexed = {row['theorem']: row for row in rows}
    dependencies = {
        INSERT + 'Published.stored_other': {INSERT + 'Published.outside', BUCKETS + 'Entry.Completed.outside'},
        TABLE + 'EntryView.unique': {TABLE + 'EntryView.contents', TABLE + 'EntryView.stored', 'List.ext_getElem'},
        TABLE + 'EntryView.frame': {INSERT + 'Published.stored_other', INSERT + 'Published.foreign', BASE + 'represented_frame'},
        TABLE + 'EntryView.of_live': {BASE + 'Valid.related', 'Or.resolve_left'},
        TABLE + 'Binding.of_ready': {INSERT + 'Layout.of_ready', TABLE + 'occupied_iff'},
        TABLE + 'Binding.after_new_slot': {TABLE + 'EntryView.unique', TABLE + 'EntryView.frame', TABLE + 'publication_count'},
        GRAPH + 'Facts.store_absent': {OWNED + 'after_live', OWNED + 'store_unique', OWNED + 'store_apart', OWNED + 'view_store'},
        GRAPH + 'Facts.publish_absent': {GRAPH + 'Facts.store_absent', PUB + 'publish_absent'},
        GRAPH + 'Facts.publish_selected_new': {GRAPH + 'Facts.publish_new_slot', GRAPH + 'Facts.store_absent',
            TABLE + 'EntryView.of_live', TABLE + 'Binding.after_new_slot', TABLE + 'count_room', TABLE + 'count_bound',
            BASE + 'Valid.related', 'Compiler.ZigAir.Memory.WordArray.view_width'},
        TESTS + 'repeated_from_initialized_owner': {GRAPH + 'MapCapacityTests.from_initialized_owner',
            GRAPH + 'Facts.publish_selected_new', TABLE + 'Binding.of_ready', TABLE + 'publication_count', GRAPH + 'prepareGrowth_keys'},
        TESTS + 'wrong_arguments_rejected': {TABLE + 'EntryView.unique', TESTS + 'argument_view'},
    }
    for name, needed in dependencies.items():
        require(needed <= set(indexed[name]['dependencies']), 'table proof lost composition: ' + name + ': ' + str(sorted(needed - set(indexed[name]['dependencies']))))
    for name in CLAIMS:
        if not name.startswith(TESTS):
            require(not any(part.endswith('Tests') for dep in indexed[name]['dependencies'] for part in dep.split('.')), 'table core depends on a fixture')
    name = GRAPH + 'Facts.publish_selected_new'
    value = indexed[name]['statement']; fields, _, root, scope = telescope(value)
    wanted = ['σ', 'safety', 'allocator', 'owner', 'capacity', 'data', 'before', 'rows', 'facts',
        'place', 'receiver', 'bucketCapacity', 'bucket', 'index', 'embedded', 'binding', 'fp', 'available', 'inside',
        'availableRead', 'room', 'vacant', 'key', 'owned', 'id', 'aligned', 'absent', 'custody']
    require(list(fields) == wanted, 'table producer gained a resulting view, size bound or successful-prefix premise')
    binding_at(value, *fields['binding'], 'before')
    node, context = fields['vacant']
    unused = app(value, app(value, node, 'Not')[0], TABLE + 'Used')
    native_path(value, unused[0], context, 'before')
    require([expressions.named(value, a, context) for a in unused[1:]] == ['bucket', 'index'], 'vacancy concerns another slot')
    node, context = fields['absent']; absent = app(value, node, 'Eq')
    selected = value['nodes'][absent[-2]]
    require(selected[0] == 'app' and expressions.named(value, selected[2], context) == 'key', 'absence concerns another key')
    keys_path(value, selected[1], context, 'before'); app(value, absent[-1], 'Option.none')
    node, context = fields['aligned']; aligned = app(value, node, 'Eq')
    path(value, aligned[-2], context, ('Compiler.Extraction.Cache.Key.arguments',), 'key')
    path(value, aligned[-1], context, ('Compiler.Extraction.Storage.ArgumentSlice.items',), 'owned')
    node, context = fields['custody']
    custody = app(value, node, BASE + 'OwnedCall.Caller.GraphCustody')
    require([expressions.named(value, a, context) for a in custody[:-1]] == ['σ', 'allocator', 'owned', 'rows'], 'table custody changed its owner')
    path(value, custody[-1], context, (WORLD + 'memory',), 'before')
    witness = value['nodes'][app(value, root, 'Exists')[-1]]
    require(witness[:2] == ['lambda', 'after'], 'table producer lost actual reached world')
    scope += ['after']; equation, rest = app(value, witness[4], 'And')
    equation = app(value, equation, 'Eq')
    require([expressions.named(value, a, scope) for a in app(value, equation[-2], GRAPH + 'publishSelectedNew')] ==
            ['σ', 'place', 'safety', 'receiver', 'bucketCapacity', 'bucket', 'index', 'fp', 'key', 'owned', 'id', 'before'],
            'table producer rebound its actual native inputs')
    result = app(value, equation[-1], 'Prod.mk')
    app(value, result[-2], 'Except.ok')
    require(expressions.named(value, result[-1], scope) == 'after', 'table execution discarded native memory')
    facts, rest = app(value, rest, 'And')
    require(expressions.named(value, app(value, facts, GRAPH + 'Facts')[-2], scope) == 'after', 'table graph facts concern another world')
    bound, rest = app(value, rest, 'And'); binding_at(value, bound, scope, 'after')
    stored, rest = app(value, rest, 'And'); stored = app(value, stored, 'Eq')
    keys_path(value, stored[-2], scope, 'after')
    update = app(value, stored[-1], OWNED + 'store')
    keys_path(value, update[0], scope, 'before')
    require(expressions.named(value, update[1], scope) == 'key', 'table producer installed another key')
    entry = app(value, update[2], OWNED + 'Entry.mk')
    path(value, entry[0], scope, ('Compiler.Extraction.Storage.ArgumentSlice.address',), 'owned')
    require(expressions.named(value, entry[1], scope) == 'id', 'table producer installed another ID')
    effects, post = app(value, rest, 'And'); effects = app(value, effects, 'Eq')
    for arg, state in zip(effects[-2:], ('after', 'before')):
        path(value, arg, scope, (PUB + 'Effects.allocator', BASE + 'Session.effects', WORLD + 'memory'), state)
    post = app(value, post, INSERT + 'Published')
    require([expressions.named(value, a, scope) for a in post[:8]] ==
            ['place', 'safety', 'receiver', 'bucket', 'index', 'bucketCapacity', 'fp', 'available'], 'native publication changed its slot or counters')
    original_count = app(value, app(value, post[8], 'BitVec.ofNat')[-1], TABLE + 'count')
    require([expressions.named(value, a, scope) for a in original_count[:2]] == ['bucketCapacity', 'bucket'], 'size bound counts another map')
    native_path(value, original_count[-1], scope, 'before')
    require(expressions.named(value, post[9], scope) == 'key' and expressions.named(value, post[11], scope) == 'id', 'native and logical entries differ')
    pointer = app(value, post[10], 'Compiler.ZigAir.Memory.Address.mk')
    path(value, pointer[0], scope, ('Compiler.Extraction.Storage.ArgumentSlice.address',), 'owned')
    require(expressions.named(value, app(value, pointer[1], 'OfNat.ofNat')[1], scope) == ('natural', '0'), 'native arguments changed offset')
    for arg, state in zip(post[-2:], ('before', 'after')): native_path(value, arg, scope, state)
    return {'checkedDependencies': sorted(dependencies), 'checkedStatements': [name],
            'selectedAbsentKeyNativeTableCorrespondenceDerived': True, 'argumentContentsFromOriginalCustody': True,
            'sizeBoundFromUnusedSlot': True, 'probingVerified': False, 'nativeHashMapVerified': False}


def interfaces(output, env, lean):
    records = expressions.interface_export(output, env, lean, MODULE, (TABLE + 'EntryView.mk', TABLE + 'Binding.mk'))
    audit_interfaces(records)
    return {'sha256': digest(output / 'interfaces.json'), 'checked': [TABLE + 'EntryView.mk', TABLE + 'Binding.mk']}


def audit_interfaces(records):
    indexed = {record['name']: record for record in records}
    expected = {
        'EntryView': (['capacity', 'bucket', 'index', 'state', 'key', 'entry', 'stored', 'contents', 'owned'],
                      {'stored': BUCKETS + 'Entry.Stored', 'contents': 'Compiler.ZigAir.Memory.WordArray.Represents',
                       'owned': 'Compiler.Extraction.Memory.Arguments.Owned'}),
        'Binding': (['place', 'safety', 'receiver', 'bucket', 'capacity', 'state', 'table', 'layout', 'metadata', 'size', 'slots', 'entries', 'unique'],
                    {'layout': INSERT + 'Layout', 'metadata': BUCKETS + 'Metadata.readByte', 'size': TABLE + 'count',
                     'slots': TABLE + 'EntryView', 'entries': TABLE + 'EntryView', 'unique': TABLE + 'EntryView'}),
    }
    for name, (wanted, required) in expected.items():
        record = indexed[TABLE + name + '.mk']; value = record['type']
        fields, _, _, _ = telescope(value)
        require(list(fields) == wanted, 'native table relation lost an independent observation: ' + name)
        for field, constant in required.items():
            require(constant in expressions.step.constants_below(value, fields[field][0]), 'native table relation lost ' + field)
        if name == 'EntryView':
            node, context = fields['contents']
            contents = app(value, node, 'Compiler.ZigAir.Memory.WordArray.Represents')
            require(expressions.named(value, contents[0], context) == 'state', 'argument reads use another memory')
            sliced = app(value, app(value, contents[1], 'Compiler.Extraction.Memory.Arguments.view')[0], OWNED + 'slice')
            require([expressions.named(value, a, context) for a in sliced] == ['key', 'entry'], 'argument reads use another slice')
            path(value, contents[2], context, ('Compiler.Extraction.Cache.Key.arguments',), 'key')


def controls(output, env, lean):
    directory = ROOT / 'lean/Compiler/Extraction'
    source = 'import Compiler.Extraction.ExpressionMapNewTests\n'
    for name in ('ExpressionMapSlotFrame', 'ExpressionMapTableEntry', 'ExpressionMapTable',
                 'ExpressionMapTableInsertion', 'ExpressionMapTablePublication'):
        source += without_imports((directory / (name + '.lean')).read_text()) + '\n'
    fixture = without_imports((directory / 'ExpressionMapTableTests.lean').read_text())
    records = [mutation_check(output, 'table-unchanged', source + fixture, True, env, lean)]
    for name, before, after in (
        ('argument-contents', 'key.arguments\n  owned :', '[]\n  owned :'),
        ('native-count', '(List.range capacity.toNat).countP (occupied state bucket)', '0'),
        ('ignore-used', '| .ok (free, used) => !free && used', '| .ok (_free, _used) => false'),
        ('discard-logical-update', '(.ok (), Publication.freshWorld key owned id reached.memory.effects.allocator reached)', '(.ok (), reached)'),
        ('wrong-logical-id', '(.ok (), Publication.freshWorld key owned id reached.memory.effects.allocator reached)', '(.ok (), Publication.freshWorld key owned (id + 1) reached.memory.effects.allocator reached)'),
        ('discard-native-writes', '(.ok (), Publication.freshWorld key owned id reached.memory.effects.allocator reached)', '(.ok (), Publication.freshWorld key owned id reached.memory.effects.allocator before)'),
        ('discard-rejection-prefix', '| (.error fault, reached) => (.error fault, reached)', '| (.error fault, _reached) => (.error fault, before)'),
    ):
        require(before in source, 'missing table control: ' + name)
        records.append(mutation_check(output, 'table-' + name, source.replace(before, after, 1), False, env, lean))
    return checked_controls(output, records)


def check_observation(record):
    scalars = {'first_id': 4275878552, 'second_id': 53, 'lookup_first': 4275878552, 'lookup_second': 53, 'used_slots': 2, 'available': 4}
    flags = ('second_key_retained', 'second_pointer_retained', 'both_new', 'distinct_slots')
    insertion.entries.keys.admission.fields(record, ('schema', 'first', 'second_arguments', *scalars, *flags), 'table')
    require(record['schema'] == 'oksolc.expression-map-table.v1', 'wrong table schema')
    require(all(type(record[k]) is int and record[k] == v for k, v in scalars.items()), 'wrong table counts or IDs')
    require(all(record[k] is True for k in flags), 'table lost a key, slot or argument buffer')
    arguments = record['second_arguments']
    require(type(arguments) is list and all(type(v) is int for v in arguments) and arguments == [5, 17, 4294967294], 'wrong second argument contents')
    insertion.entries.keys.check_observation(record['first'], value_retained=False, count=2)
    return record


def capture(output, env):
    records, controls = [], []
    for mode in ('Debug', 'ReleaseSafe', 'ReleaseFast'):
        binary = output / ('buckets-' + mode); name = 'table-' + mode
        run(output, name, [binary, 'table'], cwd=ROOT, env=env)
        raw = (output / (name + '.stdout')).read_bytes()
        require(len(raw) <= 4096 and not (output / (name + '.stderr')).read_bytes(), 'unbounded or noisy table capture')
        record = check_observation(json.loads(raw))
        records.append({'mode': mode, 'binarySha256': digest(binary), 'observationSha256': digest(output / (name + '.stdout')), 'observed': record})
        for field, changed in (('first_id', 53), ('lookup_first', None), ('lookup_second', 4275878552), ('used_slots', 1),
                               ('available', 5), ('both_new', False), ('distinct_slots', False), ('second_arguments', [5, 17, 4294967295]),
                               ('second_pointer_retained', False), ('second_key_retained', False)):
            bad = copy.deepcopy(record); bad[field] = changed
            try: check_observation(bad)
            except ValueError as error: controls.append({'mode': mode, 'field': field, 'rejection': str(error)})
            else: raise ValueError('accepted corrupt table observation')
    return {'captures': records, 'observationControls': controls,
            'scope': 'two distinct native argument keys retain both entries; probing is exercised, not proved'}
