"""Check native key-field assignment through the existing bucket allocation.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import json
import check_native_invocation as expressions
from constructor_joint_checks import app, path
from native_resource_admission_checks import telescope
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check
from check_zig_air_memory_proofs import without_imports
from check_word_swap import ROOT
from build_toolchain import digest, run
from native_map_write_checks import GRAPH, require
from native_map_allocation_checks import MAP
import native_map_capacity_checks as capacity
import generate_map_bucket_layout as admission

MODULE = 'Compiler.Extraction.ExpressionMapKeyTests'
BUCKETS = MAP + 'Buckets.'
KEY = BUCKETS + 'KeyFields.'
TESTS = GRAPH + 'MapKeyTests.'
CLAIMS = [BUCKETS + 'key_layout']
CLAIMS += [KEY + n for n in ('value_valid', 'region', 'project_key', 'key_view', 'field_views', 'field_selected',
    'access_entry', 'entry_pointer', 'select_verified', 'field_geometry', 'store_total', 'write_total', 'read_other',
    'store_frame', 'writes_verified', 'Written.header', 'Written.read', 'assign_verified', 'assign_rejected')]
CLAIMS += [GRAPH + n for n in ('Facts.assign_key', 'assignKey_prefix')]
CLAIMS += [TESTS + n for n in ('from_initialized_owner', 'sample_values', 'assigned', 'readback', 'const_slice_readback',
    'native_fields_readback', 'neighbors_uninitialized', 'header_retained', 'readonly_rejected', 'rebound_header_rejected',
    'out_of_bounds_rejected', 'missing_header_rejected')]


def source_binding(lib, source=None):
    source = admission.storage.SOURCE.read_bytes() if source is None else source
    binding = admission.source_binding(lib, source=source)
    admission.storage.function(source, 'fn publishOwned(self: *ExpressionClasses, key: ExpressionKey, id: Id)').expect('''std.mem.Allocator.Error!void {
        const entry = try self.expressions.getOrPut(self.allocator, key);
        if (entry.found_existing) self.allocator.free(entry.key_ptr.arguments);
        entry.key_ptr.* = key; entry.value_ptr.* = id; }''')
    return {**binding, 'scope': 'key assignment through checked native header/element/field pointers',
            'keyFieldAssignmentVerified': True, 'nativeHashMapVerified': False, 'sourceAdapterFormallyVerified': False}


def source_controls(lib):
    source = admission.storage.SOURCE.read_bytes(); records = []
    for before, after in ((b'entry.key_ptr.* = key;', b'entry.key_ptr.* = undefined;'),
                          (b'arguments: []const Id,\n    sequence_number: u32,', b'arguments: []Id,\n    sequence_number: u32,'),
                          (b'arguments: []const Id,\n    sequence_number: u32,', b'arguments: []const Id,\n    sequence_number: u64,')):
        require(source.count(before) == 1, 'ambiguous key source control')
        try: source_binding(lib, source.replace(before, after, 1))
        except (ValueError, admission.storage.Unsupported) as error:
            records.append({'mutation': before.decode(), 'rejection': str(error)})
        else: raise ValueError('accepted changed native key assignment')
    return records


def audit_prefix(value, root, scope, function, inputs):
    equation = app(value, root, 'Eq')
    require([expressions.named(value, a, scope) for a in app(value, equation[-2], function)] ==
            inputs, 'key prefix changed its execution inputs')
    result = app(value, equation[-1], 'Prod.mk')
    require(expressions.named(value, result[-2], scope) == 'result', 'key prefix changed its reached result')
    namespace = 'Compiler.Extraction.Memory.Arguments.Normalization.'
    world = app(value, result[-1], namespace + 'OwnedCall.World.mk')
    path(value, world[-2], scope, (namespace + 'OwnedCall.World.graph',), 'before')
    session = value['nodes'][world[-1]]
    require(session[0] == 'let', 'key prefix lost its reached session')
    path(value, session[3], scope, (namespace + 'OwnedCall.World.memory',), 'before')
    local = scope + [session[1]]
    updated = app(value, session[4], namespace + 'Session.mk')
    require(expressions.named(value, updated[-2], local) == 'memory', 'key prefix discarded its partial stores')
    for field, selector in ((updated[-3], 'heap'), (updated[-1], 'effects')):
        path(value, field, local, (namespace + 'Session.' + selector,), session[1])


def audit(rows):
    indexed = {row['theorem']: row for row in rows}
    dependencies = {
        KEY + 'key_view': {KEY + 'project_key'}, KEY + 'field_views': {KEY + 'project_key'},
        KEY + 'entry_pointer': {KEY + 'access_entry'},
        KEY + 'store_total': {KEY + 'access_entry', KEY + 'field_views', 'Compiler.ZigAir.Memory.store_subobject_total'},
        KEY + 'write_total': {KEY + 'store_total', KEY + 'select_verified'},
        KEY + 'writes_verified': {KEY + 'write_total', KEY + 'read_other', KEY + 'store_frame'},
        KEY + 'Written.read': {KEY + 'Written.header', KEY + 'read_eq'},
        KEY + 'assign_verified': {KEY + 'writes_verified', KEY + 'entry_pointer'},
        GRAPH + 'Facts.assign_key': {KEY + 'assign_verified', KEY + 'Written.read', GRAPH + 'Facts.private_map_frame', GRAPH + 'assignKey_prefix'},
        TESTS + 'from_initialized_owner': {capacity.TESTS + 'from_initialized_owner', GRAPH + 'Facts.assign_key'},
        TESTS + 'const_slice_readback': {TESTS + 'readback', TESTS + 'sample_values'},
        TESTS + 'native_fields_readback': {TESTS + 'readback', TESTS + 'sample_values'},
    }
    for name, required in dependencies.items():
        require(required <= set(indexed[name]['dependencies']), 'key assignment lost composition: ' + name)
    for name in CLAIMS:
        if not name.startswith(TESTS):
            require(not any(part.endswith('Tests') for dep in indexed[name]['dependencies'] for part in dep.split('.')),
                    'key assignment core depends on a fixture')
    binders = {
        KEY + 'entry_pointer': ['state', 'capacity', 'bucket', 'index', 'cell', 'inside', 'valid', 'found', 'typed', 'header'],
        KEY + 'store_total': ['state', 'capacity', 'bucket', 'index', 'cell', 'key', 'arguments', 'bounded', 'inside', 'valid', 'found', 'typed', 'writable', 'length', 'slot'],
        KEY + 'writes_verified': ['capacity', 'bucket', 'index', 'key', 'arguments', 'slots', 'before', 'cell', 'bounded', 'inside', 'valid', 'found', 'typed', 'writable', 'length'],
        KEY + 'assign_verified': ['capacity', 'bucket', 'index', 'key', 'arguments', 'before', 'cell', 'inside', 'valid', 'found', 'typed', 'writable', 'length', 'header'],
        GRAPH + 'Facts.assign_key': ['σ', 'safety', 'allocator', 'owner', 'capacity', 'data', 'before', 'rows', 'facts',
            'bucketCapacity', 'bucket', 'index', 'cell', 'inside', 'found', 'typed', 'writable', 'key', 'arguments', 'length', 'header'],
        GRAPH + 'assignKey_prefix': ['σ', 'bucketCapacity', 'bucket', 'index', 'key', 'arguments', 'before', 'result', 'memory', 'ran'],
        TESTS + 'from_initialized_owner': ['safety', 'meaning', 'index', 'key', 'arguments', 'length'],
    }
    for name, wanted in binders.items():
        value = indexed[name]['statement']; fields, _, root, scope = telescope(value)
        require(list(fields) == wanted, 'key assignment gained initialization/outcome premises: ' + name)
        if name == GRAPH + 'assignKey_prefix':
            audit_prefix(value, root, scope, GRAPH + 'assignKey',
                         ['σ', 'bucketCapacity', 'bucket', 'index', 'key', 'arguments', 'before'])
        if name in (KEY + 'assign_verified', GRAPH + 'Facts.assign_key'):
            witness = value['nodes'][app(value, root, 'Exists')[-1]]
            require(witness[:2] == ['lambda', 'after'], 'key assignment lost its actual post-state')
            equation, rest = app(value, witness[4], 'And'); equation = app(value, equation, 'Eq')
            function = KEY + 'assign' if name.startswith(KEY) else GRAPH + 'assignKey'
            wanted = ['capacity', 'bucket', 'index', 'key', 'arguments', 'before'] if name.startswith(KEY) else ['σ', 'bucketCapacity', 'bucket', 'index', 'key', 'arguments', 'before']
            require([expressions.named(value, a, scope + ['after']) for a in app(value, equation[-2], function)] == wanted,
                    'key assignment changed its original inputs')
            result = app(value, equation[-1], 'Prod.mk')
            require(expressions.named(value, result[-1], scope + ['after']) == 'after', 'key assignment returned another state')
            if name.startswith(GRAPH):
                facts, rest = app(value, rest, 'And')
                require(expressions.named(value, app(value, facts, GRAPH + 'Facts')[-2], scope + ['after']) == 'after', 'key assignment framed another graph')
            representation, rest = app(value, rest, 'And')
            represented = app(value, representation, KEY + 'Written')
            capacity_name = 'capacity' if name.startswith(KEY) else 'bucketCapacity'
            require(expressions.named(value, app(value, represented[0], 'BitVec.toNat')[-1], scope + ['after']) == capacity_name,
                    'key representation changed its bucket capacity')
            require([expressions.named(value, represented[i], scope + ['after']) for i in (1, 2, 3, 4, 5)] ==
                    ['bucket', 'index', 'key', 'arguments', KEY + 'order'], 'key representation changed its identity or contents')
            if name.startswith(GRAPH):
                for node, variable in ((represented[-2], 'before'), (represented[-1], 'after')):
                    path(value, node, scope + ['after'], ('Compiler.Extraction.Memory.Arguments.Normalization.Session.memory',
                        'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.World.memory'), variable)
                reads, _ = app(value, rest, 'And'); _, _, body, readScope = telescope(value, reads, scope + ['after'])
                equation = app(value, body, 'Eq'); observed = app(value, equation[-2], KEY + 'read')
                require([expressions.named(value, a, readScope) for a in observed[:-1]] ==
                        ['bucketCapacity', 'bucket', 'index', 'slot'], 'key readback changed its native inputs')
                path(value, observed[-1], readScope, ('Compiler.Extraction.Memory.Arguments.Normalization.Session.memory',
                    'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.World.memory'), 'after')
                contents = app(value, app(value, equation[-1], 'Except.ok')[-1], KEY + 'value')
                require([expressions.named(value, a, readScope) for a in contents] == ['key', 'arguments', 'slot'],
                        'key readback changed its input contents or slice identity')
            else:
                require([expressions.named(value, a, scope + ['after']) for a in represented[-2:]] == ['before', 'after'],
                        'key assignment representation changed its native states')
    return {'checkedDependencies': sorted(dependencies), 'checkedStatements': sorted(binders),
            'keyFieldsAndSliceIdentityDerived': True, 'nativeGraphFrameReused': True,
            'nativeHashMapVerified': False, 'logicalTableReplacementVerified': False}


def controls(output, env, lean):
    directory = ROOT / 'lean/Compiler/Extraction'
    source = 'import Compiler.Extraction.ExpressionMapCapacityTests\n'
    for name in ('ExpressionMapKey.lean', 'ExpressionMapKeyWrites.lean', 'ExpressionMapKeyMemory.lean'):
        source += without_imports((directory / name).read_text()) + '\n'
    core = source
    tests = without_imports((directory / 'ExpressionMapKeyTests.lean').read_text())
    source += tests
    require(tests.count('def before :') == 1, 'ambiguous concrete key fixtures')
    core += tests.split('def before :')[0] + '\nend ' + TESTS.removesuffix('.') + '\n'
    records = [mutation_check(output, 'map-key-unchanged', source, True, env, lean)]
    for name, before, after in (
        ('field-offset', '+ offset slot⟩', '+ offset slot + 4⟩'),
        ('wrong-data', '.int false 256 key.data.toNat', '.int false 256 key.sequence.toNat'),
        ('mutable-arguments', '.slice (.slice false (.scalar (.int false 32))) arguments key.arguments.length',
         '.slice (.slice true (.scalar (.int false 32))) arguments key.arguments.length'),
        ('argument-offset', '.slice (.slice false (.scalar (.int false 32))) arguments key.arguments.length',
         '.slice (.slice false (.scalar (.int false 32))) ⟨arguments.allocation, 0⟩ key.arguments.length'),
        ('wrong-header', 'let keys ← load state (Header.Slot.keys.pointer capacity bucket)',
         'let keys ← load state (Header.Slot.values.pointer capacity bucket)'),
        ('wrong-index', 'elementPointer state keys index', 'elementPointer state keys (index + 1)'),
        ('skip-field', '[.kind, .instruction, .data, .arguments, .sequence]', '[.kind, .instruction, .data, .sequence]'),
        ('discard-write', '| .ok after => writes source key arguments rest after', '| .ok _after => writes source key arguments rest state'),
        ('discard-world', '\n  (result, { before with memory := { before.memory with memory } })\n', '\n  (result, before)\n'),
    ):
        # Mutations target the general proofs, their allocation consumer and
        # source field values. Full memory fixtures remain in the positive gate;
        # evaluating invalid mutated heaps solely to print errors is unnecessary.
        target = core
        require(target.count(before) == 1, 'ambiguous key control: ' + name)
        records.append(mutation_check(output, 'map-key-' + name, target.replace(before, after, 1), False, env, lean))
    return checked_controls(output, records)


def check_observation(record, *, value_retained=True, count=2):
    scalars = {'item_type': 2, 'instruction': 171, 'argument_count': 3, 'sequence_number': 305419896,
               'capacity': 8, 'count': count, 'attempts': 1, 'allocations': 1, 'frees': 1}
    flags = ('argument_pointer_retained', 'neighbor_retained')
    admission.fields(record, ('schema', 'data_words', 'arguments', 'value_retained', *scalars, *flags), 'key assignment')
    require(record['schema'] == 'oksolc.expression-map-key-assignment.v1', 'wrong key assignment schema')
    require(all(type(record[k]) is int and record[k] == v for k, v in scalars.items()), 'wrong key field or allocation effects')
    require(all(record[k] is True for k in flags), 'key assignment changed its pointer/value/neighbor frame')
    require(type(value_retained) is bool and record['value_retained'] is value_retained, 'wrong value-retention observation')
    for field, expected in (('data_words', [3, 5, 7, 11]), ('arguments', [5, 17, 4294967295])):
        require(type(record[field]) is list and len(record[field]) == len(expected) and
                all(type(v) is int for v in record[field]) and record[field] == expected, 'wrong native key content: ' + field)
    return record


def capture(output, env):
    records, corruptions = [], []
    for mode in ('Debug', 'ReleaseSafe', 'ReleaseFast'):
        binary = output / ('buckets-' + mode); name = 'key-assignment-' + mode
        run(output, name, [binary, 'key'], cwd=ROOT, env=env)
        raw = (output / (name + '.stdout')).read_bytes()
        require(len(raw) <= 4096 and not (output / (name + '.stderr')).read_bytes(), 'unbounded or noisy key assignment capture')
        record = check_observation(json.loads(raw))
        records.append({'mode': mode, 'binarySha256': digest(binary), 'observationSha256': digest(output / (name + '.stdout')), 'observed': record})
        for field, replacement in (('argument_pointer_retained', False), ('value_retained', False), ('neighbor_retained', False),
                                  ('item_type', 1), ('data_words', [3, 5, 7, 0]), ('arguments', [5, 17, 0]),
                                  ('argument_count', 2), ('frees', 0), ('count', True)):
            changed = copy.deepcopy(record); changed[field] = replacement
            try: check_observation(changed)
            except ValueError as error: corruptions.append({'mode': mode, 'field': field, 'rejection': str(error)})
            else: raise ValueError('accepted corrupt key assignment observation')
    return {'captures': records, 'observationControls': corruptions, 'scope': 'key assignment only; hashing/probing/ownership transfer remain open'}
