"""Check the complete defined native key/ID assignment tail.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import json
from pathlib import Path
import native_map_key_checks as keys
from native_map_key_checks import GRAPH, BUCKETS, KEY, require, app, path, telescope, expressions
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check
from check_zig_air_memory_proofs import without_imports
from check_word_swap import ROOT
from build_toolchain import digest, run

MODULE = 'Compiler.Extraction.ExpressionMapEntryTests'
VALUES = BUCKETS + 'Values.'
ENTRY = BUCKETS + 'Entry.'
TESTS = GRAPH + 'MapEntryTests.'
MEMORY = 'Compiler.ZigAir.Memory.'
CLAIMS = [MEMORY + n for n in ('access_narrow', 'elementPointer_of_access')] + [KEY + 'read_eq']
CLAIMS += [VALUES + n for n in ('views', 'access_entry', 'entry_pointer', 'store_total', 'store_frame',
    'header_frame', 'key_frame', 'value_frame', 'read_eq')]
CLAIMS += [ENTRY + n for n in ('assign_steps', 'assign_verified', 'Completed.native_frame', 'Completed.headers',
    'Completed.outside', 'Completed.other_values', 'Completed.metadata_frame', 'Completed.stored', 'selection_rejected', 'value_rejected')]
CLAIMS += [GRAPH + n for n in ('assignEntry_prefix', 'Facts.assign_entry')]
CLAIMS += [TESTS + n for n in ('from_initialized_owner', 'completed', 'assigned', 'readback', 'native_value_readback',
    'const_slice_readback', 'neighbor_values', 'metadata_retained', 'header_retained', 'selection_failure_before_writes',
    'partial_prefix', 'partial_key_readback', 'partial_value_retained', 'readonly_keys_rejected', 'out_of_bounds_rejected')]


def source_binding(lib, source=None, native=None):
    binding = keys.source_binding(lib, source=source)
    native = (Path(lib) / 'std/hash_map.zig').read_bytes() if native is None else native
    keys.admission.source_binding(lib, source=source, native=native)
    for name, kind in (('keys', 'K'), ('values', 'V')):
        keys.admission.storage.function(native, 'fn ' + name + '(self: Self) [*]' + kind).expect(
            '{ return self.header().' + name + '; }')
    return {**binding, 'scope': 'defined key/ID assignment tail after getOrPut and old-argument release',
            'entryAssignmentSourceAdmitted': True, 'nativeHashMapVerified': False, 'sourceAdapterFormallyVerified': False}


def source_controls(lib):
    source = keys.admission.storage.SOURCE.read_bytes(); native = (Path(lib) / 'std/hash_map.zig').read_bytes()
    records = []
    for before, after in ((b'entry.value_ptr.* = id;', b'entry.value_ptr.* = undefined;'),
                          (b'entry.value_ptr.* = id;', b'entry.value_ptr.* = id + 1;')):
        require(source.count(before) == 1, 'ambiguous entry source mutation')
        try: source_binding(lib, source.replace(before, after, 1))
        except (ValueError, keys.admission.storage.Unsupported) as error:
            records.append({'source': 'publishOwned', 'mutation': after.decode(), 'rejection': str(error)})
        else: raise ValueError('accepted changed entry assignment')
    for name, other in (('keys', 'values'), ('values', 'keys')):
        before = ('return self.header().' + name + ';').encode()
        require(native.count(before) == 1, 'ambiguous entry component selector')
        changed = native.replace(before, ('return self.header().' + other + ';').encode(), 1)
        try: source_binding(lib, native=changed)
        except (ValueError, keys.admission.storage.Unsupported) as error:
            records.append({'source': 'hash_map.zig', 'mutation': name, 'rejection': str(error)})
        else: raise ValueError('accepted rebound entry component')
    return records


def audit(rows):
    indexed = {row['theorem']: row for row in rows}
    dependencies = {
        KEY + 'entry_pointer': {MEMORY + 'elementPointer_of_access', KEY + 'access_entry'},
        KEY + 'read_eq': {KEY + 'entry_pointer', KEY + 'select_verified'},
        VALUES + 'entry_pointer': {MEMORY + 'elementPointer_of_access', VALUES + 'access_entry'},
        VALUES + 'store_total': {VALUES + 'access_entry', VALUES + 'views', MEMORY + 'store_subobject_total'},
        ENTRY + 'assign_verified': {ENTRY + 'write_pointers_verified', ENTRY + 'assign_steps'},
        ENTRY + 'Completed.native_frame': {MEMORY + 'store_preserves_valid', MEMORY + 'store_retains_shape'},
        ENTRY + 'Completed.stored': {KEY + 'read_eq', VALUES + 'read_eq', VALUES + 'key_frame', ENTRY + 'Completed.headers'},
        ENTRY + 'Completed.metadata_frame': {ENTRY + 'Completed.metadata_load'},
        ENTRY + 'Completed.other_values': {VALUES + 'value_frame'},
        GRAPH + 'Facts.assign_entry': {ENTRY + 'assign_verified', ENTRY + 'Completed.native_frame', ENTRY + 'Completed.stored',
            ENTRY + 'Completed.metadata_frame', GRAPH + 'Facts.private_map_frame', GRAPH + 'assignEntry_prefix'},
        TESTS + 'from_initialized_owner': {keys.capacity.TESTS + 'from_initialized_owner', GRAPH + 'Facts.assign_entry'},
        TESTS + 'selection_failure_before_writes': {ENTRY + 'selection_rejected'},
        TESTS + 'partial_prefix': {ENTRY + 'value_rejected'},
        TESTS + 'neighbor_values': {ENTRY + 'Completed.other_values'},
    }
    for name, required in dependencies.items():
        require(required <= set(indexed[name]['dependencies']), 'entry assignment lost composition: ' + name)
    for name in CLAIMS:
        if not name.startswith(TESTS):
            require(not any(part.endswith('Tests') for dep in indexed[name]['dependencies'] for part in dep.split('.')),
                    'entry core depends on a fixture')
    binders = {
        VALUES + 'store_total': ['state', 'capacity', 'bucket', 'index', 'cell', 'id', 'bounded', 'inside', 'valid', 'found', 'typed', 'writable'],
        ENTRY + 'assign_verified': ['capacity', 'bucket', 'index', 'key', 'arguments', 'id', 'before', 'cell', 'inside', 'valid', 'found', 'typed', 'writable', 'length', 'headers'],
        GRAPH + 'Facts.assign_entry': ['σ', 'safety', 'allocator', 'owner', 'capacity', 'data', 'before', 'rows', 'facts',
            'bucketCapacity', 'bucket', 'index', 'cell', 'inside', 'found', 'typed', 'writable', 'key', 'arguments', 'id', 'length', 'headers'],
        GRAPH + 'assignEntry_prefix': ['σ', 'bucketCapacity', 'bucket', 'index', 'key', 'arguments', 'id', 'before', 'result', 'memory', 'ran'],
        TESTS + 'from_initialized_owner': ['safety', 'meaning', 'index', 'key', 'arguments', 'id', 'length'],
    }
    for name, wanted in binders.items():
        value = indexed[name]['statement']; fields, _, root, scope = telescope(value)
        require(list(fields) == wanted, 'entry assignment gained an outcome or initialized-entry premise: ' + name)
        if name == GRAPH + 'assignEntry_prefix':
            keys.audit_prefix(value, root, scope, GRAPH + 'assignEntry',
                              ['σ', 'bucketCapacity', 'bucket', 'index', 'key', 'arguments', 'id', 'before'])
        if name in (ENTRY + 'assign_verified', GRAPH + 'Facts.assign_entry'):
            names = ['keyed', 'after'] if name.startswith(ENTRY) else ['after']
            for variable in names:
                witness = value['nodes'][app(value, root, 'Exists')[-1]]
                require(witness[:2] == ['lambda', variable], 'entry assignment lost its actual state witness')
                root = witness[4]; scope = scope + [variable]
            equation, rest = app(value, root, 'And'); equation = app(value, equation, 'Eq')
            args = ['capacity', 'bucket', 'index', 'key', 'arguments', 'id', 'before'] if name.startswith(ENTRY) else [
                'σ', 'bucketCapacity', 'bucket', 'index', 'key', 'arguments', 'id', 'before']
            function = ENTRY + 'assign' if name.startswith(ENTRY) else GRAPH + 'assignEntry'
            require([expressions.named(value, a, scope) for a in app(value, equation[-2], function)] == args,
                    'entry assignment changed its original inputs')
            result = app(value, equation[-1], 'Prod.mk')
            require(expressions.named(value, result[-1], scope) == 'after', 'entry assignment discarded its final store')
            if name.startswith(ENTRY):
                completed = app(value, rest, ENTRY + 'Completed')
                require([expressions.named(value, a, scope) for a in completed] ==
                        ['capacity', 'bucket', 'index', 'key', 'arguments', 'id', 'before', 'keyed', 'after'], 'entry completion rebound a store state or input')
            else:
                facts, rest = app(value, rest, 'And')
                require(expressions.named(value, app(value, facts, GRAPH + 'Facts')[-2], scope) == 'after', 'entry assignment framed another world')
                representation, _ = app(value, rest, 'And'); stored = app(value, representation, ENTRY + 'Stored')
                require([expressions.named(value, a, scope) for a in stored[:-1]] ==
                        ['bucketCapacity', 'bucket', 'index', 'key', 'arguments', 'id'], 'entry readback changed its key, ID or location')
                path(value, stored[-1], scope, ('Compiler.Extraction.Memory.Arguments.Normalization.Session.memory',
                    'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.World.memory'), 'after')
    return {'checkedDependencies': sorted(dependencies), 'checkedStatements': sorted(binders),
            'pointerArithmeticShared': True, 'completeAssignmentTailDerived': True, 'nativeGraphFrameReused': True,
            'nativeHashMapVerified': False, 'ownershipTransferVerified': False}


def controls(output, env, lean):
    directory = ROOT / 'lean/Compiler/Extraction'
    source = 'import Compiler.Extraction.ExpressionMapKeyTests\n'
    for name in ('ExpressionMapValue.lean', 'ExpressionMapEntry.lean', 'ExpressionMapEntryMemory.lean'):
        source += without_imports((directory / name).read_text()) + '\n'
    tests = without_imports((directory / 'ExpressionMapEntryTests.lean').read_text())
    require(tests.count('open Compiler.ZigAir.Memory\n') == 1, 'ambiguous entry concrete fixtures')
    core = source + tests.split('open Compiler.ZigAir.Memory\n')[0] + '\nend ' + TESTS.removesuffix('.') + '\n'
    records = [mutation_check(output, 'map-entry-unchanged', source + tests, True, env, lean)]
    for name, before, after in (
        ('value-component', '⟨bucket, valuesOffset capacity + index * 4⟩', '⟨bucket, keysOffset capacity + index * 4⟩'),
        ('value-lifetime', '⟨bucket, valuesOffset capacity + index * 4⟩', '⟨bucket + 1, valuesOffset capacity + index * 4⟩'),
        ('values-header', 'let values ← load state (Header.Slot.values.pointer capacity bucket)', 'let values ← load state (Header.Slot.keys.pointer capacity bucket)'),
        ('skip-key', 'match KeyFields.writes keyPointer key arguments KeyFields.order before with', 'match (Except.ok (), before) with'),
        ('wrong-id', '| (.ok (), keyed) => match store keyed valuePointer (number id) with', '| (.ok (), keyed) => match store keyed valuePointer (number (id + 1)) with'),
        ('discard-key', '| (.ok (), keyed) => match store keyed valuePointer (number id) with', '| (.ok (), keyed) => match store before valuePointer (number id) with'),
        ('skip-value', '| (.ok (), keyed) => match store keyed valuePointer (number id) with', '| (.ok (), keyed) => match (Except.ok keyed : Except Fault State) with'),
        ('discard-result', '| .ok after => (.ok (), after)', '| .ok _after => (.ok (), keyed)'),
        ('discard-prefix', '| .error fault => (.error fault, keyed)\n    | .ok after', '| .error fault => (.error fault, before)\n    | .ok after'),
        ('discard-world', '\n  (result, { before with memory := { before.memory with memory } })\n', '\n  (result, before)\n'),
    ):
        require(core.count(before) == 1, 'ambiguous entry control: ' + name)
        records.append(mutation_check(output, 'map-entry-' + name, core.replace(before, after, 1), False, env, lean))
    return checked_controls(output, records)


def check_observation(record):
    keys.admission.fields(record, ('schema', 'key', 'id'), 'entry assignment')
    require(record['schema'] == 'oksolc.expression-map-entry-assignment.v1', 'wrong entry assignment schema')
    require(type(record['id']) is int and record['id'] == 4275878552, 'wrong native assigned ID')
    keys.check_observation(record['key'], value_retained=False)
    return record


def capture(output, env):
    records, corruptions = [], []
    for mode in ('Debug', 'ReleaseSafe', 'ReleaseFast'):
        binary = output / ('buckets-' + mode); name = 'entry-assignment-' + mode
        run(output, name, [binary, 'entry'], cwd=ROOT, env=env)
        raw = (output / (name + '.stdout')).read_bytes()
        require(len(raw) <= 4096 and not (output / (name + '.stderr')).read_bytes(), 'unbounded or noisy entry capture')
        record = check_observation(json.loads(raw))
        records.append({'mode': mode, 'binarySha256': digest(binary), 'observationSha256': digest(output / (name + '.stdout')), 'observed': record})
        for field, replacement in (('id', 37), ('id', True), ('value_retained', True), ('argument_pointer_retained', False),
                                  ('neighbor_retained', False), ('data_words', [3, 5, 7, 0]), ('arguments', [5, 17, 0]),
                                  ('sequence_number', 0), ('argument_count', 2), ('count', 3), ('allocations', 2), ('frees', 0)):
            changed = copy.deepcopy(record)
            if field == 'id': changed[field] = replacement
            else: changed['key'][field] = replacement
            try: check_observation(changed)
            except ValueError as error: corruptions.append({'mode': mode, 'field': field, 'rejection': str(error)})
            else: raise ValueError('accepted corrupt entry assignment observation')
    return {'captures': records, 'observationControls': corruptions, 'scope': 'defined assignment tail only; probing and ownership transfer remain open'}
