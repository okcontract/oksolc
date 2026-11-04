"""Audit typed private header initialization and its actual allocation consumer.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import gzip
import hashlib
import re
import check_native_invocation as expressions
from constructor_joint_checks import app
from native_resource_admission_checks import telescope
from native_checkpoint_constructor_checks import numeral
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check
from check_zig_air_memory_proofs import without_imports
from check_word_swap import ROOT
from native_map_write_checks import GRAPH, require
from native_bucket_reservation_checks import BUCKETS
import generate_map_bucket_storage as admission

MODULE = 'Compiler.Extraction.ExpressionMapBucketStorageTests'
HEADER = BUCKETS + 'Header.'
TESTS = GRAPH + 'BucketStorageTests.'
CLAIMS = [BUCKETS + n for n in ('header_layout', 'storage_valid', 'storage_layout')]
CLAIMS += [HEADER + n for n in ('slot_views', 'value_valid', 'array_views', 'checked_value', 'store_total',
                               'read_other', 'writes_cons', 'run_steps', 'run_verified')]
CLAIMS += [GRAPH + n for n in ('Facts.reserve_header', 'reserveHeader_oom')]
CLAIMS += [TESTS + n for n in ('recursive_header', 'uninitialized_header', 'initialized_header', 'captured_header_values',
                              'rejected_capacity_retains_writes', 'zero_capacity_not_admitted')]


def audit(rows):
    indexed = {row['theorem']: row for row in rows}
    dependencies = {
        HEADER + 'store_total': {BUCKETS + 'storage_layout', HEADER + 'slot_views',
                                'Compiler.ZigAir.Memory.store_subobject_total'},
        HEADER + 'checked_value': {HEADER + 'array_views', BUCKETS + 'source_layout', BUCKETS + 'storage_layout',
                                   'Compiler.ZigAir.Memory.access_subregion'},
        HEADER + 'run_verified': {HEADER + n for n in ('store_total', 'read_other', 'run_steps', 'checked_value')},
        GRAPH + 'Facts.reserve_header': {GRAPH + 'Facts.reserve_private_success', HEADER + 'run_verified',
            GRAPH + 'Facts.frame', BUCKETS + 'storage_layout', BUCKETS + 'source_request',
            'Compiler.Extraction.Memory.Arguments.Normalization.Valid.private_memory_frame'},
        GRAPH + 'reserveHeader_oom': {GRAPH + 'PrivateRegion.oom', BUCKETS + 'storage_layout', BUCKETS + 'source_request'},
        TESTS + 'recursive_header': {GRAPH + 'Facts.reserve_header', GRAPH + 'Tests.recursive_after',
                                    GRAPH + 'Facts.operations', GRAPH + 'Facts.constants'},
    }
    for name, needed in dependencies.items():
        require(needed <= set(indexed[name]['dependencies']), 'bucket header lost composition: ' + name)
        if not name.startswith(TESTS):
            require(not any(part.endswith('Tests') for dep in indexed[name]['dependencies'] for part in dep.split('.')),
                    'bucket header core depends on a fixture')
    common = ['σ', 'safety', 'allocator', 'owner', 'capacity', 'data', 'before', 'rows', 'facts']
    binders = {
        HEADER + 'checked_value': ['state', 'id', 'cell', 'capacity', 'slot', 'positive', 'valid', 'found', 'typed', 'writable'],
        HEADER + 'store_total': ['state', 'id', 'cell', 'capacity', 'slot', 'positive', 'valid', 'found', 'typed', 'writable'],
        HEADER + 'run_verified': ['before', 'id', 'cell', 'capacity', 'positive', 'valid', 'found', 'typed', 'writable'],
        GRAPH + 'Facts.reserve_header': common + ['bucketCapacity', 'positive', 'base', 'allocate', 'effects', 'response', 'fits'],
        GRAPH + 'reserveHeader_oom': ['σ', 'before', 'bucketCapacity', 'positive', 'allocate', 'effects', 'valid', 'response'],
        TESTS + 'recursive_header': ['safety', 'depth', 'capacity', 'positive', 'base', 'allocate', 'effects', 'response', 'fits'],
    }
    for name in CLAIMS:
        if name.startswith(TESTS) and name not in binders: binders[name] = []
    for name, expected in binders.items():
        value = indexed[name]['statement']; fields, _, root, scope = telescope(value)
        require(list(fields) == expected, 'bucket header gained an initialization or outcome premise: ' + name)
        if name in (HEADER + 'run_verified', GRAPH + 'Facts.reserve_header'):
            witness = value['nodes'][app(value, root, 'Exists')[-1]]
            require(witness[:2] == ['lambda', 'after'], 'bucket header lost its actual resulting state')
            equation = app(value, app(value, witness[4], 'And')[0], 'Eq')
            operation = HEADER + 'run' if name.startswith(HEADER) else GRAPH + 'reserveHeader'
            wanted = ['capacity', 'id', 'before'] if name.startswith(HEADER) else ['σ', 'bucketCapacity', 'allocate', 'before']
            require([expressions.named(value, a, scope + ['after']) for a in app(value, equation[-2], operation)] == wanted,
                    'bucket header theorem changed the executed inputs')
        if 'response' in fields and not name.startswith(TESTS):
            response, context = fields['response']; call = app(value, response, 'Eq')[-2]
            head, args = expressions.applied(value, call)
            require(head[0] == 'bound' and context[-int(head[1])-1] == 'allocate' and len(args) == 3, 'wrong header allocator')
            source = app(value, app(value, args[0], 'BitVec.toNat')[-1], BUCKETS + 'sourceRequest')
            require(expressions.named(value, source[-1], context) == 'bucketCapacity', 'header lost native request arithmetic')
            numeral(value, args[1], 16)
    return {'checkedDependencies': sorted(dependencies), 'checkedStatements': sorted(binders),
            'headerInitializationDerived': True, 'actualNativeGraphFrameDerived': True,
            'receiverMetadataPublicationVerified': False, 'metadataClearingVerified': False, 'nativeHashMapVerified': False}


def controls(output, env, lean):
    directory = ROOT / 'lean/Compiler/Extraction'
    source = 'import Compiler.Extraction.ExpressionMapBucketReservationTests\nimport Compiler.Extraction.ExpressionMapKeyLayout\n'
    for name in ('ExpressionMapBucketStorageLayout.lean', 'ExpressionMapBucketStorage.lean',
                 'ExpressionMapBucketHeaderReservation.lean', 'ExpressionMapBucketStorageTests.lean'):
        source += without_imports((directory / name).read_text()) + '\n'
    records = [mutation_check(output, 'bucket-header-unchanged', source, True, env, lean)]
    for name, before, after in (
        ('header-offset', '(16, .scalar (.int false 32))]', '(12, .scalar (.int false 32))]'),
        ('component-offset', '(keysOffset capacity, .object', '(keysOffset capacity + 16, .object'),
        ('skip-values', 'writes capacity id [.values, .keys, .capacity] state', 'writes capacity id [.keys, .capacity] state'),
        ('key-pointer', '| .keys => arrayPointer state keyType capacity.toNat ⟨id, (sourceKeys capacity).toNat⟩',
         '| .keys => arrayPointer state keyType capacity.toNat ⟨id, (sourceValues capacity).toNat⟩'),
        ('capacity', '.scalar (.int false 32 capacity.toNat)', '.scalar (.int false 32 (capacity + 1).toNat)'),
        ('discard-memory', '(initialized.map (fun _ => some address), { reserved with memory := { reserved.memory with memory } })',
         '(initialized.map (fun _ => some address), { reserved with memory := { reserved.memory with memory := reserved.memory.memory } })'),
        ('discard-prefix', '| .error fault => (.error fault, state)', '| .error fault => (.error fault, { state with heap := [] })'),
    ):
        require(source.count(before) == 1, 'ambiguous header control: ' + name)
        changed = source.replace(before, after, 1)
        if name == 'capacity':
            # Keep the wrong source word well typed; the captured read must reject it.
            changed = changed.replace('| capacity => exact WordArray.number_valid capacity',
                                      '| capacity => exact WordArray.number_valid (capacity + 1)', 1)
        records.append(mutation_check(output, 'bucket-header-' + name, changed, False, env, lean))
    return checked_controls(output, records)


def capture(output, mode, raw, lib):
    require(admission.generate(raw, lib) == admission.OUTPUT.read_bytes(), 'private header storage admission changed')
    nodes = admission.metadata(raw); _, header = admission.named(nodes, admission.HEADER)
    members = re.findall(r'![0-9]+', nodes[header['elements']])
    changes = [(members[2], 'offset: 128', 'offset: 96')]
    pointer = admission.attributes(nodes, members[0], 'DIDerivedType')['baseType']
    changes.append((pointer, '"[*]u32"', '"[*]const u32"'))
    controls = []
    for index, (key, before, after) in enumerate(changes):
        old = (key + ' = ' + nodes[key]).encode(); require(raw.count(old) == 1 and before in nodes[key], 'ambiguous metadata control')
        changed = raw.replace(old, old.replace(before.encode(), after.encode()), 1)
        path = output / ('header-metadata-' + mode + '-' + str(index) + '.ll.gz')
        with gzip.open(path, 'wb') as stream: stream.write(changed)
        try: admission.header(changed, lib)
        except ValueError as error:
            controls.append({'field': key, 'rejection': str(error), 'inputSha256': hashlib.sha256(changed).hexdigest()})
        else: raise ValueError('accepted corrupted private header metadata')
    identity, packed = admission.named(nodes, admission.METADATA)
    member = re.findall(r'![0-9]+', nodes[packed['elements']])[0]
    backing = admission.attributes(nodes, member, 'DIDerivedType')['baseType']
    packed_controls = []
    for index, (key, before, after) in enumerate((
        (identity, 'size: 8, align: 8', 'size: 16, align: 8'),
        (identity, 'line: ' + packed['line'], 'line: 1'),
        (packed['elements'], nodes[packed['elements']], '!{}'),
        (member, 'name: "bits"', 'name: "fingerprint"'),
        (member, 'scope: ' + identity + ',', 'scope: ' + packed['scope'] + ','),
        (backing, 'DW_ATE_unsigned', 'DW_ATE_signed'),
    )):
        old = (key + ' = ' + nodes[key]).encode()
        require(raw.count(old) == 1 and nodes[key].count(before) == 1, 'ambiguous packed metadata control')
        changed = raw.replace(old, old.replace(before.encode(), after.encode(), 1), 1)
        with gzip.open(output / ('packed-metadata-' + mode + '-' + str(index) + '.ll.gz'), 'wb') as stream:
            stream.write(changed)
        try: admission.packed_metadata(changed, lib)
        except ValueError as error:
            packed_controls.append({'field': key, 'rejection': str(error), 'inputSha256': hashlib.sha256(changed).hexdigest()})
        else: raise ValueError('accepted corrupted packed metadata')
    return {'llvmIrSha256': hashlib.sha256(raw).hexdigest(), 'header': admission.header(raw, lib),
            'metadataControls': controls, 'packedMetadata': admission.packed_metadata(raw, lib),
            'packedControls': packed_controls}
