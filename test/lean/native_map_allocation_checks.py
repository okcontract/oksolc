"""Bind complete bucket allocation to its actual standalone map receiver.
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
from native_bucket_reservation_checks import BUCKETS
import generate_map_bucket_layout as admission

MODULE = 'Compiler.Extraction.ExpressionMapAllocationTests'
MAP = 'Compiler.Extraction.ExpressionMap.'
INIT = MAP + 'Initialization.'
RECEIVER = MAP + 'Receiver.'
TESTS = GRAPH + 'MapAllocationTests.'
CLAIMS = [INIT + n for n in ('Placement.layout_checked', 'slot_views_at', 'store_value_at_total')]
CLAIMS += [GRAPH + 'Facts.reserve_header_framed']
CLAIMS += [RECEIVER + n for n in ('value_valid', 'metadata_view', 'checked_value', 'root_pointer', 'publish_verified')]
CLAIMS += [GRAPH + n for n in ('Facts.local_map_frame', 'Facts.allocate_buckets', 'allocateBuckets_rejected', 'allocateBuckets_oom')]
CLAIMS += [TESTS + n for n in ('seed_valid', 'seed_frame', 'seed_facts', 'from_initialized_owner', 'captured_publication',
                              'receiver_fields_retained', 'oom_retains_receiver', 'readonly_retains_header')]


def audit(rows):
    indexed = {row['theorem']: row for row in rows}
    dependencies = {
        INIT + 'store_value_total': {INIT + 'store_value_at_total'},
        INIT + 'store_value_at_total': {INIT + 'slot_views_at', 'Compiler.ZigAir.Memory.store_subobject_total'},
        GRAPH + 'Facts.reserve_header': {GRAPH + 'Facts.reserve_header_framed'},
        GRAPH + 'Facts.reserve_header_framed': {GRAPH + 'Facts.reserve_private_success', BUCKETS + 'Header.run_verified'},
        RECEIVER + 'checked_value': {RECEIVER + 'metadata_view', BUCKETS + 'storage_layout', 'Compiler.ZigAir.Memory.access_subregion'},
        RECEIVER + 'publish_verified': {INIT + 'store_value_at_total', RECEIVER + 'checked_value', RECEIVER + 'root_pointer'},
        GRAPH + 'Facts.local_map_frame': {GRAPH + 'Facts.frame', 'Compiler.ZigAir.Memory.Heap.lookup_ne_of_type_ne'},
        GRAPH + 'Facts.allocate_buckets': {GRAPH + 'Facts.reserve_header_framed', RECEIVER + 'publish_verified', GRAPH + 'Facts.local_map_frame'},
        GRAPH + 'allocateBuckets_oom': {GRAPH + 'reserveHeader_oom'},
        TESTS + 'from_initialized_owner': {GRAPH + 'Facts.allocate_buckets', TESTS + 'seed_facts'},
        TESTS + 'readonly_retains_header': {GRAPH + 'allocateBuckets_rejected'},
    }
    for name, needed in dependencies.items():
        require(needed <= set(indexed[name]['dependencies']), 'map allocation lost composition: ' + name)
        if not name.startswith(TESTS):
            require(not any(part.endswith('Tests') for dep in indexed[name]['dependencies'] for part in dep.split('.')),
                    'map allocation core depends on a fixture')
    common = ['σ', 'safety', 'allocator', 'owner', 'capacity', 'data', 'before', 'rows', 'facts']
    binders = {
        RECEIVER + 'checked_value': ['state', 'bucket', 'cell', 'capacity', 'positive', 'valid', 'found', 'typed', 'writable'],
        RECEIVER + 'publish_verified': ['safety', 'before', 'receiver', 'bucket', 'localCell', 'bucketCell', 'capacity', 'positive',
            'valid', 'localFound', 'localType', 'localWritable', 'bucketFound', 'bucketType', 'bucketWritable'],
        GRAPH + 'Facts.allocate_buckets': common + ['receiver', 'localCell', 'found', 'typed', 'writable', 'bucketCapacity',
            'positive', 'base', 'allocate', 'effects', 'response', 'fits'],
        GRAPH + 'allocateBuckets_oom': ['σ', 'safety', 'before', 'receiver', 'bucketCapacity', 'positive', 'allocate', 'effects', 'valid', 'response'],
        TESTS + 'from_initialized_owner': ['safety', 'meaning'],
        GRAPH + 'allocateBuckets_rejected': ['σ', 'safety', 'capacity', 'receiver', 'allocate', 'before', 'headed', 'bucket', 'fault', 'reserved', 'rejected'],
    }
    for name in CLAIMS:
        if name.startswith(TESTS) and name not in binders:
            binders[name] = {'seed_valid': ['safety', 'writable'], 'seed_frame': ['safety', 'writable', 'id', 'apart'],
                            'seed_facts': ['safety', 'meaning']}.get(name.removeprefix(TESTS), ['safety'])
    for name, expected in binders.items():
        value = indexed[name]['statement']; fields, _, root, scope = telescope(value)
        require(list(fields) == expected, 'map allocation gained a success/graph/publication premise: ' + name)
        if name == GRAPH + 'Facts.allocate_buckets':
            witness = value['nodes'][app(value, root, 'Exists')[-1]]
            require(witness[:2] == ['lambda', 'after'], 'allocation lost actual resulting state')
            equation = app(value, app(value, witness[4], 'And')[0], 'Eq')
            require([expressions.named(value, a, scope + ['after']) for a in app(value, equation[-2], GRAPH + 'allocateBuckets')] ==
                    ['σ', 'safety', 'bucketCapacity', 'receiver', 'allocate', 'before'], 'allocation changed native inputs or receiver')
        if name == GRAPH + 'allocateBuckets_rejected':
            equation = app(value, root, 'Eq')
            require([expressions.named(value, a, scope) for a in app(value, equation[-2], GRAPH + 'allocateBuckets')] ==
                    ['σ', 'safety', 'capacity', 'receiver', 'allocate', 'before'], 'rejection changed the executed inputs')
            result = app(value, equation[-1], 'Prod.mk')
            require(expressions.named(value, result[-1], scope) == 'headed', 'rejection discarded the reached prefix')
            require(expressions.named(value, app(value, result[-2], 'Except.error')[-1], scope) == 'fault',
                    'rejection changed its fault')
        if 'response' in fields:
            response, context = fields['response']; call = app(value, response, 'Eq')[-2]
            head, args = expressions.applied(value, call)
            require(head[0] == 'bound' and context[-int(head[1])-1] == 'allocate' and len(args) == 3, 'wrong allocation host')
            source = app(value, app(value, args[0], 'BitVec.toNat')[-1], BUCKETS + 'sourceRequest')
            require(expressions.named(value, source[-1], context) == 'bucketCapacity', 'allocation lost native request arithmetic')
            numeral(value, args[1], 16)
    return {'checkedDependencies': sorted(dependencies), 'checkedStatements': sorted(binders),
            'receiverPublicationDerived': True, 'nativeBucketAllocationDerived': True,
            'localDeclarationDerived': False, 'metadataClearingVerified': False, 'nativeHashMapVerified': False}


def controls(output, env, lean):
    directory = ROOT / 'lean/Compiler/Extraction'
    source = 'import Compiler.Extraction.ExpressionMapBucketStorageTests\n'
    for name in ('ExpressionMapReceiver.lean', 'ExpressionMapAllocation.lean'):
        source += without_imports((directory / name).read_text()) + '\n'
    # Mutations target the generic owning proofs. Keep a matching core positive
    # and independently elaborate the complete concrete regression module;
    # false heap dumps must not replace a semantic proof rejection.
    records = [mutation_check(output, 'map-allocation-core-unchanged', source, True, env, lean),
               mutation_check(output, 'map-allocation-fixtures-unchanged', source +
                   without_imports((directory / 'ExpressionMapAllocationTests.lean').read_text()), True, env, lean)]
    for name, before, after in (
        ('metadata-offset', 'capacity.toNat ⟨bucket, 24⟩', 'capacity.toNat ⟨bucket, 0⟩'),
        ('receiver-field', 'fieldPointer state (.pointer (.pointer writable false (allocationType safety)) receiver) metadataOffset',
         'fieldPointer state (.pointer (.pointer writable false (allocationType safety)) receiver) (sizeOffset safety)'),
        ('null-publication', '.ok (.optionalObject metadataPointerType ⟨8, 8⟩ (some (.leaf pointer)))',
         '.ok (.optionalObject metadataPointerType ⟨8, 8⟩ none)'),
        ('wrong-receiver', 'match ExpressionMap.Receiver.publish safety capacity ⟨receiver, 0⟩ bucket.allocation headed.memory.memory with',
         'match ExpressionMap.Receiver.publish safety capacity ⟨receiver + 1, 0⟩ bucket.allocation headed.memory.memory with'),
        ('discard-publication', '| .ok memory => (.ok (some bucket), { headed with memory := { headed.memory with memory } })',
         '| .ok memory => (.ok (some bucket), headed)'),
        ('discard-prefix', '| .error fault => (.error fault, headed)', '| .error fault => (.error fault, before)'),
    ):
        require(source.count(before) == 1, 'ambiguous allocation control: ' + name)
        records.append(mutation_check(output, 'map-allocation-' + name, source.replace(before, after, 1), False, env, lean))
    return checked_controls(output, records)


def source_controls(lib):
    native = (lib / 'std/hash_map.zig').read_bytes()
    before = b'self.metadata = @ptrCast(@alignCast(metadata));'
    require(native.count(before) == 1, 'ambiguous receiver source assignment')
    changed = native.replace(before, b'self.metadata = null;', 1)
    try: admission.source_binding(lib, native=changed)
    except (ValueError, admission.storage.Unsupported) as error:
        return [{'mutation': before.decode(), 'rejection': str(error)}]
    raise ValueError('accepted missing native receiver publication')
