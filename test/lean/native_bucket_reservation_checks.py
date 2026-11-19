"""Check source-bound bucket requests and their native graph reservation frame.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import json
import sys
import check_native_invocation as expressions
from constructor_joint_checks import app
from native_resource_admission_checks import telescope
from native_checkpoint_constructor_checks import numeral
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check
from check_zig_air_memory_proofs import without_imports
from check_word_swap import ROOT
from build_toolchain import digest, run
from native_map_write_checks import GRAPH, require
import generate_map_bucket_layout as admission

MODULE = 'Compiler.Extraction.ExpressionMapBucketReservationTests'
BUCKETS = 'Compiler.Extraction.ExpressionMap.Buckets.'
TESTS = GRAPH + 'BucketReservationTests.'
CLAIMS = [BUCKETS + n for n in ('layout', 'geometry', 'sourceAlign_toNat', 'source_layout', 'source_request')]
CLAIMS += [GRAPH + n for n in ('Facts.reserve_buckets', 'Facts.reserve_buckets_success', 'reserveBuckets_oom')]
CLAIMS += [TESTS + n for n in ('recursive_reservation', 'recursive_fields', 'captured_requests')]


def audit(rows):
    indexed = {row['theorem']: row for row in rows}
    dependencies = {
        BUCKETS + 'source_layout': {BUCKETS + 'sourceAlign_toNat'},
        BUCKETS + 'source_request': {BUCKETS + 'source_layout'},
        GRAPH + 'Facts.reserve_buckets': {GRAPH + 'Facts.reserve_private'},
        GRAPH + 'Facts.reserve_buckets_success': {GRAPH + 'Facts.reserve_private_success', BUCKETS + 'source_request', BUCKETS + 'geometry'},
        GRAPH + 'reserveBuckets_oom': {GRAPH + 'PrivateRegion.oom', BUCKETS + 'source_request', BUCKETS + 'geometry'},
        TESTS + 'recursive_reservation': {GRAPH + 'PrivateRegionTests.recursive_reservation'},
        TESTS + 'recursive_fields': {GRAPH + 'PrivateRegionTests.recursive_fields'},
    }
    for name, needed in dependencies.items():
        require(needed <= set(indexed[name]['dependencies']), 'bucket reservation lost composition: ' + name)
    common = ['σ', 'safety', 'allocator', 'owner', 'capacity', 'data', 'before', 'rows', 'facts']
    expected = {
        BUCKETS + 'source_layout': ['capacity'], BUCKETS + 'source_request': ['capacity'],
        GRAPH + 'Facts.reserve_buckets': common + ['bucketCapacity', 'allocate'],
        GRAPH + 'Facts.reserve_buckets_success': common + ['bucketCapacity', 'base', 'allocate', 'effects', 'response', 'fits'],
        GRAPH + 'reserveBuckets_oom': ['σ', 'before', 'bucketCapacity', 'allocate', 'effects', 'valid', 'response'],
        TESTS + 'recursive_reservation': ['safety', 'depth', 'capacity', 'allocate'],
        TESTS + 'recursive_fields': ['safety', 'depth', 'capacity', 'allocate', 'slot', 'value', 'typed', 'valid', 'active'],
        TESTS + 'captured_requests': [],
    }
    for name, binders in expected.items():
        value = indexed[name]['statement']
        fields, _, root, scope = telescope(value)
        require(list(fields) == binders, 'bucket reservation added an outcome/final-state premise: ' + name)
        if name in (BUCKETS + 'source_request', BUCKETS + 'source_layout'):
            field, context = fields['capacity']
            numeral(value, app(value, field, 'BitVec')[0], 32)
            pairs = [(root, 'sourceRequest', 'bytes')]
            if name == BUCKETS + 'source_layout':
                keys, rest = app(value, root, 'And')
                values, extent = app(value, rest, 'And')
                pairs = [(keys, 'sourceKeys', 'keysOffset'), (values, 'sourceValues', 'valuesOffset'),
                         (extent, 'sourceRequest', 'bytes')]
            for term, native, logical in pairs:
                equality = app(value, term, 'Eq')
                source = app(value, app(value, equality[-2], 'BitVec.toNat')[-1], BUCKETS + native)
                target = app(value, app(value, equality[-1], BUCKETS + logical)[-1], 'BitVec.toNat')
                require(expressions.named(value, source[-1], scope) == expressions.named(value, target[-1], scope) == 'capacity',
                        'source layout lost its full-width capacity binding')
        if 'response' in fields:
            term, context = fields['response']
            called = app(value, term, 'Eq')[-2]
            head, args = expressions.applied(value, called)
            require(head[0] == 'bound' and context[-int(head[1]) - 1] == 'allocate' and len(args) == 3,
                    'bucket response changed its allocator')
            source = app(value, app(value, args[0], 'BitVec.toNat')[-1], BUCKETS + 'sourceRequest')
            require(expressions.named(value, source[-1], context) == 'bucketCapacity', 'bucket response lost native request arithmetic')
            numeral(value, args[1], 16)
        if name == GRAPH + 'Facts.reserve_buckets':
            args = app(value, root, GRAPH + 'Facts')
            require([expressions.named(value, a, scope) for a in args[:6] + args[7:]] ==
                    ['σ', 'safety', 'allocator', 'owner', 'data', 'capacity', 'rows'], 'bucket reservation changed the graph')
            result = app(value, args[6], 'Prod.snd')[-1]
            require([expressions.named(value, a, scope) for a in app(value, result, GRAPH + 'reserveBuckets')] ==
                    ['σ', 'bucketCapacity', 'allocate', 'before'], 'bucket reservation discarded the actual result')
    return {'checkedDependencies': sorted(dependencies), 'checkedStatements': sorted(expected),
            'nativeWordRequestEqualsRegionExtent': True, 'nativeGraphFrameDerived': True,
            'bucketInitializationVerified': False, 'nativeHashMapVerified': False}


def controls(output, env, lean):
    directory = ROOT / 'lean/Compiler/Extraction'
    source = 'import Compiler.Extraction.InternerNativeGraphPrivateRegionTests\n'
    for name in ('ExpressionMapBucketLayout.lean', 'ExpressionMapBucketReservation.lean', 'ExpressionMapBucketReservationTests.lean'):
        source += without_imports((directory / name).read_text()) + '\n'
    records = [mutation_check(output, 'bucket-request-unchanged', source, True, env, lean)]
    for name, before, after in (
        ('header', 'def headerBytes : Nat := 24', 'def headerBytes : Nat := 16'),
        ('keys', 'def keyBytes : Nat := 64', 'def keyBytes : Nat := 32'),
        ('values', 'def valueBytes : Nat := 4', 'def valueBytes : Nat := 8'),
        ('alignment', 'def allocationAlignment : Nat := 16', 'def allocationAlignment : Nat := 8'),
        ('rounding', '(value + mask) &&& ~~~mask', 'value &&& ~~~mask'),
        ('native-request', 'let values := sourceAlign 2 (keys + count * 64)', 'let values := sourceAlign 2 (keys + count * 32)'),
    ):
        require(source.count(before) == 1, 'ambiguous bucket request mutation: ' + name)
        records.append(mutation_check(output, 'bucket-request-' + name, source.replace(before, after, 1), False, env, lean))
    return checked_controls(output, records)


def capture(output, zig, lib, env, *, header=False):
    run(output, 'bucket-admission-tests', [sys.executable, 'test/lean/test_map_bucket_layout.py'], cwd=ROOT, env=env)
    if header:
        import native_bucket_storage_checks as storage
        run(output, 'bucket-header-tests', [sys.executable, 'test/lean/test_map_bucket_storage.py'], cwd=ROOT, env=env)
    binding = admission.source_binding(lib)
    source_controls = []
    native = (lib / 'std/hash_map.zig').read_bytes()
    for before, after in ((b'const meta_size = @sizeOf(Header) + new_cap * @sizeOf(Metadata);', b'const meta_size = new_cap;'),
                          (b'const keys_end = keys_start + new_cap * @sizeOf(K);', b'const keys_end = keys_start;'),
                          (b'const vals_end = vals_start + new_cap * @sizeOf(V);', b'const vals_end = vals_start;'),
                          (b'const total_size = max_align.forward(vals_end);', b'const total_size = vals_end;'),
                          (b'const slice = try allocator.alignedAlloc(u8, max_align, total_size);', b'const slice = try allocator.alloc(u8, total_size);')):
        require(native.count(before) == 1, 'ambiguous native allocation control')
        try: admission.source_binding(lib, native=native.replace(before, after, 1))
        except (ValueError, admission.storage.Unsupported) as error:
            source_controls.append({'mutation': before.decode(), 'rejection': str(error)})
        else: raise ValueError('accepted changed native allocation recipe')
    records, corruptions = [], []
    for mode in ('Debug', 'ReleaseSafe', 'ReleaseFast'):
        binary = output / ('buckets-' + mode)
        llvm = output / ('buckets-' + mode + '.ll')
        run(output, 'bucket-build-' + mode, [zig, 'build-exe', '-j4', '--zig-lib-dir', lib, '-fllvm', '-O', mode,
            '--dep', 'compiler', '-Mroot=' + str(ROOT / 'test/lean/expression_map_buckets.zig'), '-O', mode,
            '-Mcompiler=' + str(ROOT / 'src/modules.zig'), '--cache-dir', output / 'zig-cache',
            '--global-cache-dir', output / 'global-cache', '-femit-bin=' + str(binary)] +
            (['-femit-llvm-ir=' + str(llvm)] if header else []), cwd=ROOT, env=env)
        run(output, 'bucket-run-' + mode, [binary], cwd=ROOT, env=env)
        raw = (output / ('bucket-run-' + mode + '.stdout')).read_bytes()
        observation = output / ('bucket-observation-' + mode + '.json'); observation.write_bytes(raw)
        require(len(raw) <= 32768, 'bucket observation exceeds admission bound')
        profile = json.loads(raw)
        require(profile['target']['mode'] == mode, 'bucket observation has wrong build mode')
        require(admission.generate(profile, lib) == admission.OUTPUT.read_bytes(), 'bucket layout admission changed')
        require(admission.key_layout(profile, lib) == admission.KEY_OUTPUT.read_bytes(), 'key field admission changed')
        require(not (output / ('bucket-run-' + mode + '.stderr')).read_bytes(), 'bucket probe wrote stderr')
        records.append({'mode': mode, 'binarySha256': digest(binary), 'observationSha256': digest(observation),
                        'cases': admission.check_profile(profile)})
        if header:
            records[-1]['headerStorage'] = storage.capture(output, mode, llvm.read_bytes(), lib)
        for key, replacement in (('oom_error', None), ('metadata', 0), ('key_pointer', 0), ('value_pointer', 0),
                                 ('index', True), ('frees', 0), ('remaps', 1), ('metadata_cleared', False),
                                 ('available', 0), ('empty_lookup', False)):
            changed = copy.deepcopy(profile); changed['cases'][0][key] = replacement
            try: admission.check_profile(changed)
            except ValueError as error: corruptions.append({'mode': mode, 'field': key, 'rejection': str(error)})
            else: raise ValueError('accepted corrupted bucket observation: ' + key)
        for key, replacement in (('bits', 16), ('backing', 'i8'), ('fingerprint_offset', 1), ('used_offset', 0)):
            changed = copy.deepcopy(profile); changed['metadata'][key] = replacement
            try: admission.check_profile(changed)
            except ValueError as error: corruptions.append({'mode': mode, 'field': 'metadata.' + key, 'rejection': str(error)})
            else: raise ValueError('accepted corrupted packed metadata observation: ' + key)
    result = {'binding': binding, 'layoutSha256': digest(admission.OUTPUT), 'captures': records,
            'keyLayoutSha256': digest(admission.KEY_OUTPUT),
            'sourceControls': source_controls, 'observationControls': corruptions,
            'scope': 'complete bucket allocation geometry only; initialization, map ownership, probing and retirement remain open'}
    if header:
        result['storageLayoutSha256'] = digest(storage.admission.OUTPUT)
        result['scope'] = 'allocation geometry and private header initialization; receiver publication, metadata clearing, map ownership, probing and retirement remain open'
    return result
