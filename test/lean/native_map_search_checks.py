"""Audit receiver-derived search around the explicit native hash boundary.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import json
from pathlib import Path
import native_map_probe_checks as probe
from native_map_key_checks import GRAPH, require, telescope, expressions
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check
from check_zig_air_memory_proofs import without_imports
from check_word_swap import ROOT
from build_toolchain import digest, run

MODULE = 'Compiler.Extraction.ExpressionMapSearchTests'
SEARCH, TESTS = probe.MAP + 'Search.', GRAPH + 'MapSearchTests.'
LAYOUT = probe.MAP + 'Insertion.Layout.'
CLAIMS = [SEARCH + n for n in ('remember_eq', 'lookup_loop_eq', 'insertion_loop_eq', 'lookup_after_hash_eq', 'insertion_after_hash_eq')]
CLAIMS += [LAYOUT + n for n in ('read_field', 'read_bucket', 'read_capacity')]
CLAIMS += [probe.TABLE + 'Binding.' + n for n in ('read_count', 'empty_of_count_zero')]
CLAIMS += [GRAPH + n for n in ('publish_from_receiver_eq', 'publish_from_receiver_rejected', 'Facts.lookup_from_receiver', 'Facts.probe_receiver_then_publish')]
CLAIMS += [TESTS + n for n in ('third_probe', 'publication_and_lookup', 'empty_owner', 'empty_after_hash_rejected',
    'empty_skips_missing_header', 'missing_header_rejected', 'missing_header_publication_retains_world', 'missing_count_rejected', 'receiver_placement_rejected')]
# Reviewed complete operation bodies and public types. Hashing remains an
# explicit input boundary; these pins must never imply that Wyhash is proved.
DEFINITIONS = {'Compiler.Extraction.ExpressionMap.Search.readCount': 'c4be16ac0edf22337e00ad681d70f155e3951c125ee45de40b548bb6cb303dcb',
 'Compiler.Extraction.ExpressionMap.Search.readBucket': '2556ac9e08b388a2187dcded0c0dd50d6fe17e0df677db8df1bc037d3786f87d',
 'Compiler.Extraction.ExpressionMap.Search.inspect': '82d5e689750cb85f40949790ae8c8fe26a368938bada672e46e0e7cc97bcc4c0',
 'Compiler.Extraction.ExpressionMap.Search.remember': '0fe728e8fe8b097e6ea57ab51f0ed9c2a1e420c268688fcd7f13d5c7968b1c03',
 'Compiler.Extraction.ExpressionMap.Search.lookupLoop': '0fca7f3bb6c49f85be539751272299bb7123824502a7105604e1081a60d01a5d',
 'Compiler.Extraction.ExpressionMap.Search.insertionLoop': 'f06e3a45fc7e57e572fe06bb4b871713b22df7c41478bbf8a2dec2562b1fea5e',
 'Compiler.Extraction.ExpressionMap.Search.lookupAfterHash': 'c713052620005facae276ee6c6ff9000fb3246e2af73184f66f70f412fba9226',
 'Compiler.Extraction.ExpressionMap.Search.insertionAfterHash': '3cbef043980e65d47424c06355a0062e99cbf6a4419036a87897a2851f579b09',
 'Compiler.Extraction.ExpressionMap.Search.withHash': '2abc20856bc178b50ea182ba1977e8859a33d3efa4585640db2a8abcda2ec80c',
 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.publishFromReceiver': '5e351766caf8f6f4e3ae2b7e3f37541eef6c1cfc0c9e1eaeb89b2a408bf5dffc'}
STATEMENTS = {'Compiler.Extraction.ExpressionMap.Search.lookup_after_hash_eq': '91f99ee187b9e430cfd81743bf01ede5f4062e59131e8c6d2d8dcc4bbb168e09',
 'Compiler.Extraction.ExpressionMap.Search.insertion_after_hash_eq': 'eff6032287811e722e22e3e13ece1a57bd7b82f233aa80b2af99b5e1b475d4ac',
 'Compiler.Extraction.ExpressionMap.Insertion.Layout.read_capacity': '1219f2db61d6509c50c5accd1c6502303bb50d9d95838ce4ba46c017f21a41e0',
 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.publish_from_receiver_rejected': '219220d638e810bd1312a3d4e132524b4f9eabd59e0eb320811cba1bb3ea5ddc',
 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.Facts.lookup_from_receiver': 'c5c05ac07e7ce6be31e73c2387354e525153e2f463c010c4e0d0598fed5e4065',
 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.Facts.probe_receiver_then_publish': '3d727a18f315ec428acda35db96013e455a534f565f884dbef848a4f658bfd70'}


def audit_interfaces(records, definitions=None):
    definitions = DEFINITIONS if definitions is None else definitions
    require(len(records) == len(definitions) and {r['name'] for r in records} == set(definitions), 'definition inventory changed')
    for record in records:
        require(probe.encoded_digest(record) == definitions[record['name']], 'unreviewed definition: ' + record['name'])


def interfaces(output, env, lean, *, module=MODULE, definitions=None, prefix='search'):
    definitions = DEFINITIONS if definitions is None else definitions
    directory = output / (prefix + '-interfaces'); directory.mkdir()
    records = expressions.interface_export(directory, env, lean, module, tuple(definitions))
    audit_interfaces(records, definitions)
    controls = []
    for record in records:
        bad = copy.deepcopy(records)
        changed = next(r for r in bad if r['name'] == record['name'])
        # Constructors have a type but no definition body. Pin and corrupt the
        # full exported record in either case, including invariant fields.
        term = changed['value'] if isinstance(changed.get('value'), dict) else changed['type']
        term['root'] = -1
        try: audit_interfaces(bad, definitions)
        except ValueError as error: controls.append({'name': record['name'], 'rejection': str(error)})
        else: raise ValueError('accepted corrupted receiver search definition')
    return {'sha256': digest(directory / 'interfaces.json'), 'checked': list(definitions), 'controls': controls}


def audit(rows):
    indexed = {r['theorem']: r for r in rows}
    dependencies = {
        LAYOUT + 'read_field': {probe.MAP + 'Counter.read_eq'},
        LAYOUT + 'read_capacity': {LAYOUT + 'read_field', probe.BUCKETS + 'Metadata.read_capacity'},
        SEARCH + 'lookup_after_hash_eq': {SEARCH + 'lookup_loop_eq', LAYOUT + 'read_capacity', LAYOUT + 'read_bucket'},
        SEARCH + 'insertion_after_hash_eq': {SEARCH + 'insertion_loop_eq', LAYOUT + 'read_capacity', LAYOUT + 'read_bucket'},
        GRAPH + 'Facts.lookup_from_receiver': {GRAPH + 'Facts.lookup_hashed', SEARCH + 'lookup_after_hash_eq', probe.TABLE + 'Binding.read_count', probe.TABLE + 'Binding.empty_of_count_zero'},
        GRAPH + 'Facts.probe_receiver_then_publish': {GRAPH + 'Facts.probe_then_publish', SEARCH + 'insertion_after_hash_eq', GRAPH + 'publish_from_receiver_eq'},
        TESTS + 'publication_and_lookup': {GRAPH + 'Facts.lookup_from_receiver', GRAPH + 'Facts.probe_receiver_then_publish', probe.TESTS + 'repeated_from_initialized_owner'},
        TESTS + 'missing_header_publication_retains_world': {GRAPH + 'publish_from_receiver_rejected'},
    }
    for name, expected in dependencies.items():
        require(expected <= set(indexed[name]['dependencies']), 'receiver search lost composition: ' + name)
    for name in CLAIMS:
        if not name.startswith(TESTS):
            require(not any(part.endswith('Tests') for dep in indexed[name]['dependencies'] for part in dep.split('.')), 'receiver search depends on a fixture')
    wanted = ['σ', 'safety', 'allocator', 'owner', 'capacity', 'data', 'before', 'rows', 'facts', 'hashes', 'place',
              'receiver', 'bucket', 'bucketCapacity', 'available', 'embedded', 'inv', 'room', 'key', 'owned', 'id', 'aligned', 'custody']
    fields, lets, _, _ = telescope(indexed[GRAPH + 'Facts.probe_receiver_then_publish']['statement'])
    require(list(fields) == wanted and not lets, 'receiver consumer gained a read-success or selected-slot premise')
    for name, expected in STATEMENTS.items():
        require(probe.encoded_digest(indexed[name]['statement']) == expected, 'receiver search rebound its original state/outcome: ' + name)
    return {'checkedDependencies': sorted(dependencies), 'checkedStatements': list(STATEMENTS),
            'receiverCapacityAndCountDerived': True, 'emptyLookupSkipsHashContinuation': True,
            'nativeHashProducerVerified': False, 'completeNativeLookupVerified': False}


def audit_controls(rows):
    records = []
    for name in STATEMENTS:
        bad = copy.deepcopy(rows)
        next(r for r in bad if r['theorem'] == name)['statement']['root'] = 0
        try: audit(bad)
        except ValueError as error: records.append({'name': name, 'rejection': str(error)})
        else: raise ValueError('accepted corrupted receiver search statement')
    return records


def source_binding(lib, **overrides):
    return {**probe.source_binding(lib, **overrides),
            'scope': 'receiver-derived size-zero prefix, post-hash search and new-slot publication; native hash and replacement remain separate',
            'receiverSearchBoundary': 'getIndex size-zero prefix and post-hash lookup/insertion; native hash producer remains open'}


def source_controls(lib):
    native = (Path(lib) / 'std/hash_map.zig').read_bytes()
    records = []
    for before, after in ((b'if (self.size == 0)', b'if (self.size != 0)'),
                          (b'var limit = self.capacity();', b'var limit = 0;'),
                          (b'var first_tombstone_idx: usize = self.capacity();', b'var first_tombstone_idx: usize = 0;'),
                          (b'metadata = self.metadata.? + idx;', b'metadata = self.metadata.?;')):
        require(before in native, 'missing receiver source control')
        try: source_binding(lib, native=native.replace(before, after, 1))
        except (ValueError, probe.ADMISSION.storage.Unsupported) as error:
            records.append({'mutation': before.decode(), 'rejection': str(error)})
        else: raise ValueError('accepted changed receiver source')
    return records


def controls(output, env, lean):
    directory = ROOT / 'lean/Compiler/Extraction'
    source = 'import Compiler.Extraction.ExpressionMapProbeTests\n'
    for name in ('Reads', 'Loop', 'Memory'):
        source += without_imports((directory / ('ExpressionMapSearch' + name + '.lean')).read_text()) + '\n'
    fixture = without_imports((directory / 'ExpressionMapSearchTests.lean').read_text())
    records = [mutation_check(output, 'search-unchanged', source + fixture, True, env, lean)]
    for name, before, after in (
        ('count-field', 'receiver .size | .error', 'receiver .available | .error'),
        ('bucket-identity', 'else .ok address.allocation', 'else .ok (address.allocation + 1)'),
        ('limit-zero', 'source limit.toNat (Probe.start', 'source 0 (Probe.start'),
        ('tombstone-sentinel', '(Probe.start capacity hash) first.toNat', '(Probe.start capacity hash) 0'),
        ('wrong-empty-guard', 'if size = 0 then .ok none else', 'if size ≠ 0 then .ok none else'),
        ('lost-read-fault', '| .error fault => (.error fault, before)', '| .error _fault => (.ok (), before)'),
    ):
        require(before in source, 'missing receiver mutation: ' + name)
        records.append(mutation_check(output, 'search-' + name, source.replace(before, after, 1), False, env, lean))
    return checked_controls(output, records)


def check_observation(value):
    fields = probe.ADMISSION.fields
    fields(value, ('schema', 'hashes', 'cases'), 'receiver search')
    require(value['schema'] == 'oksolc.expression-map-caller.v1', 'wrong caller schema')
    hashes = value['hashes']
    require(type(hashes) is list and len(hashes) == 2 and all(type(h) is int and 0 <= h < 2**64 for h in hashes), 'invalid caller hashes')
    cases = value['cases']
    require(type(cases) is list and len(cases) == 4, 'incomplete caller cases')
    miss_comparisons = int((hashes[0] & 7) == (hashes[1] & 7) and (hashes[0] >> 57) == (hashes[1] >> 57))
    expected = (('empty-unallocated', 0, 0, 0, False, 0, 0, None), ('empty-allocated', 8, 0, 6, True, 0, 0, None),
                ('hit', 8, 1, 5, True, 1, 1, 37), ('miss', 8, 1, 5, True, 1, miss_comparisons, None))
    for case, wanted in zip(cases, expected):
        fields(case, ('name', 'capacity', 'size', 'available', 'metadata_present', 'hash_calls', 'comparisons', 'result', 'unchanged'), 'caller case')
        name, capacity, size, available, present, calls, comparisons, result = wanted
        require(case['name'] == name and case['metadata_present'] is present and case['unchanged'] is True, 'caller changed receiver or branch')
        for key, expected in (('capacity', capacity), ('size', size), ('available', available), ('hash_calls', calls), ('comparisons', comparisons)):
            require(type(case[key]) is int and case[key] == expected, 'wrong caller observation: ' + key)
        require(case['result'] is None if result is None else type(case['result']) is int and case['result'] == result, 'wrong caller result')
    return value


def capture(output, env):
    records, controls = [], []
    for mode in ('Debug', 'ReleaseSafe', 'ReleaseFast'):
        binary = output / ('buckets-' + mode); name = 'caller-' + mode
        run(output, name, [binary, 'caller'], cwd=ROOT, env=env)
        raw = (output / (name + '.stdout')).read_bytes()
        require(len(raw) < 8192 and not (output / (name + '.stderr')).read_bytes(), 'unbounded or noisy caller capture')
        value = check_observation(json.loads(raw))
        records.append({'mode': mode, 'binarySha256': digest(binary), 'observationSha256': digest(output / (name + '.stdout')), 'observed': value})
        for index, field, wrong in ((0, 'hash_calls', 1), (1, 'metadata_present', False), (2, 'result', None), (3, 'unchanged', False)):
            bad = copy.deepcopy(value); bad['cases'][index][field] = wrong
            try: check_observation(bad)
            except ValueError as error: controls.append({'mode': mode, 'case': index, 'field': field, 'rejection': str(error)})
            else: raise ValueError('accepted corrupt caller capture')
    return {'captures': records, 'observationControls': controls, 'nativeHashProducerVerified': False}
