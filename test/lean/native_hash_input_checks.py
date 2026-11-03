"""Derive the native hash input image without certifying Wyhash execution.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import json
from pathlib import Path
import native_map_search_checks as search
from native_map_key_checks import GRAPH, require, telescope
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check
from check_zig_air_memory_proofs import without_imports
from check_word_swap import ROOT
from build_toolchain import digest, run

MODULE = 'Compiler.Extraction.ExpressionMapHashInputTests'
INPUT, TESTS = search.probe.MAP + 'HashInput.', GRAPH + 'MapHashInputTests.'
CLAIMS = [INPUT + n for n in ('shape', 'total_length', 'read_verified', 'oversized_rejected')]
CLAIMS += [search.SEARCH + n for n in ('with_input_digest_eq', 'with_input_digest_rejected', 'insertion_with_input_digest_eq')]
CLAIMS += [GRAPH + 'Facts.' + n for n in ('query_byte_budget', 'hash_input', 'lookup_from_hash_input', 'probe_hash_input_then_publish')]
CLAIMS += [TESTS + n for n in ('existing_lookup', 'existing_publication', 'word_bytes', 'scalar_boundaries', 'argument_bytes',
    'native_bytes', 'copied_bytes', 'changed_bytes', 'uninitialized_rejected', 'lookup_uninitialized_rejected', 'oversized_rejected', 'empty_skips_hash_inputs')]
LENGTHS = [0, 1, 2, 3, 10, 11, 12, 13, 14, 15, 16, 17, 31, 32, 33, 65]
# Complete reviewed operation bodies and public statements; no Wyhash body is
# admitted by these pins. The byte-input digest is an explicit open boundary.
DEFINITIONS = {'Compiler.Extraction.ExpressionMap.HashInput.word': '73c3242cecf2f5ac7d7015ee3cbe9c18492c6a31f44fdc6baafca3b857856fb2',
 'Compiler.Extraction.ExpressionMap.HashInput.data': '29a6872d605c8d230ff4d038d57c1db7464f0a8ce45618b655281023f0eef11b',
 'Compiler.Extraction.ExpressionMap.HashInput.arguments': 'a81cc143125e2d8c5587202dd43d396dc3fe9b9de95910477b6c5cfdfbca8a25',
 'Compiler.Extraction.ExpressionMap.HashInput.encode': 'c5ad74545d8116ec1fd49dc0d26acb3498db33032da0f34eadf154427cebfa62',
 'Compiler.Extraction.ExpressionMap.HashInput.read': '8d5cde9fe8ed4dbf0461f38178b01a387ccc941e061e1af63bd89c42dca265b5',
 'Compiler.Extraction.ExpressionMap.Search.withInputDigest': '788769d2563b9a7a07d7f225a820978ef6e66b91d00d35339caaf19c892efe28',
 'Compiler.Extraction.ExpressionMap.Search.insertionWithInputDigest': '736fd509b1c0f62932ae08d718fc5f238f799fb88d5080954a97b918fb0b3c0c'}
STATEMENTS = {'Compiler.Extraction.ExpressionMap.HashInput.read_verified': '035f6cff4e947eb20dda754d5f3b335d9834a0a7296d7a2b0decf6efcebb3ca6',
 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.Facts.query_byte_budget': 'a596669835afdafe25a1b300a3bfed189c7da72e7f584136fe6af402f1cafb92',
 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.Facts.hash_input': 'f301654a109c8b86b2e4feee075cc5b75aa6ff63914b4b04445cbcd86524a564',
 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.Facts.lookup_from_hash_input': 'a7d7da099794a2e60a616498686476afc412343d6247cf632e2806083cd0beb1',
 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.Facts.probe_hash_input_then_publish': '110b2f2efa6f045c3bfcd1fb2c9433104fcfe0c838ac78794fcd172ffc8e8bca',
 'Compiler.Extraction.ExpressionMap.Search.with_input_digest_rejected': '1d255bbececfe4c95a5e850dbb97488a45826edbf385c39515c2efa72c2043e4'}


def interfaces(output, env, lean):
    return search.interfaces(output, env, lean, module=MODULE, definitions=DEFINITIONS, prefix='hash-input')


def audit(rows):
    indexed = {r['theorem']: r for r in rows}
    dependencies = {
        INPUT + 'read_verified': {search.probe.MAP + 'ArgumentScan.bytes_verified', 'Compiler.ZigAir.Memory.WordByteView.read_word'},
        GRAPH + 'Facts.query_byte_budget': {'Compiler.ZigAir.Memory.valid_regions_separated', 'Compiler.ZigAir.Memory.valid_lookup'},
        GRAPH + 'Facts.hash_input': {GRAPH + 'Facts.query_view', GRAPH + 'Facts.query_byte_budget', INPUT + 'read_verified', INPUT + 'total_length'},
        GRAPH + 'Facts.lookup_from_hash_input': {GRAPH + 'Facts.hash_input', GRAPH + 'Facts.lookup_from_receiver'},
        GRAPH + 'Facts.probe_hash_input_then_publish': {GRAPH + 'Facts.hash_input', GRAPH + 'Facts.probe_receiver_then_publish'},
        TESTS + 'existing_lookup': {GRAPH + 'Facts.lookup_from_hash_input', search.probe.TESTS + 'repeated_from_initialized_owner'},
        TESTS + 'existing_publication': {GRAPH + 'Facts.probe_hash_input_then_publish', search.probe.TESTS + 'repeated_from_initialized_owner'},
    }
    for name, expected in dependencies.items():
        require(expected <= set(indexed[name]['dependencies']), 'hash input lost its producer/consumer: ' + name)
    for name in CLAIMS:
        if not name.startswith(TESTS):
            require(not any(part.endswith('Tests') for dep in indexed[name]['dependencies'] for part in dep.split('.')), 'hash input depends on a fixture')
    wanted = ['σ', 'safety', 'allocator', 'owner', 'capacity', 'data', 'before', 'rows', 'facts', 'key', 'owned', 'aligned', 'custody']
    fields, lets, _, _ = telescope(indexed[GRAPH + 'Facts.hash_input']['statement'])
    require(list(fields) == wanted and not lets, 'hash input gained a byte-image or arithmetic premise')
    for name, expected in STATEMENTS.items():
        require(search.probe.encoded_digest(indexed[name]['statement']) == expected, 'hash input lost its exact source/budget/consumer: ' + name)
    return {'checkedDependencies': sorted(dependencies), 'checkedStatements': list(STATEMENTS),
            'inputBytesAndLengthDerived': True, 'nativeHashProducerVerified': False, 'completeNativeLookupVerified': False}


def audit_controls(rows):
    records = []
    for name in STATEMENTS:
        bad = copy.deepcopy(rows)
        next(r for r in bad if r['theorem'] == name)['statement']['root'] = 0
        try: audit(bad)
        except ValueError as error: records.append({'name': name, 'rejection': str(error)})
        else: raise ValueError('accepted corrupted hash-input statement')
    return records


def source_binding(lib, source=None):
    raw = search.probe.ADMISSION.storage.SOURCE.read_bytes() if source is None else source
    binding = search.source_binding(lib, source=raw)
    search.probe.ADMISSION.storage.function(raw, 'pub fn hash(_: @This(), key: ExpressionKey) u64').expect('''{
        var hasher = std.hash.Wyhash.init(0);
        hasher.update(std.mem.asBytes(&key.item_type));
        hasher.update(std.mem.asBytes(&key.instruction));
        hasher.update(std.mem.asBytes(&key.data));
        hasher.update(std.mem.sliceAsBytes(key.arguments));
        hasher.update(std.mem.asBytes(&key.sequence_number));
        return hasher.final(); }''')
    return {**binding, 'hashInputScope': 'five scalar/argument byte images and arithmetic budget; native hasher local state remains open',
            'scalarBytes': [4, 1, 32, 4], 'sourceAdapterFormallyVerified': False, 'nativeHashProducerVerified': False,
            'observedWyhashSha256': digest(Path(lib) / 'std/hash/wyhash.zig')}


def source_controls(lib):
    raw = search.probe.ADMISSION.storage.SOURCE.read_bytes()
    records = []
    for before, after in ((b'std.hash.Wyhash.init(0)', b'std.hash.Wyhash.init(1)'),
                          (b'std.mem.asBytes(&key.data)', b'std.mem.asBytes(&key.instruction)'),
                          (b'std.mem.sliceAsBytes(key.arguments)', b'std.mem.asBytes(&key.arguments)'),
                          (b'hasher.update(std.mem.asBytes(&key.sequence_number));', b'')):
        require(before in raw, 'missing hash-input source control')
        try: source_binding(lib, raw.replace(before, after, 1))
        except (ValueError, search.probe.ADMISSION.storage.Unsupported) as error:
            records.append({'mutation': before.decode(), 'rejection': str(error)})
        else: raise ValueError('accepted changed hash input producer')
    return records


def controls(output, env, lean):
    directory = ROOT / 'lean/Compiler/Extraction'
    source = 'import Compiler.Extraction.ExpressionMapSearchTests\nimport Compiler.ZigAir.MemoryShapeRegions\n'
    for name in ('ExpressionMapHashInput', 'ExpressionMapHashInputMemory'):
        source += without_imports((directory / (name + '.lean')).read_text()) + '\n'
    fixture = without_imports((directory / 'ExpressionMapHashInputTests.lean').read_text())
    records = [mutation_check(output, 'hash-input-unchanged', source + fixture, True, env, lean)]
    # Reuse the small byte-vector witnesses; malformed core proofs must not
    # trigger reduction/pretty-printing of the large populated-map fixtures.
    byte_fixture = ('namespace ' + TESTS.rstrip('.') + '\nopen Compiler.Extraction.ExpressionMap\n' +
                    fixture[fixture.index('theorem word_bytes'):fixture.index('theorem scalar_boundaries')] +
                    '\nend ' + TESTS.rstrip('.') + '\n')
    for name, before, after in (
        ('wrong-byte-order', 'Compiler.ZigAir.WordBytes.read .little value', 'Compiler.ZigAir.WordBytes.read .big value'),
        ('short-data', 'List.range 32', 'List.range 31'),
        ('changed-scalar', '[word key.kind, [key.instruction], data key.data, bytes, word key.sequence]', '[word key.kind, [key.instruction], data key.data, bytes, word key.kind]'),
        ('shifted-argument', 'ArgumentScan.bytes state source 0', 'ArgumentScan.bytes state source 1'),
        ('lost-byte-budget', 'owned.items.length * 4 + 48 < addressLimit := by', 'owned.items.length * 4 + addressLimit < addressLimit := by'),
        ('lost-hash-fault', 'let inputs ← HashInput.read state key source', 'let inputs := (HashInput.read state key source).toOption.getD []'),
    ):
        require(before in source, 'missing hash-input mutation: ' + name)
        records.append(mutation_check(output, 'hash-input-' + name, source.replace(before, after, 1) + (byte_fixture if name == 'wrong-byte-order' else ''), False, env, lean))
    return checked_controls(output, records)


def expected_inputs(length):
    word = lambda value, width: list(value.to_bytes(width, 'little'))
    arguments = [byte for i in range(length) for byte in word((i * 0x9e3779b9) % 2**32, 4)]
    return [word(2, 4), [171], word(11 * 2**192 + 7 * 2**128 + 5 * 2**64 + 3, 32), arguments, word(0x12345678, 4)]


def check_observation(value):
    fields = search.probe.ADMISSION.fields
    fields(value, ('schema', 'endian', 'usize_bytes', 'scalar_bytes', 'cases'), 'hash input')
    require(value['schema'] == 'oksolc.expression-hash-input.v1' and value['endian'] == 'little', 'wrong hash-input profile')
    require(type(value['usize_bytes']) is int and value['usize_bytes'] == 8, 'wrong hash-input usize')
    sizes = value['scalar_bytes']
    require(type(sizes) is list and all(type(n) is int for n in sizes) and sizes == [4, 1, 32, 4], 'wrong scalar representation widths')
    cases = value['cases']
    require(type(cases) is list and len(cases) == len(LENGTHS), 'incomplete hash-input cases')
    for case, length in zip(cases, LENGTHS):
        fields(case, ('length', 'inputs', 'native_hash', 'replayed_hash'), 'hash input case')
        require(type(case['length']) is int and case['length'] == length, 'wrong hash-input order/length')
        inputs = case['inputs']
        require(type(inputs) is list and len(inputs) == 5 and all(type(chunk) is list and all(type(b) is int and 0 <= b < 256 for b in chunk) for chunk in inputs), 'invalid hash-input byte images')
        require(inputs == expected_inputs(length), 'native input bytes differ from specified field images')
        require(all(type(case[k]) is int and 0 <= case[k] < 2**64 for k in ('native_hash', 'replayed_hash')), 'invalid native hash observation')
        require(case['native_hash'] == case['replayed_hash'], 'five-input native replay changed its hash')
    return value


def capture(output, env):
    captures, controls = [], []
    for mode in ('Debug', 'ReleaseSafe', 'ReleaseFast'):
        binary = output / ('buckets-' + mode); name = 'hash-input-' + mode
        run(output, name, [binary, 'hash-input'], cwd=ROOT, env=env)
        raw = (output / (name + '.stdout')).read_bytes()
        require(len(raw) < 65536 and not (output / (name + '.stderr')).read_bytes(), 'unbounded or noisy hash-input capture')
        value = check_observation(json.loads(raw))
        captures.append({'mode': mode, 'binarySha256': digest(binary), 'observationSha256': digest(output / (name + '.stdout')), 'observed': value})
        for index, chunk in ((0, 0), (2, 2), (14, 3), (15, 4)):
            bad = copy.deepcopy(value); bad['cases'][index]['inputs'][chunk][0] ^= 1
            try: check_observation(bad)
            except ValueError as error: controls.append({'mode': mode, 'case': index, 'chunk': chunk, 'rejection': str(error)})
            else: raise ValueError('accepted corrupted native hash-input bytes')
    return {'captures': captures, 'observationControls': controls, 'nativeHashProducerVerified': False}
