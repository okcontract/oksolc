"""Check complete local Wyhash execution consumed by map lookup/publication.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
from pathlib import Path
import native_wyhash_final_checks as final
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check
from check_zig_air_memory_proofs import without_imports
from check_word_swap import ROOT

local = final.local
require = local.require
MODULE = 'Compiler.Extraction.WyhashHashTests'
UPDATE = 'Compiler.Extraction.WyhashUpdate.'
HASH = 'Compiler.Extraction.WyhashHash.'
MAP = 'Compiler.Extraction.ExpressionMap.'
GRAPH = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.'
CLAIMS = [final.BYTES + n for n in ('copy_valid', 'cellsFrom_lookup', 'image_represents')]
CLAIMS += [UPDATE + n for n in ('initFields_eq', 'init_eq', 'Core.store_word', 'Core.byte_frame', 'init_invariant',
    'Input.Ready.represented', 'Input.Ready.store_word', 'lane_verified', 'round_verified', 'copy_buffer',
    'fill_verified', 'loop_verified', 'close_buffer', 'update_verified', 'Invariant.final')]
CLAIMS += [HASH + n for n in ('updates_verified', 'run_verified', 'run_digest')]
CLAIMS += [MAP + n for n in ('HashInput.wyhash_verified', 'Search.with_local_wyhash_eq', 'Search.insertion_with_local_wyhash_eq')]
CLAIMS += [GRAPH + 'Facts.' + n for n in ('lookup_from_local_wyhash', 'probe_local_wyhash_then_publish')]
CLAIMS += [HASH + 'Tests.' + n for n in ('captured_results', 'exact_block_no_reads', 'overflow_before_reads', 'short_input_explicit',
    'missing_input_rejected', 'wrong_input_type_rejected')]
CLAIMS += [GRAPH + n for n in ('MapProbeTests.initialized_owner', 'MapWyhashTests.observed_source_consumed',
    'MapWyhashTests.initialized_publication_lookup', 'MapWyhashTests.empty_skips_hash')]
DEFINITION_NAMES = [final.BYTES + n for n in ('cellsFrom', 'imageView')]
DEFINITION_NAMES += [UPDATE + n for n in ('store', 'seedState', 'initFields', 'init', 'secret', 'Input.external',
    'Input.buffer', 'Input.cells', 'Input.view', 'Input.Ready', 'lane', 'round', 'loop', 'fill', 'updateBody',
    'update', 'ByteAt', 'WordAt', 'Core.mk', 'Invariant.mk', 'initialCells', 'byteAt')]
DEFINITION_NAMES += [HASH + n for n in ('updates', 'run', 'digest')]
DEFINITION_NAMES += [MAP + 'Search.' + n for n in ('withLocalWyhash', 'insertionWithLocalWyhash')]
STATEMENT_NAMES = [UPDATE + n for n in ('init_invariant', 'loop_verified', 'update_verified', 'Invariant.final')]
STATEMENT_NAMES += [HASH + n for n in ('updates_verified', 'run_verified', 'run_digest')]
STATEMENT_NAMES += [MAP + 'HashInput.wyhash_verified', GRAPH + 'Facts.lookup_from_local_wyhash', GRAPH + 'Facts.probe_local_wyhash_then_publish']
DEFINITIONS = {'Compiler.ZigAir.Memory.ByteSlice.cellsFrom': '76ee3512d27504436de9ca63468162170f4a7daf551cf37ba86c3b0b420fb8aa',
 'Compiler.ZigAir.Memory.ByteSlice.imageView': 'd9a6ce84fbff21374ae2adb014c604682958f2ad69a4625c5d158d30335c63e2',
 'Compiler.Extraction.WyhashUpdate.store': '979a583cf9d0083c840fa8c8e9a1e5fd2ec7080f5d011b16cb727ee6e351fe25',
 'Compiler.Extraction.WyhashUpdate.seedState': '2a589b7e06390553ce200e5a9cd5b204744f074b4fa46385b7757bcd62d3fc66',
 'Compiler.Extraction.WyhashUpdate.initFields': 'b335927533e72a0964e3d5f053d348779a5f3acd67e36cb63bc5357881c20b22',
 'Compiler.Extraction.WyhashUpdate.init': '169d4225ced89e48d5abc99344997dfb755008cbc6e3723d2b3e4982c169ff51',
 'Compiler.Extraction.WyhashUpdate.secret': '0c60d5d96f890b08d1a895e918dd422d2b9349310660b19b8135faede7b32207',
 'Compiler.Extraction.WyhashUpdate.Input.external': 'e96ae660c0f0808adf92eb0a0587a7ebc026303035901e5f75cba177b1dfd198',
 'Compiler.Extraction.WyhashUpdate.Input.buffer': '4db192db5629be7b9853ee01c3374b880e18c9b953df7baab8cdf3b62b5eca9f',
 'Compiler.Extraction.WyhashUpdate.Input.cells': '066a82af2a30af8e72a967e4901560d4b202d72e9118d1b7f7dc1853edcd857d',
 'Compiler.Extraction.WyhashUpdate.Input.view': '7889a955f33af9184b0384b0846ef0dd85b3fb36b927e488e5d855b2fc8277fd',
 'Compiler.Extraction.WyhashUpdate.Input.Ready': '32479632a82813171273ea4a743934f32727c833d9e7f4c801e9b978fbadfc85',
 'Compiler.Extraction.WyhashUpdate.lane': 'fa9f99ea7fd699521ee766e1078f0884bcd5868528d740f473cb124f8eb464bb',
 'Compiler.Extraction.WyhashUpdate.round': 'dea0fbb52085443f32b940ed3345902ad0a67dcafa08b1c623c341590e238774',
 'Compiler.Extraction.WyhashUpdate.loop': '30d6564464106604dc2becdc5694b385462b85e98f5d451a4ba1e4fad9369d9b',
 'Compiler.Extraction.WyhashUpdate.fill': '9bc33ba9b0d6e07d9de09ffe74fe5d434d48a722485dc262c311562af0b29963',
 'Compiler.Extraction.WyhashUpdate.updateBody': '0e86cb645f2cb323c9f9b362b9df5dd20b9053c4169d99699376a2e42c75b5c2',
 'Compiler.Extraction.WyhashUpdate.update': 'b53b54b11465ebc436af5d9e739ab120b793c95b9bbc5cafe30d672800838ea5',
 'Compiler.Extraction.WyhashUpdate.ByteAt': '639cb5a1b21671fa583c116718aad256566d78603c12f103fe407cb2c40c7223',
 'Compiler.Extraction.WyhashUpdate.WordAt': '73d3867a200282787c4939166433e52709574ea13a4092ae9dfac5c829129791',
 'Compiler.Extraction.WyhashUpdate.Core.mk': '5b266469959ea97362826be93a50505ea9fbac86d7dd7626e13f1cc3ed260715',
 'Compiler.Extraction.WyhashUpdate.Invariant.mk': '2f58dabb5ee4db87ef77c342b629ee0870c1ccff7408bab8aca04eca67a9afee',
 'Compiler.Extraction.WyhashUpdate.initialCells': '47e09d8dbb7ce5e99ddd36ce10fcd0b382c39028641a0a33a642fb01414fb57c',
 'Compiler.Extraction.WyhashUpdate.byteAt': '9f397115e5ab0c309ae196c3f246c7151ad2e874bc020255211ff2f25c2aae43',
 'Compiler.Extraction.WyhashHash.updates': '10eba6b8717d8c3ea8cee4b1596894b8c145a37fcf12a399e228d968563de903',
 'Compiler.Extraction.WyhashHash.run': '13df289a1ca4140cbec3873a2e5fb53be9f26cbb0a49076dfaa88d35be660b19',
 'Compiler.Extraction.WyhashHash.digest': '884a8d4a87085b3b1348118ce18635831cf7ecdcfad732b684a7fe1049b068e3',
 'Compiler.Extraction.ExpressionMap.Search.withLocalWyhash': '5b689b08c2c548b05e83d605e7dbf59247539c0fb2419929546a5f21e39e2aae',
 'Compiler.Extraction.ExpressionMap.Search.insertionWithLocalWyhash': 'bd9744de009207a291de513c2a8b81949c3516135485776b8250272518d47b10'}
STATEMENTS = {'Compiler.Extraction.WyhashUpdate.init_invariant': '1537e7752b3ae1f785e42f58e45ad25967c76a13cf29f11267d7860abb235d45',
 'Compiler.Extraction.WyhashUpdate.loop_verified': '27fd8adc30b3edc221073573a92e70b50a25c02b1cc2b6ee9bd366f2f613fd76',
 'Compiler.Extraction.WyhashUpdate.update_verified': '05b9f1e621946d759d042815229b150ae14224e81606273dfeda2a26b2426d16',
 'Compiler.Extraction.WyhashUpdate.Invariant.final': 'f5834859de1c518ab15e5dcd819080fd34c504aa774799c6bdee0fca6cd06a69',
 'Compiler.Extraction.WyhashHash.updates_verified': '743dcb438d1e61fc2eab2ca1b030779d36c39156510851b40e6a7d3e9af3692f',
 'Compiler.Extraction.WyhashHash.run_verified': 'efb5565296d392c56a0878080335e87fada8cec1e43d42daca2e1140d5069ed0',
 'Compiler.Extraction.WyhashHash.run_digest': '3bef6454a2a90d5df276a04952629058a40501b696190c20af7f96b0e0cf42ac',
 'Compiler.Extraction.ExpressionMap.HashInput.wyhash_verified': 'e16478b81d4595af32ea49cb50a0b9a22fa71015f096639aac2f5a82be4a9e59',
 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.Facts.lookup_from_local_wyhash': '7b831e56fb7bdbfa3133e90c15e7ced1856c764fe987d70c022210cffa88e321',
 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.Facts.probe_local_wyhash_then_publish': '04b0c8adcad3e9f0d5501ec8d99a39c4b4cd6490a305e280000e611684854926'}
LENGTHS = [[4, 1, 32, 0, 4], [4, 1, 32, 4, 4], [4, 1, 32, 8, 4], [4, 1, 32, 12, 4],
    [4, 1, 32, 60, 4], [0, 0, 0, 48, 0], [48, 1, 0, 0, 0], [47, 2, 0, 0, 0],
    [1, 47, 1, 0, 0], [0, 0, 0, 49, 0], [0, 0, 0, 96, 0], [0, 0, 0, 97, 0],
    [16, 16, 16, 16, 16], [49, 15, 1, 47, 2]]
SECRETS = [local.SECRET1, 0x8ebc6af09c88c6e3, 0x589965cc75374cc3]


def expected_case(sizes, index):
    state = [local.mix(local.SECRET0, local.SECRET1)] * 3
    total = length = 0
    buf = [None] * 48

    def snapshot():
        return {'length': length, 'total': total, 'state': state[:], 'initialized': [
            b if i < length or (total > 16 and length < 16 and i >= 48 - (16 - length)) else None
            for i, b in enumerate(buf)]}

    def round_block(block):
        require(len(block) == 48 and None not in block, 'oracle read outside initialized block')
        for lane in range(3):
            a = int.from_bytes(bytes(block[16 * lane:16 * lane + 8]), 'little')
            b = int.from_bytes(bytes(block[16 * lane + 8:16 * lane + 16]), 'little')
            state[lane] = local.mix(a ^ SECRETS[lane], b ^ state[lane])

    steps = [snapshot()]
    for size in sizes:
        data = [((total + i) * 17 + index * 29 + 3) % 256 for i in range(size)]
        total += size
        if size <= 48 - length:
            buf[length:length + size] = data
            length += size
        else:
            at = 0
            if length:
                at = 48 - length
                buf[length:] = data[:at]
                round_block(buf)
                length = 0
            while at + 48 < size:
                round_block(data[at:at + 48])
                at += 48
            remaining = size - at
            if remaining < 16 and at >= 48:
                rem = 16 - remaining
                buf[48 - rem:] = data[at - rem:at]
            buf[:remaining] = data[at:]
            length = remaining
        steps.append(snapshot())
    answer = local.finalize(state, total, buf, length)
    return {'lengths': sizes, 'steps': steps, 'native_hash': answer, 'repeated_hash': answer,
            'changed_a_hash': answer, 'changed_b_hash': answer, 'source_retained': True}


def strict_equal(actual, expected, path='Wyhash hash'):
    require(type(actual) is type(expected), 'wrong observation type: ' + path)
    if isinstance(expected, dict):
        require(set(actual) == set(expected), 'wrong observation fields: ' + path)
        for key in expected: strict_equal(actual[key], expected[key], path + '.' + key)
    elif isinstance(expected, list):
        require(len(actual) == len(expected), 'incomplete observation: ' + path)
        for i, value in enumerate(expected): strict_equal(actual[i], value, path + '[' + str(i) + ']')
    else:
        require(actual == expected, 'changed native observation: ' + path)


def check_observation(value):
    expected = {'schema': 'oksolc.wyhash-hash.v1', 'endian': 'little', 'usize_bytes': 8,
        'size': 104, 'alignment': 8, 'offsets': [0, 8, 16, 40, 56, 48],
        'cases': [expected_case(sizes, index) for index, sizes in enumerate(LENGTHS)]}
    strict_equal(value, expected)
    return value


def capture(output, env):
    return local.capture(output, env, command='wyhash-hash', checker=check_observation)


def interfaces(output, env, lean):
    require(set(DEFINITIONS) == set(DEFINITION_NAMES), 'incomplete hash definition pins')
    return local.inputs.search.interfaces(output, env, lean, module=MODULE, definitions=DEFINITIONS, prefix='wyhash-hash')


def audit(rows):
    indexed = {r['theorem']: r for r in rows}
    dependencies = {
        UPDATE + 'copy_buffer': {final.BYTES + 'copy_verified', final.BYTES + 'copy_valid'},
        UPDATE + 'update_verified': {UPDATE + 'copy_buffer', UPDATE + 'fill_verified', UPDATE + 'loop_verified', UPDATE + 'close_buffer'},
        UPDATE + 'Invariant.final': {final.BUFFER + 'run_verified'},
        HASH + 'updates_verified': {UPDATE + 'update_verified', final.BYTES + 'image_represents'},
        HASH + 'run_verified': {UPDATE + 'init_invariant', HASH + 'updates_verified', UPDATE + 'Invariant.final'},
        HASH + 'run_digest': {HASH + 'run_verified'},
        MAP + 'HashInput.wyhash_verified': {HASH + 'run_digest'},
        GRAPH + 'Facts.lookup_from_local_wyhash': {GRAPH + 'Facts.hash_input', MAP + 'HashInput.wyhash_verified', GRAPH + 'Facts.lookup_from_receiver'},
        GRAPH + 'Facts.probe_local_wyhash_then_publish': {GRAPH + 'Facts.hash_input', MAP + 'HashInput.wyhash_verified', GRAPH + 'Facts.probe_receiver_then_publish'},
        GRAPH + 'MapWyhashTests.initialized_publication_lookup': {GRAPH + 'MapProbeTests.initialized_owner', GRAPH + 'Facts.lookup_from_local_wyhash', GRAPH + 'Facts.probe_local_wyhash_then_publish'},
    }
    for name, required in dependencies.items():
        require(required <= set(indexed[name]['dependencies']), 'hash lost its producer/consumer: ' + name)
    for name in CLAIMS:
        if not any(part.endswith('Tests') for part in name.split('.')):
            require(not any(part.endswith('Tests') for dep in indexed[name]['dependencies'] for part in dep.split('.')), 'hash core depends on a fixture')
    require(set(STATEMENTS) == set(STATEMENT_NAMES), 'incomplete hash statement pins')
    for name, expected in STATEMENTS.items():
        require(local.inputs.search.probe.encoded_digest(indexed[name]['statement']) == expected, 'changed hash statement: ' + name)
    for suffix, expected in (
        ('lookup_from_local_wyhash', ['σ', 'safety', 'allocator', 'owner', 'capacity', 'data', 'before', 'rows', 'facts', 'place', 'receiver', 'bucket', 'bucketCapacity', 'available', 'inv', 'key', 'owned', 'aligned', 'custody']),
        ('probe_local_wyhash_then_publish', ['σ', 'safety', 'allocator', 'owner', 'capacity', 'data', 'before', 'rows', 'facts', 'place', 'receiver', 'bucket', 'bucketCapacity', 'available', 'embedded', 'inv', 'room', 'key', 'owned', 'id', 'aligned', 'custody'])):
        fields, lets, _, _ = local.inputs.telescope(indexed[GRAPH + 'Facts.' + suffix]['statement'])
        require(list(fields) == expected and not lets, 'local hash consumer gained a digest, successful run, poststate or byte budget premise')
    return {'checkedDependencies': sorted(dependencies), 'checkedStatements': list(STATEMENTS),
        'completeLocalHashVerified': True, 'lookupPublicationConsumeLocalHash': True,
        'localHeapAdmissionVerified': False, 'nativeHashProducerVerified': False}


def audit_controls(rows):
    records = []
    for name in STATEMENTS:
        bad = copy.deepcopy(rows)
        next(r for r in bad if r['theorem'] == name)['statement']['root'] = -1
        try: audit(bad)
        except ValueError as error: records.append({'name': name, 'rejection': str(error)})
        else: raise ValueError('accepted changed hash statement')
    return records


def source_binding(lib, native=None):
    binding = final.source_binding(lib, native)
    raw = (Path(lib) / 'std/hash/wyhash.zig').read_bytes() if native is None else native
    function = local.inputs.search.probe.ADMISSION.storage.function
    bodies = {
        'pub fn init(seed: u64) Wyhash': '''{
            var self = Wyhash{ .a = undefined, .b = undefined, .state = undefined,
                .total_len = 0, .buf = undefined, .buf_len = 0, };
            self.state[0] = seed ^ mix(seed ^ secret[0], secret[1]);
            self.state[1] = self.state[0]; self.state[2] = self.state[0]; return self; }''',
        'pub fn update(self: *Wyhash, input: []const u8) void': '''{
            self.total_len += input.len;
            if (input.len <= 48 - self.buf_len) {
                @memcpy(self.buf[self.buf_len..][0..input.len], input); self.buf_len += input.len; return; }
            var i: usize = 0;
            if (self.buf_len > 0) { i = 48 - self.buf_len;
                @memcpy(self.buf[self.buf_len..][0..i], input[0..i]); self.round(&self.buf); self.buf_len = 0; }
            while (i + 48 < input.len) : (i += 48) { self.round(input[i..][0..48]); }
            const remaining_bytes = input[i..];
            if (remaining_bytes.len < 16 and i >= 48) { const rem = 16 - remaining_bytes.len;
                @memcpy(self.buf[self.buf.len - rem ..], input[i - rem .. i]); }
            @memcpy(self.buf[0..remaining_bytes.len], remaining_bytes); self.buf_len = remaining_bytes.len; }''',
        'inline fn round(self: *Wyhash, input: *const [48]u8) void': '''{
            inline for (0..3) |i| { const a = read(8, input[8 * (2 * i) ..]);
                const b = read(8, input[8 * (2 * i + 1) ..]);
                self.state[i] = mix(a ^ secret[i + 1], b ^ self.state[i]); } }''',
    }
    for signature, body in bodies.items(): function(raw, signature).expect(body)
    return {**binding, 'checkedUpdateFunctions': list(bodies),
        'scope': 'complete long-key local execution and its map consumers; external byte images and local heap/frame admission remain an explicit boundary',
        'sourceAdapterFormallyVerified': False, 'localUpdateVerified': True,
        'localHeapAdmissionVerified': False, 'nativeHashProducerVerified': False}


def source_controls(lib):
    raw = (Path(lib) / 'std/hash/wyhash.zig').read_bytes()
    records = []
    for name, before, after in (
        ('seed', b'seed ^ mix(seed ^ secret[0], secret[1])', b'seed ^ mix(seed ^ secret[1], secret[0])'),
        ('initial-copy', b'self.state[2] = self.state[0];', b'self.state[2] = 0;'),
        ('count', b'self.total_len += input.len;', b'self.total_len = input.len;'),
        ('append', b'self.buf[self.buf_len..][0..input.len]', b'self.buf[0..input.len]'),
        ('fill-round', b'self.round(&self.buf);', b''),
        ('loop-boundary', b'while (i + 48 < input.len)', b'while (i + 48 <= input.len)'),
        ('loop-stride', b'(i += 48)', b'(i += 47)'),
        ('suffix-source', b'input[i - rem .. i]', b'input[0..rem]'),
        ('suffix-destination', b'self.buf[self.buf.len - rem ..]', b'self.buf[0..rem]'),
        ('length', b'self.buf_len = remaining_bytes.len;', b'self.buf_len = 0;'),
        ('round-secret', b'a ^ secret[i + 1]', b'a ^ secret[i]')):
        require(before in raw, 'missing update source mutation: ' + name)
        try: source_binding(lib, raw.replace(before, after, 1))
        except (ValueError, local.inputs.search.probe.ADMISSION.storage.Unsupported) as error:
            records.append({'mutation': name, 'rejection': str(error)})
        else: raise ValueError('accepted changed native update: ' + name)
    return records


def controls(output, env, lean):
    directory = ROOT / 'lean/Compiler/Extraction'
    source = 'import Compiler.Extraction.WyhashBufferTests\nimport Compiler.Extraction.WyhashHashVectors\n'
    for name in ('WyhashUpdate.lean', 'WyhashHash.lean', 'ExpressionMapWyhash.lean'):
        source += without_imports((directory / name).read_text()) + '\n'
    fixture = without_imports((directory / 'WyhashHashTests.lean').read_text())
    records = [mutation_check(output, 'wyhash-hash-unchanged', source + fixture, True, env, lean)]
    # Mutate the executable definitions with their concrete semantic witnesses.
    # Rechecking a false general proof can exhaust elaborator recursion while
    # printing a huge unification failure, masking the decisive digest rejection.
    # The unchanged control, statement/axiom audit and fresh replay check all
    # general proofs; no proof body is replaced with an axiom or sorry here.
    update = without_imports((directory / 'WyhashUpdate.lean').read_text())
    model = ('import Compiler.Extraction.WyhashBufferTests\nimport Compiler.Extraction.WyhashHashVectors\n' +
             update.split('def ByteAt (', 1)[0])
    model += update[update.index('def initialCells ('):update.index('theorem initFields_eq (')]
    model += '\nend Compiler.Extraction.WyhashUpdate\n'
    model += without_imports((directory / 'WyhashHash.lean').read_text()).split('theorem updates_verified (', 1)[0]
    model += '\nend Compiler.Extraction.WyhashHash\n'
    witnesses = fixture.split('namespace ' + GRAPH + 'MapWyhashTests', 1)[0]
    for name, before, after in (
        ('seed', 'seed ^^^ mix (seed ^^^ secret0) secret1', 'seed ^^^ mix (seed ^^^ secret0) secret0'),
        ('count', 'BitVec.ofNat 64 (total.toNat + view.length)', 'BitVec.ofNat 64 view.length'),
        ('append', '0 length view.length cells', '0 0 view.length cells'),
        ('fill-round', 'let cells ← round .buffer 0 cells', 'let cells ← .ok cells'),
        ('round-secret', '(a ^^^ secret index)', '(a ^^^ secret 0)'),
        ('loop-boundary', 'if index + 48 < view.length then do', 'if index + 48 ≤ view.length then do'),
        ('loop-stride', 'loop source view (index + 48) cells', 'loop source view (index + 47) cells'),
        ('suffix-source', '(index - (16 - remaining)) (48 - (16 - remaining))', '0 (48 - (16 - remaining))'),
        ('length', 'store cells 48 (BitVec.ofNat 64 remaining)', 'store cells 48 0'),
        ('swallow-fault', 'WyhashBuffer.run cells\n', '.ok ((WyhashBuffer.run cells).toOption.getD 0)\n')):
        require(model.count(before) == 1, 'missing or ambiguous hash execution mutation: ' + name)
        records.append(mutation_check(output, 'wyhash-hash-' + name, model.replace(before, after, 1) + witnesses, False, env, lean))
    return checked_controls(output, records)
