"""Check local Wyhash finalization from the original initialized buffer regions.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
from pathlib import Path
import native_wyhash_local_checks as local
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check
from check_zig_air_memory_proofs import without_imports
from check_word_swap import ROOT

require = local.require
MODULE = 'Compiler.Extraction.WyhashBufferTests'
BYTES = 'Compiler.ZigAir.Memory.ByteSlice.'
FINAL = 'Compiler.Extraction.WyhashFinalization.'
BUFFER = 'Compiler.Extraction.WyhashBuffer.'
CLAIMS = [BYTES + n for n in ('read_verified', 'write_verified', 'readLE_verified', 'copy_verified', 'array_geometry')]
CLAIMS += [FINAL + n for n in ('final0_verified', 'round_verified', 'loop_verified', 'tail_verified', 'finish_verified')]
CLAIMS += [BUFFER + n for n in ('buffer_geometry', 'prepare_verified', 'readLength_verified', 'run_verified')]
CLAIMS += [BUFFER + 'Tests.' + n for n in ('boundary_results', 'partial_source_valid', 'partial_source_represents',
    'partial_source_consumed', 'absent_gap', 'exact_boundary_no_reads', 'missing_suffix_rejected', 'missing_prefix_rejected',
    'wrong_buffer_type_rejected', 'oversize_rejected', 'small_key_explicit', 'missing_length_rejected',
    'absent_scratch_rejected', 'slice_bounds_rejected', 'wrong_byte_order')]
DEFINITION_NAMES = [BYTES + n for n in ('byte', 'value', 'Geometry', 'Represents', 'read', 'write', 'decode', 'readLE', 'copy')]
DEFINITION_NAMES += [FINAL + n for n in ('final0', 'round', 'loop', 'rounds', 'tail', 'finish', 'result')]
DEFINITION_NAMES += [BUFFER + n for n in ('buffer', 'scratch', 'Represents', 'inputLength', 'inputStart', 'inputBytes', 'prepare', 'readLength', 'run', 'result')]
DEFINITIONS = {'Compiler.ZigAir.Memory.ByteSlice.byte': '2d48fbde4d809c7554081d1f736b63fb8a91dd4e47fa350c5fb8b5a6ed9f71d7',
 'Compiler.ZigAir.Memory.ByteSlice.value': '8407fdabe46518bd0607222eefbd64de35e8827293043d1babaa04d6eaea989a',
 'Compiler.ZigAir.Memory.ByteSlice.Geometry': '98ff794b483247f9db768b8c7c9d2fb21e5db76b7b910e505aca1e1536501563',
 'Compiler.ZigAir.Memory.ByteSlice.Represents': 'cd2ec8403c7a96e3a8a826f279a6c8f5d8935fbf3b417514b7032515305b2830',
 'Compiler.ZigAir.Memory.ByteSlice.read': 'ac00eb67ca56f483521cd27aade8c1ebf6addbaf901f9bf54732f9bc4d279f01',
 'Compiler.ZigAir.Memory.ByteSlice.write': 'db6ec1ad0e633131822dda8dce2150c08ff2b6be1c57694cd2488c943b7c2c99',
 'Compiler.ZigAir.Memory.ByteSlice.decode': '7fb0587bb4e97af530bbe42cdcc40f8b54f4bab2149aa49c6b1ba917cca4e904',
 'Compiler.ZigAir.Memory.ByteSlice.readLE': 'c6cf9d69e76ba96ce3b66fa4dd08187fb1ebc46cadb61e9ac84eedbf32e4b818',
 'Compiler.ZigAir.Memory.ByteSlice.copy': '15885375bd772cbc425cabded7cbfe7c02a0bd8bbdc45f9ce7883eaed48a7398',
 'Compiler.Extraction.WyhashFinalization.final0': 'be3e5cb5c8fc8b41d7338d074603936b0cf518767c2c79febdb85f0fb6ba922d',
 'Compiler.Extraction.WyhashFinalization.round': '1e0cc3fb9d9dc02582d564b2d08fa46135c412e61b94ca4964df572b74e40599',
 'Compiler.Extraction.WyhashFinalization.loop': '72b523622edf2af6b3f4948f183c569d8fccc6a96efea5cf5778f3f68c5fe1f5',
 'Compiler.Extraction.WyhashFinalization.rounds': '96c053b1b2a14349578621dd0030b7fc6e21b7772fc52375322786cffdde19b5',
 'Compiler.Extraction.WyhashFinalization.tail': '942c337dde3433b42a3c199157cbf385925d9527bb3e9b4d560a2a893c091560',
 'Compiler.Extraction.WyhashFinalization.finish': 'cbe90f57e0ae76004d3af563d685af619992a2c51415959836340a8d110c14c1',
 'Compiler.Extraction.WyhashFinalization.result': '792c225fe2a2507c19b711e331d040d4956bc7fb0509cb1161693abd59bd6964',
 'Compiler.Extraction.WyhashBuffer.buffer': '3ea28e4ab402445be8e73c733c6e08369a2b38853ae17e439f6b704eecd15515',
 'Compiler.Extraction.WyhashBuffer.scratch': 'd57798a35c9261aa7b431acd405fb2220216def5476b62430cde950c9b27c5f5',
 'Compiler.Extraction.WyhashBuffer.Represents': '557febf56703dedf91a4bf35d1b8ec235ee30ec33011e81d7053a9efb740c872',
 'Compiler.Extraction.WyhashBuffer.inputLength': '4519aa80e1e4a62e213325bcbf6e37a20d126ac918767c0a3938a56043fbafb0',
 'Compiler.Extraction.WyhashBuffer.inputStart': 'b75ebc319878093536cbb3f652dcdf72cc8bd27d99b9625528b49ff83c33fd16',
 'Compiler.Extraction.WyhashBuffer.inputBytes': '5c20a94abe341e2d38f8118d1771862446800d0605081a10bbc29a3029dd63bd',
 'Compiler.Extraction.WyhashBuffer.prepare': '31b929d14e68de911ce65738b3ebc940920d8b56c356da3e7ffe03a8a29e0fa6',
 'Compiler.Extraction.WyhashBuffer.readLength': '000fae19878bca255f83ac5ffc5d5f84ebfd90764a528d839165e9f737ba81c2',
 'Compiler.Extraction.WyhashBuffer.run': 'f0e148b5aeac3d7d0f8318d3f7a83fc52f6f6185a86610137f8059d3f3ff45af',
 'Compiler.Extraction.WyhashBuffer.result': '1bde817339c08f41ee0645d2f35df8a11124a429926e72e2877a93e0d4cc13fa'}
STATEMENTS = {'Compiler.ZigAir.Memory.ByteSlice.readLE_verified': 'f552a6a8a101e85c2a88589ee7bb553dcf7d370d845171a584429be503fbf5c8',
 'Compiler.ZigAir.Memory.ByteSlice.copy_verified': '8da115d2603edac7515eed8c3be24004232c1b34380c2200a284547d4a83eba1',
 'Compiler.Extraction.WyhashFinalization.loop_verified': 'acad0c540719a5b1eb17cb2055913a9fdaf98eb7ccbd2e5a0a2240f8eb5ecb2f',
 'Compiler.Extraction.WyhashFinalization.finish_verified': '71625a388703aaf125d4d83987a408ea649c93447ba39c2865bab23a88c43802',
 'Compiler.Extraction.WyhashBuffer.prepare_verified': '2b0820ff89cafe62d9ffde452bfb70ca49d9cab48f56e0cf4d36e435fdc68637',
 'Compiler.Extraction.WyhashBuffer.run_verified': '335b953b8685698e2a54b718f10e61337c74910882465c2f1e9b20a77806558b'}


def interfaces(output, env, lean):
    require(set(DEFINITIONS) == set(DEFINITION_NAMES), 'incomplete finalization definition pins')
    return local.inputs.search.interfaces(output, env, lean, module=MODULE, definitions=DEFINITIONS, prefix='wyhash-final')


def audit(rows):
    indexed = {r['theorem']: r for r in rows}
    dependencies = {
        BYTES + 'copy_verified': {BYTES + 'read_verified', BYTES + 'write_verified'},
        FINAL + 'finish_verified': {BYTES + 'readLE_verified', FINAL + 'loop_verified', local.LOCAL + 'nativeOps_eq', local.LOCAL + 'finishTail_verified'},
        BUFFER + 'prepare_verified': {BYTES + 'copy_verified', BUFFER + 'buffer_geometry'},
        BUFFER + 'run_verified': {BUFFER + 'prepare_verified', BUFFER + 'readLength_verified', FINAL + 'finish_verified', local.LOCAL + 'shallowCopy_verified'},
        BUFFER + 'Tests.partial_source_consumed': {BUFFER + 'run_verified'},
    }
    for name, expected in dependencies.items():
        require(expected <= set(indexed[name]['dependencies']), 'finalization lost its producer/consumer: ' + name)
    for name in CLAIMS:
        if '.Tests.' not in name:
            require(not any(part.endswith('Tests') for dep in indexed[name]['dependencies'] for part in dep.split('.')), 'finalization core depends on a fixture')
    require(set(STATEMENTS) == {BYTES + 'copy_verified', BYTES + 'readLE_verified', FINAL + 'loop_verified',
        FINAL + 'finish_verified', BUFFER + 'prepare_verified', BUFFER + 'run_verified'}, 'incomplete finalization statement pins')
    for name, expected in STATEMENTS.items():
        require(local.inputs.search.probe.encoded_digest(indexed[name]['statement']) == expected, 'changed finalization statement: ' + name)
    fields, lets, _, _ = local.inputs.telescope(indexed[BUFFER + 'run_verified']['statement'])
    require(list(fields) == ['source', 'oldA', 'oldB', 's0', 's1', 's2', 'total', 'length', 'bytes', 'valid',
        'coreRead', 'lengthRead', 'bounded', 'long', 'bufferRead'] and not lets,
        'finalization acquired supplied scratch, tail words, state, or read success')
    return {'checkedDependencies': sorted(dependencies), 'checkedStatements': list(STATEMENTS),
            'localLongKeyFinalizationVerified': True, 'nativeUpdateVerified': False,
            'localHeapAdmissionVerified': False, 'nativeHashProducerVerified': False}


def audit_controls(rows):
    records = []
    for name in STATEMENTS:
        bad = copy.deepcopy(rows)
        next(r for r in bad if r['theorem'] == name)['statement']['root'] = 0
        try: audit(bad)
        except ValueError as error: records.append({'name': name, 'rejection': str(error)})
        else: raise ValueError('accepted changed finalization statement')
    return records


def source_binding(lib, native=None, memory=None):
    binding = local.source_binding(lib, native)
    raw = (Path(lib) / 'std/hash/wyhash.zig').read_bytes() if native is None else native
    mem = (Path(lib) / 'std/mem.zig').read_bytes() if memory is None else memory
    function = local.inputs.search.probe.ADMISSION.storage.function
    bodies = {
        'inline fn final0(self: *Wyhash) void': '{ self.state[0] ^= self.state[1] ^ self.state[2]; }',
        'inline fn read(comptime bytes: usize, data: []const u8) u64': '''{
            std.debug.assert(bytes <= 8); const T = @Int(.unsigned, 8 * bytes);
            return @as(u64, std.mem.readInt(T, data[0..bytes], .little)); }''',
        'pub fn final(self: *Wyhash) u64': '''{
            var input: []const u8 = self.buf[0..self.buf_len];
            var newSelf = self.shallowCopy();
            if (self.total_len <= 16) { newSelf.smallKey(input); } else {
                var offset: usize = 0; var scratch: [16]u8 = undefined;
                if (self.buf_len < 16) { const rem = 16 - self.buf_len;
                    @memcpy(scratch[0..rem], self.buf[self.buf.len - rem ..][0..rem]);
                    @memcpy(scratch[rem..][0..self.buf_len], self.buf[0..self.buf_len]);
                    input = &scratch; offset = rem; }
                newSelf.final0(); newSelf.final1(input, offset); }
            return newSelf.final2(); }''',
    }
    for signature, body in bodies.items(): function(raw, signature).expect(body)
    signature = 'pub inline fn readInt(comptime T: type, buffer: *const [@divExact(@typeInfo(T).int.bits, 8)]u8, endian: Endian) T'
    require(mem.count(signature.encode()) == 1, 'missing or duplicated native readInt')
    start = mem.index(signature.encode())
    # Restrict lexing to this complete top-level function; unrelated std.mem
    # tests contain tokens outside the deliberately bounded source adapter.
    end = mem.index(b'\n}', start) + 2
    function(mem[start:end], signature).expect('''{
        const little_val: T = @bitCast(buffer.*);
        return switch (endian) { .little => little_val, .big => @byteSwap(little_val), }; }''')
    return {**binding, 'checkedFinalizationFunctions': list(bodies) + ['std.mem.readInt'],
        'scope': 'complete long-key local finalization from original initialized buffer regions; byte-array interpretation is explicit little-endian',
        'sourceAdapterFormallyVerified': False, 'nativeUpdateVerified': False,
        'localHeapAdmissionVerified': False, 'nativeHashProducerVerified': False}


def source_controls(lib):
    raw = (Path(lib) / 'std/hash/wyhash.zig').read_bytes()
    memory = (Path(lib) / 'std/mem.zig').read_bytes()
    records = []
    for label, before, after in (
        ('scratch-suffix', b'self.buf[self.buf.len - rem ..][0..rem]', b'self.buf[0..rem]'),
        ('scratch-append', b'scratch[rem..][0..self.buf_len]', b'scratch[0..self.buf_len]'),
        ('scratch-start', b'offset = rem;', b'offset = 0;'),
        ('omit-final0', b'newSelf.final0();', b''),
        ('round-boundary', b'while (i + 16 < input.len)', b'while (i + 16 <= input.len)'),
        ('wrong-lane', b'self.state[0] ^= self.state[1] ^ self.state[2];', b'self.state[0] ^= self.state[1];'),
        ('read-endian', b'std.mem.readInt(T, data[0..bytes], .little)', b'std.mem.readInt(T, data[0..bytes], .big)'),
    ):
        require(before in raw, 'missing finalization source mutation: ' + label)
        try: source_binding(lib, raw.replace(before, after, 1))
        except (ValueError, local.inputs.search.probe.ADMISSION.storage.Unsupported) as error:
            records.append({'mutation': label, 'rejection': str(error)})
        else: raise ValueError('accepted changed native finalization: ' + label)
    before, after = b'.little => little_val,', b'.little => @byteSwap(little_val),'
    require(before in memory, 'missing readInt mutation')
    try: source_binding(lib, memory=memory.replace(before, after, 1))
    except (ValueError, local.inputs.search.probe.ADMISSION.storage.Unsupported) as error:
        records.append({'mutation': 'readInt-byte-order', 'rejection': str(error)})
    else: raise ValueError('accepted changed native readInt')
    return records


def controls(output, env, lean):
    directory = ROOT / 'lean/Compiler'
    source = 'import Compiler.Extraction.WyhashLocalTests\n'
    for name in ('ZigAir/MemoryByteSlice.lean', 'Extraction/WyhashFinalization.lean', 'Extraction/WyhashBuffer.lean'):
        source += without_imports((directory / name).read_text()) + '\n'
    fixture = without_imports((directory / 'Extraction/WyhashBufferTests.lean').read_text())
    records = [mutation_check(output, 'wyhash-final-unchanged', source + fixture, True, env, lean)]
    for name, before, after in (
        ('byte-shift', '.ok (head.zeroExtend 64 ||| (tail <<< 8))', '.ok (head.zeroExtend 64 ||| (tail <<< 7))'),
        ('copy-source', '(src + 1) (dst + 1) count after', 'src (dst + 1) count after'),
        ('scratch-tail', '(buffer (48 - rem) rem) scratch', '(buffer 0 rem) scratch'),
        ('scratch-append', 'scratch 0 rem length middle', 'scratch 0 0 length middle'),
        ('scratch-offset', '.ok (after, scratch, rem)', '.ok (after, scratch, 0)'),
        ('omit-final0', 'let cells ← final0 ops cells', 'let cells ← .ok cells'),
        ('round-boundary', 'if index + 16 < view.length - start then do', 'if index + 16 ≤ view.length - start then do'),
        ('round-stride', 'loop ops input view start (index + 16) after', 'loop ops input view start (index + 17) after'),
        ('tail-offset', 'ByteSlice.readLE input view (view.length - 16) 8\n', 'ByteSlice.readLE input view (view.length - 8) 8\n'),
        ('small-key', 'if total.toNat ≤ 16 then .error .unsupported', 'if total.toNat ≤ 16 then .ok 0'),
    ):
        require(before in source, 'missing finalization proof mutation: ' + name)
        records.append(mutation_check(output, 'wyhash-final-' + name, source.replace(before, after, 1) + fixture, False, env, lean))
    return checked_controls(output, records)


def check_observation(value):
    return local.check_observation(value, lengths=list(range(49)), schema='oksolc.wyhash-final.v1')


def capture(output, env):
    return local.capture(output, env, command='wyhash-final', checker=check_observation)
