"""Check partial local transfer and the Wyhash finalization tail.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import json
from pathlib import Path
import native_hash_input_checks as inputs
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check
from check_zig_air_memory_proofs import without_imports
from check_word_swap import ROOT
from build_toolchain import digest, run

require = inputs.require
MODULE = 'Compiler.Extraction.WyhashLocalTests'
LOCAL, MEMORY = 'Compiler.Extraction.WyhashLocal.', 'Compiler.ZigAir.Memory.'
CLAIMS = [MEMORY + 'Cells.' + n for n in ('transferScalar_valid', 'lookup_typed', 'transferScalar_eq')]
CLAIMS += [LOCAL + n for n in ('geometry', 'shallowCopy_verified', 'nativeOps_eq', 'mum_verified',
    'final2_verified', 'finishTail_verified', 'shallowCopy_finishTail')]
CLAIMS += [LOCAL + 'Tests.' + n for n in ('core_valid', 'core_represents', 'missing_copy', 'absent_reads',
    'old_values_irrelevant', 'wide_product', 'undefined_transfer', 'defined_transfer', 'invalid_source_rejected',
    'invalid_target_rejected', 'malformed_rejected', 'zero_width_rejected', 'missing_state_rejected',
    'missing_length_rejected', 'transfer_frames_other')]
DEFINITIONS = {'Compiler.ZigAir.Memory.Cells.transferScalar': '376c2d8ab40556404e110dad1e59652233a714379a989fafbe84feaab639acef',
 'Compiler.Extraction.WyhashLocal.objectType': '28180622ff9f2cb0087e668eb0a55f47076f8e035cdfe2b162973faeea8e4245',
 'Compiler.Extraction.WyhashLocal.word': 'd26a624d4cd4f61a4069e72e85afd378d3ecb459309bc94b38fbfb1497f326f9',
 'Compiler.Extraction.WyhashLocal.put': '11f3b7619916e653b65b77647d1e6b056ae2c336be48b1310db15984f5f363cd',
 'Compiler.Extraction.WyhashLocal.core': '814464909a91390d940aaf826a367be19a923923c8a6fab41c001a59e9b3cb4c',
 'Compiler.Extraction.WyhashLocal.copyFields': '8306d8031edd8ce95ed4eafaea55750b44bbff72e55771aa0db93d053a3885b7',
 'Compiler.Extraction.WyhashLocal.shallowCopy': 'f793f62427c5c2c6e75180b63ddbd918101a1e83bab3a805a894bfef1e56c511',
 'Compiler.Extraction.WyhashLocal.readWord': '4c3eac8f988b98a99c031097cfdde99656c3b352bdd5c49aa42eb58a5dd73745',
 'Compiler.Extraction.WyhashLocal.writeWord': 'b982772b9c692431ef1f91ed885e37547f3b901cb8f05554099c6f62de48c4dd',
 'Compiler.Extraction.WyhashLocal.product': '32e23118957a2a5d19d4302ad75cbc77e49d94762cca3f5ff17c7175ca498c59',
 'Compiler.Extraction.WyhashLocal.lo': 'b57a329f23b09603d194b24f5322457d66ba368778199c8fefb0466406d1c5fc',
 'Compiler.Extraction.WyhashLocal.hi': '64745ac8e93dbdb228ca0f6b187f95569404cb77118f4b22d83666fa08c776ec',
 'Compiler.Extraction.WyhashLocal.mix': 'a96a7e253c2ad3d3b6b1c7fd7e70cc8840a6e6b26b8fd483b461678e2834371a',
 'Compiler.Extraction.WyhashLocal.secret0': '8fd5b72d479ccbb076b744d97ce9cae4129fac092d11579eb06153a2f532cb54',
 'Compiler.Extraction.WyhashLocal.secret1': '6d63d5a9b9414507678cade976d9526b15679e77ed906aa0e3ead718cbf066fe',
 'Compiler.Extraction.WyhashLocal.nativeOps': '13a91bc1e6dcb9c3f960f32965e839f6e093e79448398c9c1a2302dabc29d8f7',
 'Compiler.Extraction.WyhashLocal.localOps': '5ac6b41ba5e084bb383b737ea28001af980579bbac83b38ddc21c30735fc619d',
 'Compiler.Extraction.WyhashLocal.mum': '5fba446533f15b51e5434b4e2c37f2ec018c82e81889693959aa07efeded35a5',
 'Compiler.Extraction.WyhashLocal.xorOperands': '01cb84c3841e81a5bcd35930bd997851148425cef04a1a924cc2ecdf4be7797b',
 'Compiler.Extraction.WyhashLocal.finishProduct': '2918a79c29b56c49bb96016b30beeb74618f943f39a13513c56eeeb8d2eb3ccf',
 'Compiler.Extraction.WyhashLocal.final2': 'c870472427770e0f7e2eed84ce5efa5302c3f33b1f7ac727e08a068f2bcf4861',
 'Compiler.Extraction.WyhashLocal.overwriteTail': 'baeee520b69b996c079fb7fedf9adb0cd843dc150cd73d4941da95ab1f4e6b1f',
 'Compiler.Extraction.WyhashLocal.finishTail': '8c49a5a52892ad211bd2a033c260fff5031ce4145a1e7f3f0054e094d9c183a3',
 'Compiler.Extraction.WyhashLocal.result': '662731b23723a605e650a59081e06e35d228e73883ff12b73c83be3824b65e77'}
STATEMENTS = {'Compiler.ZigAir.Memory.Cells.transferScalar_eq': '8858e4ebc2f22bc7a865b5cca054df66909bf8efb0a6e5d097f20e587ba078da',
 'Compiler.ZigAir.Memory.Cells.transferScalar_valid': 'e31599d4e432053c4e755fe538d05b7abce6c2f41af3803520c4d544e654b6a7',
 'Compiler.Extraction.WyhashLocal.shallowCopy_verified': '25bbf01ce6b33ca911a450a6c9fc4749a1f0134dc10478df3e58140953cc5904',
 'Compiler.Extraction.WyhashLocal.nativeOps_eq': '8259281ed2d4c72794b7bf86c33ff3817a098b61220f271795911c3fb64a86f4',
 'Compiler.Extraction.WyhashLocal.mum_verified': 'ed9ced5bdc3daf911424ac73441fbc056cb066954a2d87385f149d2a3f3d4d83',
 'Compiler.Extraction.WyhashLocal.final2_verified': '3100b15afa79bb270adc08932e0f3b0ff28113088527be1881a4f6efd7cea814',
 'Compiler.Extraction.WyhashLocal.shallowCopy_finishTail': '6e298c6a3d10a531ab4411b2c6095d62e07690c1a4d220bfe162d180c4c00e2b'}
LENGTHS = list(range(1, 49, 4))
MASK = 2**64 - 1
SECRET0, SECRET1 = 0xa0761d6478bd642f, 0xe7037ed1a0b428db


def interfaces(output, env, lean):
    return inputs.search.interfaces(output, env, lean, module=MODULE, definitions=DEFINITIONS, prefix='wyhash-local')


def audit(rows):
    indexed = {r['theorem']: r for r in rows}
    dependencies = {
        MEMORY + 'Cells.transferScalar_valid': {MEMORY + 'Cells.write_preserves_valid', MEMORY + 'Cells.forget_valid'},
        LOCAL + 'shallowCopy_verified': {MEMORY + 'Cells.transferScalar_eq'},
        LOCAL + 'nativeOps_eq': {LOCAL + 'write_word_native', LOCAL + 'geometry'},
        LOCAL + 'shallowCopy_finishTail': {LOCAL + 'shallowCopy_verified', LOCAL + 'nativeOps_eq', LOCAL + 'final2_verified'},
        LOCAL + 'Tests.old_values_irrelevant': {LOCAL + 'shallowCopy_finishTail'},
    }
    for name, expected in dependencies.items():
        require(expected <= set(indexed[name]['dependencies']), 'local transfer lost its producer/consumer: ' + name)
    for name in CLAIMS:
        if not name.startswith(LOCAL + 'Tests.'):
            require(not any(part.endswith('Tests') for dep in indexed[name]['dependencies'] for part in dep.split('.')), 'local core depends on a fixture')
    for name, expected in STATEMENTS.items():
        require(inputs.search.probe.encoded_digest(indexed[name]['statement']) == expected, 'changed local transfer statement: ' + name)
    fields, lets, _, _ = inputs.telescope(indexed[LOCAL + 'shallowCopy_finishTail']['statement'])
    require(list(fields) == ['source', 'oldA', 'oldB', 's0', 's1', 's2', 'total', 'a', 'b', 'valid', 'represented'] and not lets,
            'copy/finalization acquired an initialization or operation premise')
    return {'checkedDependencies': sorted(dependencies), 'checkedStatements': list(STATEMENTS),
            'partialScalarTransferVerified': True, 'copiedCoreFinalizationTailVerified': True,
            'nativeHashProducerVerified': False, 'nativeBufferReadsVerified': False, 'localHeapAdmissionVerified': False}


def audit_controls(rows):
    records = []
    for name in STATEMENTS:
        bad = copy.deepcopy(rows)
        next(r for r in bad if r['theorem'] == name)['statement']['root'] = 0
        try: audit(bad)
        except ValueError as error: records.append({'name': name, 'rejection': str(error)})
        else: raise ValueError('accepted changed local transfer statement')
    return records


def source_binding(lib, native=None):
    binding = inputs.source_binding(lib)
    raw = (Path(lib) / 'std/hash/wyhash.zig').read_bytes() if native is None else native
    storage = inputs.search.probe.ADMISSION.storage
    function = storage.function
    prefix = raw.split(b'pub fn init(seed: u64)', 1)[0].decode()
    expected = 'const std = @import("std"); pub const Wyhash = struct {\n        const secret = [_]u64{ 0xa0761d6478bd642f, 0xe7037ed1a0b428db, 0x8ebc6af09c88c6e3, 0x589965cc75374cc3, };\n        a: u64, b: u64, state: [3]u64, total_len: usize, buf: [48]u8, buf_len: usize,'
    require(storage.lex(prefix) == storage.lex(expected), 'changed Wyhash core fields or secrets')
    bodies = {
        'inline fn shallowCopy(self: *Wyhash) Wyhash': '''{ return .{
            .a = self.a, .b = self.b, .state = self.state, .total_len = self.total_len,
            .buf = undefined, .buf_len = undefined, }; }''',
        'inline fn mum(a: *u64, b: *u64) void': '''{
            const x = @as(u128, a.*) *% b.*;
            a.* = @as(u64, @truncate(x)); b.* = @as(u64, @truncate(x >> 64)); }''',
        'inline fn mix(a_: u64, b_: u64) u64': '''{
            var a = a_; var b = b_; mum(&a, &b); return a ^ b; }''',
        'inline fn final2(self: *Wyhash) u64': '''{
            self.a ^= secret[1]; self.b ^= self.state[0]; mum(&self.a, &self.b);
            return mix(self.a ^ secret[0] ^ self.total_len, self.b ^ secret[1]); }''',
        'inline fn final1(self: *Wyhash, input_lb: []const u8, start_pos: usize) void': '''{
            std.debug.assert(input_lb.len >= 16); std.debug.assert(input_lb.len - start_pos <= 48);
            const input = input_lb[start_pos..]; var i: usize = 0;
            while (i + 16 < input.len) : (i += 16) {
                self.state[0] = mix(read(8, input[i..]) ^ secret[1], read(8, input[i + 8 ..]) ^ self.state[0]); }
            self.a = read(8, input_lb[input_lb.len - 16 ..][0..8]);
            self.b = read(8, input_lb[input_lb.len - 8 ..][0..8]); }''',
    }
    for signature, body in bodies.items(): function(raw, signature).expect(body)
    return {**binding, 'checkedWyhashFunctions': list(bodies),
            'scope': 'typed local scalar transfer, shallow copy and final1 tail assignments through final2; buffer reads, loops and local heap admission remain open',
            'sourceAdapterFormallyVerified': False, 'nativeHashProducerVerified': False}


def source_controls(lib):
    raw = (Path(lib) / 'std/hash/wyhash.zig').read_bytes()
    records = []
    for before, after in ((b'0xa0761d6478bd642f', b'0xa0761d6478bd642e'), (b'.a = self.a,', b'.a = self.b,'), (b'.buf = undefined,\n            .buf_len = undefined,', b'.buf = undefined,\n            .buf_len = 0,'),
                          (b'@truncate(x >> 64)', b'@truncate(x >> 63)'), (b'self.b ^= self.state[0]', b'self.b ^= self.state[1]'),
                          (b'self.a = read(8, input_lb[input_lb.len - 16 ..][0..8]);', b'self.a = read(8, input_lb[input_lb.len - 8 ..][0..8]);')):
        require(before in raw, 'missing local source mutation')
        try: source_binding(lib, raw.replace(before, after, 1))
        except (ValueError, inputs.search.probe.ADMISSION.storage.Unsupported) as error:
            records.append({'mutation': before.decode(), 'rejection': str(error)})
        else: raise ValueError('accepted changed native local finalization')
    return records


def controls(output, env, lean):
    directory = ROOT / 'lean/Compiler'
    source = 'import Compiler.Extraction.ExpressionMapHashInputTests\n'
    for name in ('ZigAir/MemoryScalarTransfer.lean', 'Extraction/WyhashLocal.lean'):
        source += without_imports((directory / name).read_text()) + '\n'
    fixture = without_imports((directory / 'Extraction/WyhashLocalTests.lean').read_text())
    records = [mutation_check(output, 'wyhash-local-unchanged', source + fixture, True, env, lean)]
    for name, before, after in (
        ('retain-undefined', '.ok (target.forget targetOffset layout.bytes)', '.ok target'),
        ('invent-undefined', '.ok (target.forget targetOffset layout.bytes)', '.ok (target.set targetOffset (.scalar (.int false 64 0)))'),
        ('copy-wrong-length', 'copyFields source [0, 8, 16, 24, 32, 40] []', 'copyFields source [0, 8, 16, 24, 32, 32] []'),
        ('wrong-high-half', '(value >>> 64).truncate 64', '(value >>> 63).truncate 64'),
        ('skip-b-overwrite', 'ops.write cells 1 b\n', '.ok cells\n'),
        ('premature-a-read', 'def overwriteTail (ops : Ops) (cells : Cells) (a b : BitVec 64) : Except Fault Cells := do\n',
         'def overwriteTail (ops : Ops) (cells : Cells) (a b : BitVec 64) : Except Fault Cells := do\n  let _ ← ops.read cells 0\n'),
        ('initialized-copy-buffer', 'copyFields source [0, 8, 16, 24, 32, 40] []', 'copyFields source [0, 8, 16, 24, 32, 40] [(48, word 0)]'),
        ('swallow-missing-read', 'let some value := cells.lookup offset | .error .uninitialized', 'let some value := cells.lookup offset | .ok 0'),
    ):
        require(before in source, 'missing local proof mutation: ' + name)
        records.append(mutation_check(output, 'wyhash-local-' + name, source.replace(before, after, 1) + fixture, False, env, lean))
    return checked_controls(output, records)


def mix(a, b):
    value = a * b
    return (value & MASK) ^ (value >> 64)


def finalize(state, total, initialized, length):
    buf = initialized[:length] if length >= 16 else initialized[48 - (16 - length):] + initialized[:length]
    offset = 0 if length >= 16 else 16 - length
    read = lambda at: int.from_bytes(bytes(buf[at:at + 8]), 'little')
    s0 = state[0] ^ state[1] ^ state[2]
    i = 0
    while i + 16 < length:
        s0 = mix(read(offset + i) ^ SECRET1, read(offset + i + 8) ^ s0)
        i += 16
    product = (read(len(buf) - 16) ^ SECRET1) * (read(len(buf) - 8) ^ s0)
    answer = mix((product & MASK) ^ SECRET0 ^ total, (product >> 64) ^ SECRET1)
    return answer


def expected_case(length, index):
    state = [2**63 + index, 0x1122334455667788 + index, 0x99aabbccddeeff00 + index]
    total = length + 48 if length < 41 else length
    initialized = [(i * 17 + index * 29 + 3) % 256 if i < length or (length < 16 and i >= 48 - (16 - length)) else None for i in range(48)]
    answer = finalize(state, total, initialized, length)
    return {'length': length, 'total': total, 'state': state, 'initialized': initialized,
            'native_hash': answer, 'repeated_hash': answer, 'changed_a_hash': answer, 'changed_b_hash': answer, 'source_retained': True}


def check_observation(value, *, lengths=LENGTHS, schema="oksolc.wyhash-local.v1"):
    fields = inputs.search.probe.ADMISSION.fields
    fields(value, ('schema', 'endian', 'usize_bytes', 'size', 'alignment', 'offsets', 'cases'), 'Wyhash local')
    require(value['schema'] == schema and value['endian'] == 'little', 'wrong local profile')
    for name, expected in (('usize_bytes', 8), ('size', 104), ('alignment', 8)):
        require(type(value[name]) is int and value[name] == expected, 'wrong local layout: ' + name)
    require(type(value['offsets']) is list and all(type(n) is int for n in value['offsets']) and value['offsets'] == [0, 8, 16, 40, 56, 48], 'wrong named local fields')
    cases = value['cases']
    require(type(cases) is list and len(cases) == len(lengths), 'incomplete local cases')
    for index, (case, length) in enumerate(zip(cases, lengths)):
        expected = expected_case(length, index)
        fields(case, tuple(expected), 'Wyhash local case')
        for key in ('length', 'total', 'native_hash', 'repeated_hash', 'changed_a_hash', 'changed_b_hash'):
            require(type(case[key]) is int and 0 <= case[key] <= MASK, 'invalid local integer: ' + key)
        require(type(case['state']) is list and all(type(n) is int and 0 <= n <= MASK for n in case['state']), 'invalid core words')
        require(type(case['initialized']) is list and all(n is None or type(n) is int and 0 <= n < 256 for n in case['initialized']), 'invalid initialized-byte observation')
        require(case['source_retained'] is True and case == expected, 'native local finalization differs from retained core/byte observations')
    return value


def capture(output, env, *, command="wyhash-local", checker=check_observation):
    captures, controls = [], []
    for mode in ('Debug', 'ReleaseSafe', 'ReleaseFast'):
        binary = output / ('buckets-' + mode); name = command + '-' + mode
        run(output, name, [binary, command], cwd=ROOT, env=env)
        raw = (output / (name + '.stdout')).read_bytes()
        require(len(raw) < 65536 and not (output / (name + '.stderr')).read_bytes(), 'unbounded/noisy local capture')
        observed = checker(json.loads(raw))
        captures.append({'mode': mode, 'binarySha256': digest(binary), 'observationSha256': digest(output / (name + '.stdout')), 'observed': observed})
        for key in ('native_hash', 'changed_a_hash', 'changed_b_hash', 'source_retained'):
            bad = copy.deepcopy(observed); bad['cases'][0][key] = False if key == 'source_retained' else bad['cases'][0][key] ^ 1
            try: checker(bad)
            except ValueError as error: controls.append({'mode': mode, 'field': key, 'rejection': str(error)})
            else: raise ValueError('accepted changed native local observation')
    return {'captures': captures, 'observationControls': controls, 'nativeHashProducerVerified': False}
