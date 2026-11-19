"""Bind native key equality and a lookup candidate to the original table/custody.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import hashlib
import json
from pathlib import Path
import native_map_table_checks as tables
from native_map_key_checks import GRAPH, BUCKETS, require, app, path, telescope, expressions
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check
from check_zig_air_memory_proofs import without_imports
from check_word_swap import ROOT
from build_toolchain import digest, run
import extract_cache

MODULE = 'Compiler.Extraction.ExpressionMapCandidateTests'
MAP = tables.insertion.MAP
SCAN, KEY, CANDIDATE = (MAP + name + '.' for name in ('ArgumentScan', 'KeyComparison', 'Candidate'))
TESTS = GRAPH + 'MapCandidateTests.'
CLAIMS = [SCAN + n for n in ('short_offsets', 'chunk_mem', 'short_mem', 'coverage', 'difference_verified',
    'scan_verified', 'bytes_verified', 'encoded_equal', 'vector_difference', 'vectors_eq_scan', 'blocks_large',
    'different_lengths', 'empty', 'same_pointer', 'represented_alias', 'run_verified', 'byte_length_bound')]
CLAIMS += [KEY + n for n in ('entry_byte_bound', 'field_verified', 'fields_verified', 'run_verified')]
CLAIMS += [CANDIDATE + 'run_verified', GRAPH + 'Facts.lookup_candidate']
CLAIMS += [TESTS + n for n in ('after_repeated_publication', 'copied_hit', 'alias_hit', 'wrong_scalar_skipped',
    'wrong_fingerprint_skipped', 'exhausted_stopped', 'free_stopped', 'changed_argument_skipped',
    'short_argument_skipped', 'uninitialized_rejected', 'oversized_rejected')]
ADMISSION = tables.insertion.entries.keys.admission
LENGTHS = [0, 1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, 31, 32, 33, 65]
SIMD_SHA256 = '5a37398808b2f4fa0c8b797834a509615f774f70493deb4c8c2699ee339273cc'
# The complete reviewed kernel definitions, not just names occurring in a
# theorem. These pins reject weakened outcome predicates and rebound reads.
# Updating them requires reviewing the definitions alongside their source pins.
DEFINITIONS = {
    CANDIDATE + 'Correct': 'be4ea3ab3d5e71b34629d8ad0e2f9618c731125829eb9af05f907b2056c7f39e',
    CANDIDATE + 'run': 'c4de288fc0afc24fd4ed36496277880232ebc6d904b14768c37e3391cb29d1bc',
    KEY + 'field': '3b1d370d51f4fdc070429cea08b23234f63286e2473ec72bec479b8526b31294',
    SCAN + 'run': '96bd7984175dfa2d953d2be6dce80b2299c4de0cb975633eeb5e422758165013',
}


def audit_interfaces(records):
    require(len(records) == len(DEFINITIONS) and {r['name'] for r in records} == set(DEFINITIONS), 'candidate definition inventory changed')
    for record in records:
        actual = hashlib.sha256(json.dumps(record, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
        require(actual == DEFINITIONS[record['name']], 'unreviewed candidate definition: ' + record['name'])


def interfaces(output, env, lean):
    directory = output / 'candidate-interfaces'; directory.mkdir()
    records = expressions.interface_export(directory, env, lean, MODULE, tuple(DEFINITIONS))
    audit_interfaces(records)
    controls = []
    for record in records:
        bad = copy.deepcopy(records)
        next(r for r in bad if r['name'] == record['name'])['value']['root'] = 0
        try: audit_interfaces(bad)
        except ValueError as error: controls.append({'name': record['name'], 'rejection': str(error)})
        else: raise ValueError('accepted corrupted candidate definition')
    return {'sha256': digest(directory / 'interfaces.json'), 'checked': list(DEFINITIONS), 'controls': controls}


def source_binding(lib, *, source=None, mem=None, native=None, simd=None):
    lib = Path(lib)
    source = ADMISSION.storage.SOURCE.read_bytes() if source is None else source
    mem = (lib / 'std/mem.zig').read_bytes() if mem is None else mem
    native = (lib / 'std/hash_map.zig').read_bytes() if native is None else native
    simd = (lib / 'std/simd.zig').read_bytes() if simd is None else simd
    binding = ADMISSION.source_binding(lib, source=source, native=native)
    ADMISSION.storage.function(source, 'pub fn eql(_: @This(), left: ExpressionKey, right: ExpressionKey) bool').expect('''{
        return left.item_type == right.item_type and left.instruction == right.instruction and
          left.data == right.data and left.sequence_number == right.sequence_number and
          std.mem.eql(Id, left.arguments, right.arguments); }''')
    require(extract_cache.extract(source, extract_cache.SEMANTICS.read_bytes(), extract_cache.ITEMS.read_bytes(),
                                  extract_cache.OPCODES.read_bytes()) == extract_cache.OUTPUT.read_bytes(),
            'key equality field extraction is stale')
    # Complete files are pinned, including dispatch, sliceAsBytes, unreachable
    # fallback branches, loop bounds and target-dependent vector selection.
    # Reviewed specialization: runtime u32, unique bits, little-endian LLVM,
    # non-fuzzing, Scan.size=16. No extra SIMD or comparison host contract.
    require(hashlib.sha256(mem).hexdigest() == ADMISSION.MEM_SHA256, 'unreviewed equality/byte-view source')
    require(hashlib.sha256(simd).hexdigest() == SIMD_SHA256, 'unreviewed scan selection')
    return {**binding, 'memSha256': ADMISSION.MEM_SHA256, 'simdSha256': SIMD_SHA256,
        'reviewedFunctions': ['ExpressionKeyContext.eql', 'std.mem.eql', 'std.mem.eqlBytes', 'std.mem.sliceAsBytes',
                              'std.simd.suggestVectorLength', 'HashMap.getIndex', 'HashMap.getAdapted'],
        'scanBytes': 16, 'sourceAdapterFormallyVerified': False, 'completeProbingVerified': False}


def source_controls(lib):
    originals = {'source': ADMISSION.storage.SOURCE.read_bytes(),
                 'mem': (Path(lib) / 'std/mem.zig').read_bytes(),
                 'native': (Path(lib) / 'std/hash_map.zig').read_bytes(),
                 'simd': (Path(lib) / 'std/simd.zig').read_bytes()}
    records = []
    for field, before, after in (
        ('source', b'left.data == right.data', b'left.data != right.data'),
        ('source', b'std.mem.eql(Id, left.arguments, right.arguments)', b'true'),
        ('mem', b'if (a.len == 0 or a.ptr == b.ptr) return true;', b'if (a.len == 0 or a.ptr != b.ptr) return true;'),
        ('mem', b'(a.len / 8) * 4', b'(a.len / 8) * 8'),
        ('mem', b'0..(a.len - 1) / Scan.size', b'0..(a.len - 2) / Scan.size'),
        ('mem', b'a.len - Scan.size', b'a.len - Scan.size - 1'),
        ('native', b'metadata[0].fingerprint == fingerprint', b'metadata[0].fingerprint != fingerprint'),
        ('native', b'return self.values()[idx];', b'return self.values()[0];'),
        ('simd', b'pub fn suggestVectorLength', b'pub fn changedVectorLength'),
    ):
        raw = originals[field]
        require(before in raw, 'missing candidate source control')
        try: source_binding(lib, **{field: raw.replace(before, after, 1)})
        except (ValueError, ADMISSION.storage.Unsupported) as error:
            records.append({'field': field, 'mutation': before.decode(), 'rejection': str(error)})
        else: raise ValueError('accepted changed candidate source')
    return records


def audit(rows):
    indexed = {row['theorem']: row for row in rows}
    dependencies = {
        SCAN + 'vector_difference': {SCAN + 'encoded_equal', SCAN + 'bytes_verified', SCAN + 'difference_verified'},
        SCAN + 'run_verified': {SCAN + 'vectors_eq_scan', SCAN + 'scan_verified', SCAN + 'coverage', SCAN + 'represented_alias'},
        KEY + 'field_verified': {SCAN + 'run_verified', BUCKETS + 'Entry.Stored.keys'},
        KEY + 'run_verified': {KEY + 'fields_verified', 'Compiler.Extraction.Cache.equality_iff'},
        CANDIDATE + 'run_verified': {KEY + 'run_verified', KEY + 'entry_byte_bound', tables.TABLE + 'Binding.slots', tables.TABLE + 'EntryView.unique'},
        GRAPH + 'Facts.lookup_candidate': {CANDIDATE + 'run_verified', GRAPH + 'Facts.query_view'},
        TESTS + 'after_repeated_publication': {GRAPH + 'Facts.lookup_candidate', tables.TESTS + 'repeated_from_initialized_owner'},
    }
    for name, required in dependencies.items():
        require(required <= set(indexed[name]['dependencies']), 'candidate lost native composition: ' + name + ': ' + str(required - set(indexed[name]['dependencies'])))
    for name in CLAIMS:
        if not name.startswith(TESTS):
            require(not any(part.endswith('Tests') for dep in indexed[name]['dependencies'] for part in dep.split('.')), 'candidate core depends on fixture')
    binders = {
        SCAN + 'run_verified': ['state', 'left', 'right', 'a', 'b', 'leftRead', 'rightRead', 'bounded'],
        KEY + 'run_verified': ['state', 'capacity', 'bucket', 'index', 'query', 'stored', 'source', 'entry', 'queryRead', 'view', 'bounded'],
        CANDIDATE + 'run_verified': ['place', 'safety', 'receiver', 'state', 'capacity', 'bucket', 'index', 'remaining', 'fp', 'query', 'source', 'table', 'binding', 'inside', 'queryRead', 'bounded'],
        GRAPH + 'Facts.lookup_candidate': ['σ', 'safety', 'allocator', 'owner', 'capacity', 'data', 'before', 'rows', 'facts',
            'place', 'receiver', 'bucketCapacity', 'bucket', 'index', 'remaining', 'binding', 'inside', 'fp', 'key', 'owned', 'aligned', 'custody'],
    }
    for name, wanted in binders.items():
        value = indexed[name]['statement']; fields, _, root, scope = telescope(value)
        require(list(fields) == wanted, 'candidate gained a successful read/equality/entry premise: ' + name)
        if name != GRAPH + 'Facts.lookup_candidate': continue
        tables.binding_at(value, *fields['binding'], 'before')
        node, context = fields['custody']; custody = app(value, node, tables.BASE + 'OwnedCall.Caller.GraphCustody')
        require([expressions.named(value, a, context) for a in custody[:-1]] == ['σ', 'allocator', 'owned', 'rows'], 'query custody changed owner')
        path(value, custody[-1], context, (tables.WORLD + 'memory',), 'before')
        for label in ('bits', 'result'):
            witness = value['nodes'][app(value, root, 'Exists')[-1]]
            require(witness[:2] == ['lambda', label], 'candidate lost actual outcome')
            root = witness[4]; scope += [label]
        metadata, rest = app(value, root, 'And'); equation, correct = app(value, rest, 'And')
        equation = app(value, equation, 'Eq')
        args = app(value, equation[-2], CANDIDATE + 'run')
        tables.native_path(value, args[0], scope, 'before')
        require([expressions.named(value, a, scope) for a in args[1:-1]] == ['bucketCapacity', 'bucket', 'index', 'remaining', 'fp', 'key'], 'candidate changed native inputs')
        require(expressions.named(value, app(value, args[-1], 'Compiler.Extraction.Memory.Arguments.view')[0], scope) == 'owned', 'candidate reads another query')
        require(expressions.named(value, app(value, equation[-1], 'Except.ok')[-1], scope) == 'result', 'candidate discarded actual result')
        args = app(value, correct, CANDIDATE + 'Correct')
        tables.native_path(value, args[0], scope, 'before'); tables.keys_path(value, args[-3], scope, 'before')
        require([expressions.named(value, a, scope) for a in args[1:7]] == ['bucketCapacity', 'bucket', 'index', 'remaining', 'fp', 'key'], 'correctness concerns another candidate')
        require([expressions.named(value, a, scope) for a in args[-2:]] == ['bits', 'result'], 'correctness discarded native outcome')
    return {'checkedDependencies': sorted(dependencies), 'checkedStatements': sorted(binders),
            'nativeCandidateFromOriginalCustody': True, 'completeProbingVerified': False}


def audit_controls(rows):
    records = []
    for name, binder in ((SCAN + 'run_verified', 'leftRead'), (KEY + 'run_verified', 'view'),
                         (CANDIDATE + 'run_verified', 'binding'), (GRAPH + 'Facts.lookup_candidate', 'custody')):
        bad = copy.deepcopy(rows)
        value = next(r for r in bad if r['theorem'] == name)['statement']
        node = next(n for n in value['nodes'] if n[:2] == ['forall', binder])
        node[1] = 'assumed_result'
        try: audit(bad)
        except ValueError as error: records.append({'theorem': name, 'mutation': binder, 'rejection': str(error)})
        else: raise ValueError('accepted changed candidate premise')
    for constant in (CANDIDATE + 'run', CANDIDATE + 'Correct'):
        bad = copy.deepcopy(rows)
        value = next(r for r in bad if r['theorem'] == GRAPH + 'Facts.lookup_candidate')['statement']
        node = next(n for n in value['nodes'] if n[:2] == ['const', constant]); node[1] += 'Wrong'
        try: audit(bad)
        except ValueError as error: records.append({'mutation': constant, 'rejection': str(error)})
        else: raise ValueError('accepted changed candidate conclusion')
    return records


def controls(output, env, lean):
    directory = ROOT / 'lean/Compiler/Extraction'
    source = 'import Compiler.Extraction.ExpressionMapTableTests\nimport Compiler.ZigAir.MemoryWordBytes\nimport Compiler.Extraction.CacheProofs\n'
    for name in ('ArgumentScan', 'ArgumentVector', 'ArgumentEquality', 'KeyComparison', 'Candidate', 'CandidateMemory'):
        source += without_imports((directory / ('ExpressionMap' + name + '.lean')).read_text()) + '\n'
    fixture = without_imports((directory / 'ExpressionMapCandidateTests.lean').read_text())
    records = [mutation_check(output, 'candidate-unchanged', source + fixture, True, env, lean)]
    for name, before, after in (
        ('short-offset', '[0, length - 1, length / 2, length - 1 - length / 2]', '[0, length - 1, 0, 0]'),
        ('skip-tail', '++ [length - 4]', '++ []'),
        ('missing-lane', 'List.range 16', 'List.range 15'),
        ('alias-shortcut', 'left.address 0 = right.address 0 then .ok true', 'left.address 0 ≠ right.address 0 then .ok true'),
        ('ignore-length', 'left.length ≠ right.length then .ok false', 'left.length ≠ right.length then .ok true'),
        ('skip-arguments', 'ArgumentScan.run state source ⟨address.allocation, address.offset / 4, length⟩', '.ok true'),
        ('wrong-field', 'slot) stored', 'slot) (KeyFields.value query (source.address 0) slot)'),
        ('ignore-fingerprint', 'bits.toNat % 128 == fp.toNat', 'bits.toNat % 128 != fp.toNat'),
        ('exhaustion', 'remaining == 0 then return (bits, .stop)', 'remaining != 0 then return (bits, .stop)'),
        ('wrong-id', 'return .hit (BitVec.ofInt 32 id)', 'return .hit (BitVec.ofInt 32 id + 1)'),
    ):
        require(before in source, 'missing candidate mutation: ' + name)
        records.append(mutation_check(output, 'candidate-' + name, source.replace(before, after, 1), False, env, lean))
    return checked_controls(output, records)


def check_observation(value):
    ADMISSION.fields(value, ('schema', 'arch', 'backend', 'endian', 'scan_bytes', 'usize_bytes', 'unique_u32', 'fuzz', 'cases', 'collision'), 'equality')
    require(value['schema'] == 'oksolc.expression-map-equality.v1' and value['arch'] == 'aarch64' and
            value['backend'] == 'stage2_llvm' and value['endian'] == 'little', 'unsupported equality profile')
    require(type(value['scan_bytes']) is int and value['scan_bytes'] == 16 and
            type(value['usize_bytes']) is int and value['usize_bytes'] == 8 and
            value['unique_u32'] is True and value['fuzz'] is False, 'unsupported equality scan')
    require(type(value['cases']) is list and len(value['cases']) == len(LENGTHS), 'incomplete scan matrix')
    for case, length in zip(value['cases'], LENGTHS):
        ADMISSION.fields(case, ('length', 'alias_equal', 'copied_equal', 'different_length', 'changed_bytes_rejected', 'scalar_changes_rejected'), 'equality case')
        require(type(case['length']) is int and case['length'] == length and type(case['changed_bytes_rejected']) is int and
                case['changed_bytes_rejected'] == length * 4, 'wrong scan boundary or changed-byte count')
        require(case['alias_equal'] is True and case['copied_equal'] is True and case['different_length'] is False, 'wrong equality result')
        flags = case['scalar_changes_rejected']
        require(type(flags) is list and len(flags) == 4 and all(v is True for v in flags), 'wrong scalar comparison')
    collision = value['collision']
    ADMISSION.fields(collision, ('same_start', 'same_fingerprint', 'first', 'second', 'absent', 'size'), 'collision')
    require(collision['same_start'] is True and collision['same_fingerprint'] is True and collision['absent'] is None and
            all(type(collision[k]) is int and collision[k] == v for k, v in (('first', 37), ('second', 53), ('size', 2))), 'wrong colliding candidate lookup')
    return value


def capture(output, env):
    records, controls = [], []
    for mode in ('Debug', 'ReleaseSafe', 'ReleaseFast'):
        binary = output / ('buckets-' + mode); name = 'equality-' + mode
        run(output, name, [binary, 'equality'], cwd=ROOT, env=env)
        raw = (output / (name + '.stdout')).read_bytes()
        require(len(raw) < 16384 and not (output / (name + '.stderr')).read_bytes(), 'unbounded or noisy equality capture')
        value = check_observation(json.loads(raw))
        records.append({'mode': mode, 'binarySha256': digest(binary), 'observationSha256': digest(output / (name + '.stdout')), 'observed': value})
        for field, changed in (('scan_bytes', 32), ('scan_bytes', True), ('fuzz', True), ('unique_u32', False), ('cases', value['cases'][:-1])):
            bad = copy.deepcopy(value); bad[field] = changed
            try: check_observation(bad)
            except ValueError as error: controls.append({'mode': mode, 'field': field, 'rejection': str(error)})
            else: raise ValueError('accepted corrupt equality observation')
    return {'captures': records, 'observationControls': controls, 'completeProbingVerified': False}
