"""Audit complete post-hash probing and its immediate publication consumer.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import hashlib
import json
from pathlib import Path
import native_map_candidate_checks as candidates
from native_map_key_checks import GRAPH, BUCKETS, require, telescope, expressions
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check
from check_zig_air_memory_proofs import without_imports
from check_word_swap import ROOT
from build_toolchain import digest, run

MODULE = 'Compiler.Extraction.ExpressionMapProbeTests'
MAP, TABLE, ADMISSION = candidates.MAP, candidates.tables.TABLE, candidates.ADMISSION
PROBE, TESTS = MAP + 'Probe.', GRAPH + 'MapProbeTests.'
CORE = ('Power.positive', 'mask_exact', 'start_exact', 'advance_exact', 'start_bound', 'slot_bound', 'slot_zero',
        'slot_next', 'slot_split', 'slot_covers', 'remember_exact', 'passed_zero', 'remembered_zero',
        'Passed.succ', 'Remembered.succ', 'loop_lookup', 'loop_verified', 'run_verified', 'Routing.empty',
        'Passed.nonfree', 'Completed.absent', 'get_hashed_verified', 'exhausted_full', 'Completed.vacancy',
        'Canonical.of_ready', 'metadata_published', 'Canonical.published', 'nonfree_published', 'Routing.published',
        'Invariant.room', 'Invariant.of_ready', 'Invariant.published')
REGRESSIONS = ('masked_wrap', 'source_hash_parts', 'first_probe', 'second_probe', 'repeated_from_initialized_owner', 'exhausted_remembers_first',
               'exhausted_lookup_absent', 'earliest_tombstone_selected', 'free_before_tombstone_stops',
               'invalid_unused_byte_rejected', 'non_power_capacity_rejected')
CLAIMS = [PROBE + n for n in CORE] + [TESTS + n for n in REGRESSIONS]
CLAIMS += [candidates.CANDIDATE + n for n in ('run_unfold', 'inspect_metadata', 'inspect_of_run', 'inspect_verified')]
CLAIMS += [BUCKETS + 'Entry.Completed.metadata_load', GRAPH + 'Facts.query_view',
           GRAPH + 'Facts.lookup_hashed', GRAPH + 'Facts.probe_then_publish']
# Full reviewed definitions bind the native operations and the admission/result
# predicates, including their arguments. Presence of a constant alone is not
# enough to exclude a vacuous implication or a rebound post-state.
DEFINITIONS = {'Compiler.Extraction.ExpressionMap.Probe.Power': 'c0529d3e8c2b2484fedba5a367d949bc4a5253bc7b25b42ebea74dfbbd85c7f7',
    'Compiler.Extraction.ExpressionMap.Probe.mask': '657292c5382e6dd80452063b9f250fe37381c940f04d067eda15771cb0717293',
    'Compiler.Extraction.ExpressionMap.Probe.fingerprint': '86b80076412c0bfbe348e6fce14096ae0068987ba6b83b2e8b8348460e1ee32c',
    'Compiler.Extraction.ExpressionMap.Probe.start': '00fcdb3250537b51e0c587c7bd7a845c96526ccea9f9383eaafa2bfc4fe5c2a7',
    'Compiler.Extraction.ExpressionMap.Probe.advance': '23853b111d24da1e8095915a8bf878bab069058f24d7489945ba0494a2e61b5b',
    'Compiler.Extraction.ExpressionMap.Probe.remember': 'a4812933b84a7b9ea8e6497f453fad12e8142f4f2a4bbe0c108c578641137bc8',
    'Compiler.Extraction.ExpressionMap.Probe.select': 'f93fb99b9aa8ee385372457036b33ba4b404786b7fa929674e4eddca594a373d',
    'Compiler.Extraction.ExpressionMap.Probe.loop': 'a627c05c1e7ddf556db048cbb3b4a193a2a5ebe051c6c20c14948e7b1d285745',
    'Compiler.Extraction.ExpressionMap.Probe.lookupLoop': '2c8b397f805e050e22de5ebe1cf3cac7fd2c8faa6839223a891f11b4122f7a0a',
    'Compiler.Extraction.ExpressionMap.Probe.run': '88fcf280b820e55a00b3dfb85dbbf636cd6115ab0ca8904c48e00bb566f21ba3',
    'Compiler.Extraction.ExpressionMap.Probe.getHashed': 'f60ae014d8550274605d70ec2b0154f5f6c4b420676eaaccdc84e43940151e8b',
    'Compiler.Extraction.ExpressionMap.Probe.Passed': '1389d3ff223009f12f2fc4cd1d0c9f9e5c90acd00b60fb893274650020c2e3ee',
    'Compiler.Extraction.ExpressionMap.Probe.Remembered': 'cc3a287e89d5a00fb303ec45cd6aa92421a592129f2190173268507726b35031',
    'Compiler.Extraction.ExpressionMap.Probe.Completed': '3dee394d0c8d893f75e9e3456177faa17b97549d5f65c32d8a7e3bcd8f014074',
    'Compiler.Extraction.ExpressionMap.Probe.Routing.mk': '63217d670235a052ef4dbed0c00800a2988921962e0a99dcaaf1a69cdc90a3d1',
    'Compiler.Extraction.ExpressionMap.Probe.Canonical': '349297620921eafa9d31f9f66bcdd503a627683a2b146d9cd8cb824923e277fa',
    'Compiler.Extraction.ExpressionMap.Probe.Invariant.mk': '26e987719e10a7f2db4476d635bb4f33a2d4188614dec464a88185140d4c0751',
    'Compiler.Extraction.ExpressionMap.Candidate.inspect': '5535bf63ba0ed5e91101ae4b2e0fa9d8ba5c8f1eb23d8eac2b9dc87324649fcf'}
STATEMENTS = {'Compiler.Extraction.ExpressionMap.Probe.run_verified': 'ab206f8449694a5b1910751775ebbba30251d8108f6cff3952fa72a398c50545',
    'Compiler.Extraction.ExpressionMap.Probe.Completed.absent': 'bf3b18ecdfa78197d4ee167ebd26158bd2f7b0a92fda2db8cd2be6dadf0849ea',
    'Compiler.Extraction.ExpressionMap.Probe.get_hashed_verified': '082e2462acc08f0b6fe27a7b595c03c448b7d0f1ea45c2425092de35d717df92',
    'Compiler.Extraction.ExpressionMap.Probe.Completed.vacancy': 'aeec40efbb083e66fcfa4812407ced8e913a919210d45e7816785d911b9fc077',
    'Compiler.Extraction.ExpressionMap.Probe.Invariant.of_ready': 'fa54975316541d8c1dbb4fc100d12069b40587c21cf6d2f3291e5992f0235250',
    'Compiler.Extraction.ExpressionMap.Probe.Invariant.published': 'a4d3fe99ed147de227a74add7fd7c448dad4e1ef11d22fee3011a048b0b86a1f',
    'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.Facts.lookup_hashed': 'acfa77044bae14dec94d23d0859d61944c01f0d6c29a72c20c5b1888e7cb4813',
    'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.Facts.probe_then_publish': '5ed650f012819f1061f8ecd72e0df4b3952d6f60817b3c171e34ddc8e42a1c11'}


def encoded_digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def audit_interfaces(records):
    require(len(records) == len(DEFINITIONS) and {r['name'] for r in records} == set(DEFINITIONS), 'probe definition inventory changed')
    for record in records:
        require(encoded_digest(record) == DEFINITIONS[record['name']], 'unreviewed probe definition: ' + record['name'])


def interfaces(output, env, lean):
    directory = output / 'probe-interfaces'; directory.mkdir()
    records = expressions.interface_export(directory, env, lean, MODULE, tuple(DEFINITIONS))
    audit_interfaces(records)
    controls = []
    for record in records:
        bad = copy.deepcopy(records)
        next(r for r in bad if r['name'] == record['name'])['type']['root'] = 0
        try: audit_interfaces(bad)
        except ValueError as error: controls.append({'name': record['name'], 'rejection': str(error)})
        else: raise ValueError('accepted corrupted probe definition')
    return {'sha256': digest(directory / 'interfaces.json'), 'checked': list(DEFINITIONS), 'controls': controls}


def audit(rows):
    indexed = {row['theorem']: row for row in rows}
    dependencies = {
        candidates.CANDIDATE + 'inspect_verified': {candidates.CANDIDATE + 'run_verified', candidates.CANDIDATE + 'inspect_of_run'},
        PROBE + 'loop_verified': {candidates.CANDIDATE + 'inspect_verified', PROBE + 'Passed.succ', PROBE + 'Remembered.succ'},
        PROBE + 'run_verified': {PROBE + 'loop_verified', PROBE + 'passed_zero', PROBE + 'remembered_zero'},
        PROBE + 'get_hashed_verified': {PROBE + 'run_verified', PROBE + 'loop_lookup', PROBE + 'Completed.absent'},
        PROBE + 'Completed.vacancy': {PROBE + 'exhausted_full', PROBE + 'Passed.nonfree'},
        PROBE + 'Invariant.published': {TABLE + 'Binding.after_new_slot', TABLE + 'publication_count', PROBE + 'Routing.published', PROBE + 'Canonical.published'},
        GRAPH + 'Facts.query_view': {candidates.SCAN + 'byte_length_bound', candidates.tables.BASE + 'OwnedCall.Caller.Custody.good'},
        GRAPH + 'Facts.lookup_hashed': {GRAPH + 'Facts.query_view', PROBE + 'get_hashed_verified'},
        GRAPH + 'Facts.probe_then_publish': {GRAPH + 'Facts.query_view', PROBE + 'run_verified', PROBE + 'Completed.absent',
            PROBE + 'Completed.vacancy', GRAPH + 'Facts.publish_selected_new', PROBE + 'Invariant.published', TABLE + 'EntryView.of_live'},
        TESTS + 'repeated_from_initialized_owner': {GRAPH + 'Facts.probe_then_publish', GRAPH + 'Facts.lookup_hashed', PROBE + 'Invariant.of_ready'},
    }
    for name, required in dependencies.items():
        require(required <= set(indexed[name]['dependencies']), 'probe lost composition: ' + name + ': ' + str(required - set(indexed[name]['dependencies'])))
    for name in CLAIMS:
        if not name.startswith(TESTS):
            require(not any(part.endswith('Tests') for dep in indexed[name]['dependencies'] for part in dep.split('.')), 'probe core depends on fixture')
    wanted = ['σ', 'safety', 'allocator', 'owner', 'capacity', 'data', 'before', 'rows', 'facts', 'hashes', 'place',
              'receiver', 'bucket', 'bucketCapacity', 'available', 'embedded', 'inv', 'room', 'key', 'owned', 'id', 'aligned', 'custody']
    fields, lets, _, _ = telescope(indexed[GRAPH + 'Facts.probe_then_publish']['statement'])
    require(list(fields) == wanted and not lets, 'probe consumer gained an assumed slot, absence or successful execution')
    for name, expected in STATEMENTS.items():
        require(encoded_digest(indexed[name]['statement']) == expected, 'probe changed original inputs or actual result: ' + name)
    return {'checkedDependencies': sorted(dependencies), 'checkedStatements': list(STATEMENTS),
            'postHashProbeDerived': True, 'absenceAndVacancyDerived': True, 'publicationMaintainsRouting': True,
            'nativeHashProducerVerified': False, 'replacementRetirementVerified': False}


def audit_controls(rows):
    records = []
    for name in STATEMENTS:
        bad = copy.deepcopy(rows)
        next(r for r in bad if r['theorem'] == name)['statement']['root'] = 0
        try: audit(bad)
        except ValueError as error: records.append({'name': name, 'rejection': str(error)})
        else: raise ValueError('accepted corrupted probe statement')
    return records


def source_binding(lib, **overrides):
    binding = candidates.source_binding(lib, **overrides)
    return {**binding, 'reviewedFunctions': binding['reviewedFunctions'] +
            ['HashMap.getOrPutAssumeCapacityAdapted', 'Metadata.isTombstone', 'Metadata.takeFingerprint'],
            'postHashProbeVerified': True, 'nativeHashProducerVerified': False,
            'scope': 'post-hash loop and new-slot publication; native hash, capacity reads, size-zero prefix and replacement remain separate'}


def source_controls(lib):
    native = (Path(lib) / 'std/hash_map.zig').read_bytes()
    records = []
    for before, after in ((b'(idx + 1) & mask', b'(idx + 2) & mask'),
                          (b'limit -= 1;', b'limit -= 2;'),
                          (b'first_tombstone_idx == self.capacity()', b'first_tombstone_idx != self.capacity()'),
                          (b'first_tombstone_idx < self.capacity()', b'first_tombstone_idx > self.capacity()'),
                          (b'metadata[0].isTombstone()', b'metadata[0].isFree()')):
        require(before in native, 'missing native probe mutation')
        try: source_binding(lib, native=native.replace(before, after, 1))
        except (ValueError, ADMISSION.storage.Unsupported) as error:
            records.append({'mutation': before.decode(), 'rejection': str(error)})
        else: raise ValueError('accepted changed native probe source')
    return records


def controls(output, env, lean):
    directory = ROOT / 'lean/Compiler/Extraction'
    source = 'import Compiler.Extraction.ExpressionMapCandidateInspection\nimport Compiler.Extraction.ExpressionMapCandidateMemory\nimport Compiler.Extraction.ExpressionMapTableTests\n'
    for name in ('Index', 'Prefix', 'Loop', 'Routing', 'Vacancy', 'Publication', 'Invariant', 'Memory'):
        source += without_imports((directory / ('ExpressionMapProbe' + name + '.lean')).read_text()) + '\n'
    fixture = without_imports((directory / 'ExpressionMapProbeTests.lean').read_text())
    # Keep negative controls on the general proofs and concrete arithmetic
    # witnesses. A poisoned dependent fixture can fail elaboration before its
    # semantic assertion; that is not an acceptable negative verdict.
    witnesses = '''
example : Compiler.Extraction.ExpressionMap.Probe.advance 8 7 = 0 := by decide +kernel
example : Compiler.Extraction.ExpressionMap.Probe.start 8 15 = 7 := by decide +kernel
example : Compiler.Extraction.ExpressionMap.Probe.fingerprint (93 <<< 57) = 93 := by decide +kernel
'''
    records = [mutation_check(output, 'probe-unchanged', source + fixture + witnesses, True, env, lean)]
    for name, before, after in (
        ('wrong-step', 'BitVec.ofNat 64 index + 1', 'BitVec.ofNat 64 index + 2'),
        ('wrong-mask', '(capacity - 1)', '(capacity - 2)'),
        ('last-tombstone', 'first == capacity.toNat && bits == 1', 'bits == 1'),
        ('skip-last-slot', 'source capacity.toNat (start', 'source (capacity.toNat - 1) (start'),
        ('wrong-fingerprint', 'hash >>> 57', 'hash >>> 56'),
        ('ignore-tombstone', 'if first < capacity.toNat then first else index', 'if first < capacity.toNat then index else index'),
        ('wrong-countdown', 'Table.count capacity bucket state + available.toNat', 'Table.count capacity bucket state + available.toNat + 1'),
    ):
        require(before in source, 'missing probe mutation: ' + name)
        records.append(mutation_check(output, 'probe-' + name, source.replace(before, after, 1) + witnesses, False, env, lean))
    return checked_controls(output, records)


def check_observation(value):
    snapshots = ('wrapped', 'tombstone', 'reused', 'exhausted', 'recycled')
    ADMISSION.fields(value, ('schema', 'arch', 'backend', 'hashes', *snapshots, 'hit', 'missed', 'hit_comparisons',
                            'miss_comparisons', 'reuse_index', 'recycle_index', 'found_existing'), 'probe')
    require(value['schema'] == 'oksolc.expression-map-probe.v1' and value['arch'] == 'aarch64' and value['backend'] == 'stage2_llvm', 'unsupported probe profile')
    hashes = value['hashes']
    require(type(hashes) is list and len(hashes) == 4 and all(type(h) is int and 0 <= h < 2**64 for h in hashes), 'invalid native hashes')
    require(all(h & 7 == 7 and h >> 57 == hashes[0] >> 57 for h in hashes), 'missing wrap/fingerprint collision')
    fp = 128 + (hashes[0] >> 57)
    expected = (([fp] + [0]*6 + [fp], 2, 4), ([fp] + [0]*6 + [1], 1, 5),
                ([fp] + [0]*6 + [fp], 2, 4), ([1]*7 + [fp], 1, 5), ([fp] + [1]*6 + [fp], 2, 4))
    for name, (metadata, size, available) in zip(snapshots, expected):
        snapshot = value[name]; ADMISSION.fields(snapshot, ('metadata', 'size', 'available'), name)
        require(type(snapshot['metadata']) is list and all(type(b) is int for b in snapshot['metadata']) and
                snapshot['metadata'] == metadata, 'wrong probe metadata: ' + name)
        require(type(snapshot['size']) is int and snapshot['size'] == size and type(snapshot['available']) is int and
                snapshot['available'] == available, 'wrong probe counters: ' + name)
    require(value['missed'] is None and value['found_existing'] is False, 'wrong absence or insertion branch')
    for field, expected in (('hit', 53), ('hit_comparisons', 1), ('miss_comparisons', 1), ('reuse_index', 7), ('recycle_index', 0)):
        require(type(value[field]) is int and value[field] == expected, 'wrong probe result: ' + field)
    return value


def capture(output, env):
    records, controls = [], []
    for mode in ('Debug', 'ReleaseSafe', 'ReleaseFast'):
        binary = output / ('buckets-' + mode); name = 'probe-' + mode
        run(output, name, [binary, 'probe'], cwd=ROOT, env=env)
        raw = (output / (name + '.stdout')).read_bytes()
        require(len(raw) < 8192 and not (output / (name + '.stderr')).read_bytes(), 'unbounded or noisy probe capture')
        value = check_observation(json.loads(raw))
        records.append({'mode': mode, 'binarySha256': digest(binary), 'observationSha256': digest(output / (name + '.stdout')), 'observed': value})
        for field, changed in (('hit', None), ('missed', 37), ('found_existing', True), ('reuse_index', 1),
                               ('recycle_index', 7), ('miss_comparisons', 2)):
            bad = copy.deepcopy(value); bad[field] = changed
            try: check_observation(bad)
            except ValueError as error: controls.append({'mode': mode, 'field': field, 'rejection': str(error)})
            else: raise ValueError('accepted corrupted probe observation')
    return {'captures': records, 'observationControls': controls, 'nativeHashProducerVerified': False}
