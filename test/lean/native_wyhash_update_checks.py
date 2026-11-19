"""Bind complete update execution while keeping general refinement open.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from pathlib import Path
import json
import native_wyhash_refinement_checks as refinement

from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check, kernel_rejection
from check_zig_air_memory_proofs import without_imports
from check_word_swap import ROOT
from build_toolchain import digest, run
from capture import read_json
from generate import captured_path
from generate_hash_update import render

BYTE = 'Compiler.ZigAir.Memory.ByteRange.'
CALL = 'Compiler.ZigAir.AggregateCall.'
TEST = 'Compiler.ZigAir.WyhashUpdateAirTests.'
CLAIMS = [BYTE + n for n in ('copyByte_valid', 'copyLoop_valid', 'copy_valid')]
CLAIMS += [CALL + 'Invocation.' + n for n in ('resume_add', 'finished_unique')]
CLAIMS += [BYTE + 'Tests.' + n for n in ('valid_fixture', 'reads_original_integer_leaves',
    'fault_retains_initialized_prefix', 'call_primitive_keeps_fault_state', 'alias_and_permissions_reject',
    'empty_skips_access', 'array_load_and_bitcast_read_original_bytes', 'assertion_failure_is_terminal')]
CLAIMS += [TEST + n for n in ('buffered', 'assertion_body_both_outcomes', 'block_boundaries_short', 'block_boundaries_middle', 'block_boundaries_long', 'fills_existing_buffer',
    'missing_input_retains_total_and_prefix', 'stack_oom_is_explicit', 'suspension_keeps_locals')]
DEFINITION_NAMES = [BYTE + n for n in ('byte', 'read', 'copyByte', 'copyLoop', 'destination', 'source', 'copy')]
DEFINITION_NAMES += [CALL + n for n in ('Program.mk', 'Invocation.state', 'Invocation.finish',
    'Invocation.resume', 'Program.start', 'Program.runFuel')]
DEFINITION_NAMES += ['Compiler.ZigAir.GeneratedWyhashUpdate.' + n for n in ('assertion', 'update')]
DEFINITION_NAMES += [TEST + n for n in ('execute', 'agrees', 'matchesChunks')]
STATEMENT_NAMES = CLAIMS[:5]
# Full exported terms are reviewed and pinned before acceptance.
DEFINITIONS = {'Compiler.ZigAir.Memory.ByteRange.byte': 'd92a7a0e05e910ff924e4a231869aec299168f7962050524cbf07e3899cc2c42',
 'Compiler.ZigAir.Memory.ByteRange.read': '5d420e054b402edb26fc82d090074118a152544b4b3acf8cdbac45c7f59ea859',
 'Compiler.ZigAir.Memory.ByteRange.copyByte': 'c1996981d341fa109681e507c70e20cd5a6461e597b3763c29118a71a20f17f6',
 'Compiler.ZigAir.Memory.ByteRange.copyLoop': 'b96eeef2aaa56bc8fd48ddd373ed2d1e41c7db44a940bba5a21067fd6ab2ba95',
 'Compiler.ZigAir.Memory.ByteRange.destination': '3c77c63542d9528d171e41c4017c6b4645689e56588981a3c244b80281bbefc0',
 'Compiler.ZigAir.Memory.ByteRange.source': '4361064529548ac02408d80b0e1e7a1d231f9b4f7a8369f9805338a1a84875ee',
 'Compiler.ZigAir.Memory.ByteRange.copy': 'ecb2b741b656f31bb19651db3aa03ff0bd4075854e6e34e4b4743a9d18e04ada',
 'Compiler.ZigAir.AggregateCall.Program.mk': '91dba46b1bb95b31e0572c00d516d4d298c52221ac865433544ff9c84c9ddd09',
 'Compiler.ZigAir.AggregateCall.Invocation.state': '6457ee016f03b84324a5de8f60b436230fbb29abecf841e3de2751915110bf3b',
 'Compiler.ZigAir.AggregateCall.Invocation.finish': '758e45b08a19528e34c01cc67f2db70104a2560e9343f35e62d57849e17fb018',
 'Compiler.ZigAir.AggregateCall.Invocation.resume': '22b03fbc7a797ece83e4d5b19ae58f7784945fa820cb4dc88fd71ea296f96c9d',
 'Compiler.ZigAir.AggregateCall.Program.start': '31368a3e6f20d436d84ab5abfc16954429aed405037a8e4a5e7b57b4649b3ceb',
 'Compiler.ZigAir.AggregateCall.Program.runFuel': 'e8fa9b36a04eaadb3b775634710b381107c2efebb46e4bc4b9eb664adf29ab85',
 'Compiler.ZigAir.GeneratedWyhashUpdate.assertion': '9eeeeb24fe19cf33207728b38a960b97e2d05b73b59a217442c65b46ce517cdf',
 'Compiler.ZigAir.GeneratedWyhashUpdate.update': 'e2c70f1003ff4d99e9af38bb6cc250d88c2a512f710a0ffb8115f4646f70f67b',
 'Compiler.ZigAir.WyhashUpdateAirTests.execute': '834f02cfb4c34440b0de6a1d2030cd693499e59e526470d048d2733777319205',
 'Compiler.ZigAir.WyhashUpdateAirTests.agrees': '942b5d61220d72076eb74bf87b18f0357b2666c474c556f484168dc13db6a5a9',
 'Compiler.ZigAir.WyhashUpdateAirTests.matchesChunks': '7780968bec15ff1fa648f9470634fa7d98b54589df324493182f4e51e370bb44'}
STATEMENTS = {'Compiler.ZigAir.Memory.ByteRange.copyByte_valid': '43a0be155d7e8180e4017f3eec2697c465006f9439700b363060333ca643d980',
 'Compiler.ZigAir.Memory.ByteRange.copyLoop_valid': '2d2e775e9239cfe724c966b47e7871fde7b8d5b8eecd1ff03fdb7d09a3f53a6b',
 'Compiler.ZigAir.Memory.ByteRange.copy_valid': 'c65ca3dcd18fae37e5966d34df392fcfdbacc2a3696334a4bbb7d84aeac9d579',
 'Compiler.ZigAir.AggregateCall.Invocation.resume_add': '9a29b0cbc7eca3a0d4d35fe9c72f14985407c91f12b46bc19df2a4a14a354bdc',
 'Compiler.ZigAir.AggregateCall.Invocation.finished_unique': '08799b2d9459aa79b98a8f2ac19fe145e2866f76dcb33514633fa440918bb202'}

CLAIMS += refinement.CLAIMS
DEFINITION_NAMES += refinement.DEFINITION_NAMES
DEFINITIONS.update(refinement.DEFINITIONS)


def execution_regressions(output, env, lean):
    source = output / 'update-sequences.lean'
    source.write_text('''import Compiler.ZigAir.WyhashUpdateAirTests
import Lean
open Compiler.ZigAir.WyhashUpdateAirTests Compiler.Extraction Lean in
#eval IO.println (Json.arr (WyhashHash.Tests.vectors.zipIdx.map fun ((sizes, _), index) =>
  Json.mkObj [("lengths", toJson sizes),
    ("matched", toJson (matchesChunks initial (WyhashHash.Tests.chunks index 0 sizes)))]).toArray).compress
''')
    run(output, 'update-sequences', [lean, '-DwarningAsError=true', source], cwd=ROOT / 'lean', env=env)
    actual = json.loads((output / 'update-sequences.stdout').read_text())
    from native_wyhash_hash_checks import LENGTHS
    if actual != [{'lengths': sizes, 'matched': True} for sizes in LENGTHS]:
        raise ValueError('complete captured update disagrees with the existing native input matrix')
    return {'sequences': 14, 'updates': 70, 'status': 'matched', 'kernelProof': False,
            'observationsSha256': digest(output / 'update-sequences.stdout')}


def bind_capture(report_path, lib):
    report = read_json(report_path)
    if (report.get('status') != 'captured' or report.get('captureComplete') is not True or
            report['objects']['ordinary'] != report['objects']['captured']):
        raise ValueError('update capture incomplete or native object changed')
    selected = []
    for name, source in (('hash.wyhash.Wyhash.update', 'hash/wyhash.zig'), ('debug.assert', 'debug.zig')):
        entry = report['functions'][name]
        path = captured_path(report_path, entry)
        record = read_json(path)
        if (digest(path) != entry['sha256'] or record['name'] != name or record['sourceFile'] != source or
                record['sourceSha256'] != digest(Path(lib) / 'std' / source)):
            raise ValueError('update or assertion source/capture identity changed')
        selected.append(record)
    generated, scope = render(*selected)
    committed = ROOT / 'lean/Compiler/ZigAir/GeneratedWyhashUpdate.lean'
    if generated.encode() != committed.read_bytes():
        raise ValueError('captured complete update differs from committed execution')
    return {**scope, 'status': 'bound', 'generatedSha256': digest(committed),
        'airSha256': report['functions'][selected[0]['name']]['sha256'],
        'assertAirSha256': report['functions'][selected[1]['name']]['sha256'],
        'generalUpdateRefinementVerified': False, 'consumedByLookupPublication': False,
        'sourceAdapterFormallyVerified': False}


def audit(rows, encoded_digest, require):
    refined = refinement.audit(rows, encoded_digest, require)
    indexed = {r['theorem']: r for r in rows}
    require(set(STATEMENTS) == set(STATEMENT_NAMES), 'incomplete update execution statement pins')
    for name, expected in STATEMENTS.items():
        require(encoded_digest(indexed[name]['statement']) == expected, 'update execution statement changed: ' + name)
        require(not any('Tests' in d for d in indexed[name]['dependencies']), 'update core depends on fixtures')
    return {'checkedStatements': list(STATEMENTS), 'completeUpdateTranslated': True, 'bufferedRefinement': refined,
            'generalUpdateRefinementVerified': False, 'consumedByLookupPublication': False}


def controls(output, env, lean):
    directory = ROOT / 'lean/Compiler/ZigAir'
    generated = without_imports((directory / 'GeneratedWyhashUpdate.lean').read_text())
    fixture = without_imports((directory / 'WyhashUpdateAirTests.lean').read_text())
    prefix = ('import Compiler.ZigAir.AggregateExecution\nimport Compiler.Extraction.WyhashUpdate\nimport Compiler.Extraction.WyhashHashVectors\n'
              'deriving instance DecidableEq for Except\n')
    records = [mutation_check(output, 'wyhash-update-unchanged', prefix + generated + fixture, True, env, lean)]
    setup = fixture.split('theorem buffered :', 1)[0]
    edits = (
        ('omit-copies', None, None, 'agrees initial (bytes 4) = true'),
        ('wrong-round-xor', '.bitXor', '.bitAnd', 'agrees initial (bytes 49) = true'),
        ('assert-fallthrough', '.unreachable', '(.copy (.constant (.value (.scalar .unit))))',
         'GeneratedWyhashUpdate.assertion.run [.value (.scalar (.bool false))] {} = '
         '(.error (.scalar .illegalBehavior), {})'),
    )
    import re
    for name, before, after, proposition in edits:
        if name == 'omit-copies':
            changed, count = re.subn(r'\(\.copyBytes \(\.local \d+\) \(\.local \d+\)\)',
                '(.primitive (.copy (.constant (.value (.scalar .unit)))))', generated)
            if count != 4:
                raise ValueError('update copy mutation sites changed')
        else:
            if before not in generated:
                raise ValueError('missing update mutation site: ' + name)
            changed = generated.replace(before, after)
        check = (setup + '\nend Compiler.ZigAir.WyhashUpdateAirTests\n'
                 'open Compiler.ZigAir Compiler.ZigAir.WyhashUpdateAirTests\n' + kernel_rejection(proposition))
        records.append(mutation_check(output, 'wyhash-update-' + name, prefix + changed + check, False, env, lean))
    # Exercise the reached failure state independently of the success fixtures.
    model = without_imports((directory / 'MemoryByteRange.lean').read_text()).split('theorem copyByte_valid', 1)[0]
    model += '\nend Compiler.ZigAir.Memory.ByteRange\n'
    checks = without_imports((directory / 'MemoryByteRangeTests.lean').read_text()).split('theorem call_primitive', 1)[0]
    checks = checks.replace('open AggregateAir\n', '') + '\nend Compiler.ZigAir.Memory.ByteRange.Tests\n'
    imports = 'import Compiler.ZigAir.MemoryScalarBytes\nimport Compiler.ZigAir.MemoryStackFrame\n'
    records.append(mutation_check(output, 'byte-copy-unchanged', imports + model + checks, True, env, lean))
    before = '| .ok after => copyLoop after source target (index + 1) count'
    after = ('| .ok after =>\n      let copied := copyLoop after source target (index + 1) count\n'
             '      match copied.1 with\n      | .error fault => (.error fault, state)\n      | .ok () => copied')
    if model.count(before) != 1:
        raise ValueError('byte-copy failure mutation site changed')
    records.append(mutation_check(output, 'byte-copy-rollback-on-fault',
        imports + model.replace(before, after) + checks, False, env, lean))
    records += refinement.controls(output, env, lean)
    return checked_controls(output, records)
