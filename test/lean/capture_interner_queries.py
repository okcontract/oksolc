#!/usr/bin/env python3
"""Compare all defined query shapes with the pinned native implementation.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from pathlib import Path

import check_compiler
from common import decode_json
from check_word_swap import ROOT
from build_toolchain import VERSION, check_checkout, digest, run, source_identity, text, write_json

PROBE = ROOT / 'test/lean/interner_queries.zig'
NONDETERMINISTIC = frozenset((0xf1, 0xf2, 0xf4, 0xfa, 0xf0, 0xf5, 0x5a, 0x58,
                            0x59, 0x31, 0x47, 0x3b, 0x3f, 0x3e, 0x3d))


def expected_cases():
    rows = []
    for kind in range(14):
        opcodes = list(range(256)) if kind in (1, 13) else []
        if kind != 1:
            opcodes.append(None)
        for opcode in opcodes:
            result = ('assemblyException' if kind == 13 else
                      'nondeterministic' if opcode in NONDETERMINISTIC else 'deterministic')
            rows.append({'kind': kind, 'instruction': opcode, 'result': result})
    return rows


def check_profile(record, mode):
    if (not isinstance(record, dict) or set(record) != {'schema', 'zigVersion', 'mode', 'backend', 'cases'} or
            record['schema'] != 'oksolc.interner-query-observations.v1' or
            record['zigVersion'] != VERSION or record['mode'] != mode or record['backend'] != 'stage2_llvm' or
            not isinstance(record['cases'], list)):
        raise ValueError('unsupported native query profile')
    for row in record['cases']:
        if (not isinstance(row, dict) or set(row) != {'kind', 'instruction', 'result'} or
                type(row['kind']) is not int or not 0 <= row['kind'] < 14 or
                (row['instruction'] is not None and (type(row['instruction']) is not int or not 0 <= row['instruction'] < 256)) or
                type(row['result']) is not str):
            raise ValueError('malformed native query observation')
    if record['cases'] != expected_cases():
        raise ValueError('native query outcomes or complete case inventory changed')


def capture(output, compiler, tree):
    output.mkdir(parents=True, exist_ok=False)
    report = {'schema': 'oksolc.interner-query-capture.v1', 'status': 'failed', 'jobs': 4,
              'scope': '525 defined scalar query observations per build mode; no native field/memory refinement proof.'}
    try:
        compiler, tree = Path(compiler).resolve(), Path(tree).resolve()
        check_checkout(output, tree, 'zig-source')
        report['compiler'] = {'path': str(compiler), 'sha256': digest(compiler)}
        report['zigLibrary'] = {'path': str(tree / 'lib'), **source_identity(tree / 'lib')}
        report['inputs'] = check_compiler.snapshot()
        report['probeSha256'] = digest(PROBE)
        run(output, 'version', [compiler, 'version'])
        if text(output, 'version') != VERSION:
            raise ValueError('native query probe requires Zig 0.17.0')
        records = []
        report['profiles'] = records
        for mode in ('Debug', 'ReleaseSafe', 'ReleaseFast'):
            executable = output / ('interner-queries-' + mode)
            run(output, 'build-' + mode, [compiler, 'build-exe', '-j4', '--zig-lib-dir', tree / 'lib', '-fllvm',
                '-O', mode, '--dep', 'compiler', '-Mroot=' + str(PROBE), '-O', mode,
                '-Mcompiler=' + str(ROOT / 'src/modules.zig'), '--cache-dir', ROOT / '.zig-cache',
                '--global-cache-dir', output / 'global-cache', '-femit-bin=' + str(executable)], cwd=ROOT)
            run(output, 'probe-' + mode, [executable], cwd=ROOT)
            raw = (output / ('probe-' + mode + '.stdout')).read_bytes()
            entry = {'mode': mode, 'binarySha256': digest(executable),
                     'profileSha256': digest(output / ('probe-' + mode + '.stdout')), 'accepted': False}
            records.append(entry)
            write_json(output / 'report.json', report)
            if len(raw) > 1024 * 1024:
                raise ValueError('native query profile exceeds admission bound')
            profile = decode_json(raw.decode())
            entry['profile'] = profile
            write_json(output / 'report.json', report)
            check_profile(profile, mode)
            if (output / ('build-' + mode + '.stderr')).read_bytes() or (output / ('probe-' + mode + '.stderr')).read_bytes():
                raise ValueError('native query probe has unreviewed diagnostics')
            entry['accepted'] = True
        if (digest(compiler) != report['compiler']['sha256'] or
                source_identity(tree / 'lib') != {k: report['zigLibrary'][k] for k in ('files', 'sha256')} or
                check_compiler.snapshot() != report['inputs'] or digest(PROBE) != report['probeSha256']):
            raise ValueError('native query inputs changed during capture')
        report['status'] = 'passed'
    finally:
        write_json(output / 'report.json', report)
    return {'status': 'passed', 'reportSha256': digest(output / 'report.json'), 'casesPerMode': 525,
            'modes': [r['mode'] for r in records], 'nativeFieldRefinementVerified': False}
