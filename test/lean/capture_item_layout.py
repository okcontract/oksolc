#!/usr/bin/env python3
"""Capture the actual nominal AssemblyItem extent with the pinned Zig library.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from pathlib import Path
import json

import check_compiler
from check_word_swap import ROOT
from build_toolchain import VERSION, check_checkout, digest, run, source_identity, text, write_json
from generate_item_layout import generate, OUTPUT

PROBE = ROOT / 'test/lean/assembly_item_layout.zig'


def check_profile(record, expected):
    if generate(record) != expected:
        raise ValueError('native AssemblyItem extent differs from the generated nominal type')


def capture(output, compiler, tree):
    output.mkdir(parents=True, exist_ok=False)
    report = {'schema': 'oksolc.item-layout-capture.v1', 'status': 'failed', 'jobs': 4,
              'scope': 'Allocation extent only; no item field, allocator implementation or native compiler preservation proof.'}
    try:
        compiler, tree = Path(compiler).resolve(), Path(tree).resolve()
        check_checkout(output, tree, 'zig-source')
        report['compiler'] = {'path': str(compiler), 'sha256': digest(compiler)}
        report['zigLibrary'] = {'path': str(tree / 'lib'), **source_identity(tree / 'lib')}
        report['inputs'] = check_compiler.snapshot()
        report['probeSha256'] = digest(PROBE)
        expected = OUTPUT.read_bytes()
        report['modelSha256'] = digest(OUTPUT)
        run(output, 'version', [compiler, 'version'])
        if text(output, 'version') != VERSION:
            raise ValueError('native layout probe requires pinned Zig 0.17.0')
        records = []
        report['profiles'] = records
        for mode in ('Debug', 'ReleaseSafe', 'ReleaseFast'):
            executable = output / ('item-layout-' + mode)
            command = [compiler, 'build-exe', '-j4', '--zig-lib-dir', tree / 'lib', '-fllvm',
                       '-O', mode, '--dep', 'compiler', '-Mroot=' + str(PROBE),
                       '-O', mode, '-Mcompiler=' + str(ROOT / 'src/modules.zig'),
                       '--cache-dir', ROOT / '.zig-cache', '--global-cache-dir', output / 'global-cache',
                       '-femit-bin=' + str(executable)]
            run(output, 'build-' + mode, command, cwd=ROOT)
            run(output, 'probe-' + mode, [executable], cwd=ROOT)
            raw = (output / ('probe-' + mode + '.stdout')).read_bytes()
            entry = {'mode': mode, 'binarySha256': digest(executable), 'profileSha256': digest(output / ('probe-' + mode + '.stdout')),
                     'accepted': False}
            records.append(entry)
            # Retain raw output and the case observation before every assertion.
            write_json(output / 'report.json', report)
            if len(raw) > 16384:
                raise ValueError('native layout profile exceeds admission limit')
            profile = json.loads(raw)
            entry['profile'] = profile
            if profile.get('mode') != mode:
                raise ValueError('native layout build mode mismatch')
            check_profile(profile, expected)
            if (output / ('build-' + mode + '.stderr')).read_bytes() or (output / ('probe-' + mode + '.stderr')).read_bytes():
                raise ValueError('native layout capture has unreviewed diagnostics')
            entry['accepted'] = True
        if (digest(compiler) != report['compiler']['sha256'] or source_identity(tree / 'lib') !=
                {k: report['zigLibrary'][k] for k in ('files', 'sha256')} or
                check_compiler.snapshot() != report['inputs'] or digest(PROBE) != report['probeSha256'] or OUTPUT.read_bytes() != expected):
            raise ValueError('native layout inputs changed during capture')
        report['status'] = 'passed'
    finally:
        write_json(output / 'report.json', report)
    return {'status': 'passed', 'reportSha256': digest(output / 'report.json'), 'modes': [r['mode'] for r in records],
            'layoutBound': True, 'nativeFieldsVerified': False, 'nativeAllocatorVerified': False}
