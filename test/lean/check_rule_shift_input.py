#!/usr/bin/env python3
"""Native evaluation-order controls for the four selected shift literals.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import ctypes
import hashlib
from pathlib import Path

import check_rule_max_exponent as shared
import extract_rule_shift_input as admission
from build_toolchain import digest, run, write_json
from capture import source_files


def native_cases(output, library):
    native = ctypes.CDLL(str(library))
    function = native.shift_input
    function.argtypes = [ctypes.POINTER(shared.Observation), ctypes.c_uint32]
    function.restype = ctypes.c_uint32
    cases, sentinel = [], 0xA5A5A5A5
    for site in range(4):
        for operand, replacement in ((3, 37), (0, 0xFFFFFFFF), (0xFFFFFFFF, 0)):
            for mutate in (0, 1):
                for fail_at in range(3):
                    inputs = [sentinel, 7, operand, sentinel] if site < 2 else [sentinel, operand, 7, sentinel]
                    observation = shared.Observation(fail_at, mutate, replacement, 80, 99, 42, 13, 0, 0, 0,
                        (ctypes.c_uint64 * 4)(2 if site == 0 else 4, 0, 0, 0),
                        (ctypes.c_uint32 * 4)(*inputs),
                        (shared.Event * 4)(*(shared.Event(*([sentinel] * 6)) for _ in range(4))))
                    returned = function(ctypes.byref(observation), site)
                    count = fail_at or 2
                    changed = mutate and fail_at != 1
                    expected_input = inputs.copy()
                    expected_input[2 if site < 2 else 1] = replacement if changed else operand
                    loaded = replacement if changed and site != 0 else operand
                    operands = [loaded, 80] if site == 0 else [80, loaded]
                    pointers = [ctypes.addressof(observation) + shared.Observation.input_words.offset + i * 4 for i in range(4)]
                    raw = [{name: getattr(event, name) for name, _ in shared.Event._fields_} for event in observation.events]
                    observed_events = [
                        {**event, 'pointer': 'separate-live-array' if event['pointer'] > 0 and event['pointer'] not in pointers else 'invalid-array'}
                        if i == 1 and count == 2 else event for i, event in enumerate(raw)]
                    expected_events = [dict(opcode=256, first=1 if site == 0 else 2, second=sentinel, length=0, pointer=0, alignment=0)]
                    expected_events += [dict(opcode=28 if site == 3 else 27, first=operands[0], second=operands[1], length=2,
                                             pointer='separate-live-array', alignment=0)] if count == 2 else []
                    expected_events += [{name: sentinel for name, _ in shared.Event._fields_} for _ in range(4 - count)]
                    actual = dict(returned=returned, error=observation.returned_error, calls=observation.call_count,
                                  growth=observation.graph_growth, input=list(observation.input_words), events=observed_events)
                    expected = dict(returned=0 if fail_at else 99, error=int(bool(fail_at)), calls=count,
                                    growth=count - int(bool(fail_at)), input=expected_input, events=expected_events)
                    cases.append(dict(site=admission.SITES[site][0], operand=operand, replacement=replacement, mutate=mutate,
                                      failAt=fail_at, actual=actual, expected=expected, rawEvents=raw))
    path = output / 'shift-observations.json'
    write_json(path, cases)
    if any(case['actual'] != case['expected'] for case in cases):
        raise ValueError('native shift literal observation mismatch')
    return {'cases': len(cases), 'sha256': digest(path), 'librarySha256': digest(library)}


def check(zig, output, lib=None):
    lib = lib or zig.parent / 'lib'
    output.mkdir(parents=True, exist_ok=False)
    report = {'status': 'failed', 'scope': 'native constructor order controls; input mutation is not graph correspondence',
              'nativeGraphCorrespondenceVerified': False, 'recursiveInductionVerified': False, 'modes': {}}
    sources = source_files(shared.SOURCE, shared.SOURCES)
    try:
        report['pythonInputs'], report['leanInputs'] = shared.python_inputs(), shared.lean_check.source_inputs()
        report['admission'] = admission.check()
        run(output, 'version', [zig, 'version'], cwd=shared.ROOT)
        version = (output / 'version.stdout').read_text().strip()
        if version != '0.17.0':
            raise ValueError('native shift controls require Zig 0.17.0')
        report['compiler'] = {'path': str(zig), 'sha256': digest(zig), 'version': version}
        library_inputs = lambda: {str(path.relative_to(lib)): digest(path) for path in sorted(lib.rglob('*.zig'))}
        report['zigLibDir'], report['zigLibraryInputs'] = str(lib), library_inputs()
        if not report['zigLibraryInputs']:
            raise ValueError('native Zig library inputs are absent')
        report['sourceInputs'] = {name: hashlib.sha256(data).hexdigest() for name, data in sources.items()}
        for name, data in sources.items():
            path = output / 'sources' / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        for mode in ('Debug', 'ReleaseSafe', 'ReleaseFast'):
            directory = output / mode
            directory.mkdir()
            library = directory / 'shift-input.dylib'
            run(directory, 'build', [zig, 'build-lib', '--zig-lib-dir', lib, '-dynamic', '-fllvm', '-fno-incremental', '-fstrip', '-O' + mode,
                output / 'sources' / shared.SOURCE.name, '--global-cache-dir', output / 'global-cache',
                '--cache-dir', directory / 'cache', '-femit-bin=' + str(library)], cwd=shared.ROOT)
            report['modes'][mode] = {'shift': native_cases(directory, library),
                                     'maxExponentRegression': shared.native_cases(directory, library)}
            write_json(output / 'report.json', report)
        if (sources != source_files(shared.SOURCE, shared.SOURCES) or digest(zig) != report['compiler']['sha256'] or
                report['zigLibraryInputs'] != library_inputs() or
                report['pythonInputs'] != shared.python_inputs() or report['leanInputs'] != shared.lean_check.source_inputs()):
            raise ValueError('native shift inputs changed during execution')
        report['status'] = 'passed'
    finally:
        write_json(output / 'report.json', report)
    print('Native shift inputs and max-exponent regressions passed in all three modes.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--zig', type=Path, required=True)
    parser.add_argument('--zig-lib-dir', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    check(args.zig.resolve(), args.output.resolve(), args.zig_lib_dir.resolve() if args.zig_lib_dir else None)
