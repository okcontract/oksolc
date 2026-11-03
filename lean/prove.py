#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Check a selected Lean module and optional theorem dependencies during development.
This command never exports a contract or publishes a source/bytecode certificate.
"""
import argparse
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

import environment as source
from common import (BuildError, DRIVER_SHA256 as COMPILE_DRIVER_SHA256, MAX_OUTPUT,
                     canonical, decode_json, invoke, publish, read_bounded)


DRIVER_SHA256 = source.file_digest(Path(__file__))
# Cumulative compiler audits now exceed 1024 declarations. Keep a finite request
# bound without dropping claims; output, timeout and process-memory limits still
# apply independently.
MAX_DECLARATIONS = 2048


# Lean/Lake preserve source locations in their text diagnostics. Keep the raw
# diagnostic too; extracting a location must never discard the original message.
FATAL = re.compile(rb'(?im)^\s*(?:PANIC\b|\[PANIC\]|uncaught exception|error:)')
LOCATION = re.compile(r'(?P<file>[^\n:]*?\.lean):(?P<line>\d+):(?P<column>\d+):')


def valid_name(value):
    return isinstance(value, str) and len(value) <= 512 and source.NAME.fullmatch(value)


def check_module(module, declarations=(), *, lean_bin=None, jobs=4, timeout=600,
                 fresh=False, profile=False, threshold_ms=100):
    artifacts = {}
    report = {'schema': 'oksolc.lean.development-check.v1', 'status': 'failed',
              'module': module, 'requestedDeclarations': list(declarations),
              'assurance': 'developmentOnly', 'artifactPublication': False,
              'wholeContractProof': False, 'emittedEvmProof': False,
              'incrementalBuild': False, 'auditedDeclarations': [],
              'freshKernelReplay': False, 'replayIncludesImports': False,
              'profileScope': 'entireSelectedModule' if profile else 'notRequested',
              'profileThresholdMs': threshold_ms if profile else None,
              'jobs': jobs, 'timeoutSecondsPerPhase': timeout, 'phases': {}}
    current = 'request'

    def phase(name, command, data=b''):
        nonlocal current
        current = name
        started = time.perf_counter()
        record = {'command': list(map(str, command)), 'status': 'failed'}
        report['phases'][name] = record
        try:
            stdout, stderr = invoke(command, data, timeout, cwd=source.LEAN_ROOT, env=env)
            artifacts[name+'.stdout.txt'] = stdout
            artifacts[name+'.stderr.txt'] = stderr
            record['status'] = 'passed'
            return stdout, stderr
        finally:
            record['seconds'] = time.perf_counter()-started

    try:
        if (not valid_name(module) or len(declarations) > MAX_DECLARATIONS or
                any(not valid_name(d) for d in declarations) or len(set(declarations)) != len(declarations)):
            raise BuildError('invalidRequest',
                             f'use a canonical module name and up to {MAX_DECLARATIONS} unique theorem names')
        if not 1 <= jobs <= 64 or timeout <= 0 or threshold_ms < 0:
            raise BuildError('invalidRequest', 'jobs must be 1..64; timeout positive; profile threshold nonnegative')
        path = source.LEAN_ROOT.joinpath(*module.split('.')).with_suffix('.lean').resolve()
        if not path.is_relative_to(source.LEAN_ROOT.resolve()) or not path.is_file():
            raise BuildError('invalidRequest', 'module must name a source file within the Lean project')
        report['sourceFile'] = str(path.relative_to(source.ROOT))
        current = 'toolchain'
        env, sysroot, tools = source.toolchain(lean_bin, jobs)
        if fresh:
            checker = sysroot/'bin/leanchecker'
            tools['leanchecker'] = {'path': str(checker), 'sha256': source.file_digest(checker)}
        report['tools'] = tools
        before = source.source_inputs()
        drivers = {name: source.file_digest(source.LEAN_ROOT/name)
                   for name in ['prove.py', 'environment.py', 'common.py']}
        if (drivers['prove.py'] != DRIVER_SHA256 or drivers['environment.py'] != source.DRIVER_SHA256
                or drivers['common.py'] != COMPILE_DRIVER_SHA256):
            raise BuildError('staleArtifact', 'proof-check driver changed after loading')
        report['buildInputs'], report['driverSha256'] = before, drivers

        def stable():
            if before != source.source_inputs():
                raise BuildError('staleArtifact', 'Lean source inputs changed during the development check')
            for name, digest in drivers.items():
                if source.file_digest(source.LEAN_ROOT/name) != digest:
                    raise BuildError('staleArtifact', 'proof-check driver changed during the check: '+name)
            for tool in tools.values():
                if source.file_digest(Path(tool['path'])) != tool['sha256']:
                    raise BuildError('staleArtifact', 'Lean tool changed during the development check')

        targets = [module] + (['Contract.Check.Axioms'] if declarations else [])
        phase('build', [tools['lake']['path'], '--quiet', '--rehash', 'build', *targets])
        stable()
        report['incrementalBuild'] = True
        if declarations:
            audit = ('import Contract.Check.Axioms\nimport '+module+'\n' +
                     ''.join('#audit_contract_proof '+d+'\n' for d in declarations)).encode()
            stdout, stderr = phase('audit', [tools['lean']['path'], '--stdin'], audit)
            if stderr.strip() or stdout.count(b'logical axioms:') != len(declarations):
                raise BuildError('auditFailure', 'theorem audit did not report every requested declaration')
            stable()
            report['auditedDeclarations'] = list(declarations)
        if profile:
            # This re-elaborates the source file, without replacing its .olean.
            # The pinned profiler includes declaration names and component times.
            with tempfile.TemporaryDirectory(prefix='lean-proof-profile-') as tmp:
                profile_path = Path(tmp)/'profile.json'
                stdout, stderr = phase('profile', [tools['lean']['path'], '-DwarningAsError=true',
                    '-Dprofiler=true', '-Dprofiler.threshold='+str(threshold_ms),
                    '-Dtrace.profiler=true', '-Dtrace.profiler.threshold='+str(threshold_ms),
                    '-Dtrace.profiler.output.pp=true', '-Dtrace.profiler.output='+str(profile_path), str(path)])
                fatal = FATAL.search(stderr)
                if fatal:
                    raise BuildError('profileFailure', stderr[fatal.start():].decode(errors='replace')[:4000])
                data = read_bounded(profile_path, MAX_OUTPUT)
                profile_data = decode_json(data)
                if (not isinstance(profile_data, dict) or not isinstance(profile_data.get('threads'), list)
                        or not isinstance(profile_data.get('meta'), dict)):
                    raise BuildError('profileFailure', 'invalid structured profile from pinned Lean')
                artifacts['profile.json'] = data
                report['profileArtifact'] = 'profile.json'
            stable()
        if fresh:
            replay_env = env['LEAN_NUM_THREADS']
            env['LEAN_NUM_THREADS'] = '1'
            try:
                _, stderr = phase('replay', [tools['leanchecker']['path'], '--fresh', module])
            finally:
                env['LEAN_NUM_THREADS'] = replay_env
            if stderr.strip():
                raise BuildError('replayFailure', stderr.decode(errors='replace')[:4000])
            stable()
            report['freshKernelReplay'], report['replayIncludesImports'] = True, True
        stable()
        report['status'] = 'passed'
    except (BuildError, OSError, ValueError, subprocess.TimeoutExpired, KeyboardInterrupt, MemoryError) as error:
        category = error.category if isinstance(error, BuildError) else (
            'cancelled' if isinstance(error, KeyboardInterrupt) else
            'resourceLimit' if isinstance(error, (subprocess.TimeoutExpired, MemoryError)) else 'checkerFailure')
        diagnostic = str(error) or category
        locations = [dict(file=m['file'].removeprefix('error: ').removeprefix('warning: '),
                          line=int(m['line']), column=int(m['column'])) for m in LOCATION.finditer(diagnostic)]
        report['failure'] = {'phase': current, 'category': category,
                             'locations': locations, 'diagnostic': diagnostic}
        if current in report['phases']:
            report['phases'][current]['status'] = 'failed'
        artifacts['diagnostic.txt'] = (diagnostic+'\n').encode()
    artifacts['report.json'] = canonical(report)
    return report, artifacts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--module', required=True)
    parser.add_argument('--declaration', action='append', default=[], help='audit a theorem in the module or its imports; repeatable')
    parser.add_argument('--lean-bin', type=Path)
    parser.add_argument('--jobs', type=int, default=4)
    parser.add_argument('--timeout', type=int, default=600, help='seconds per phase')
    parser.add_argument('--fresh', action='store_true', help='freshly replay the module and all imports')
    parser.add_argument('--profile', action='store_true', help='re-elaborate the entire selected module with declaration profiling')
    parser.add_argument('--profile-threshold-ms', type=int, default=100)
    parser.add_argument('--output', type=Path, required=True, help='new directory for report and logs; never a contract bundle')
    args = parser.parse_args()
    try:
        if args.output.exists() or args.output.is_symlink():
            raise BuildError('outputExists', 'output directory already exists; choose a new directory')
        report, artifacts = check_module(args.module, args.declaration, lean_bin=args.lean_bin,
            jobs=args.jobs, timeout=args.timeout, fresh=args.fresh, profile=args.profile,
            threshold_ms=args.profile_threshold_ms)
        publish(args.output.absolute(), artifacts)
        if report['status'] != 'passed':
            failure = report['failure']
            print(f"{failure['phase']}: {failure['category']}: {failure['diagnostic']}", file=sys.stderr)
        print(canonical({'status': report['status'], 'assurance': report['assurance'],
                         'output': str(args.output), 'freshKernelReplay': report['freshKernelReplay']}).decode(), end='')
        return 0 if report['status'] == 'passed' else 1
    except (BuildError, OSError) as error:
        print(str(error), file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
