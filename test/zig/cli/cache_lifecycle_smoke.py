#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
# Copyright (C) 2026 OKcontract Pte. Ltd.
"""Exercise persistent-cache deletion, restart, recovery and concurrent startup."""

from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import sqlite3
import subprocess
import sys
import tempfile


def request(name='A'):
    return json.dumps({
        'language': 'Yul',
        'sources': {f'{name}.yul': {'content': f'object "{name}" {{ code {{ stop() }} }}'}},
        'settings': {'outputSelection': {'*': {'*': ['evm.bytecode.object']}}},
    }).encode()


def run(binary):
    with tempfile.TemporaryDirectory(prefix='oksolc-cache-lifecycle-') as temporary:
        parent = Path(temporary).resolve()
        project = parent / 'project'
        (project / '.git').mkdir(parents=True)
        nested = project / 'src'
        nested.mkdir()
        config = parent / 'config' / 'oksolc'
        config.mkdir(parents=True)
        (config / 'config.toml').write_text('cache = true\n')
        env = dict(os.environ, XDG_CONFIG_HOME=str(config.parent),
                   XDG_CACHE_HOME=str(parent / 'cache'))
        env.pop('OKSOLC_CACHE_AUTH_KEY', None)

        def command(*args, body=b'', environment=env, cwd=project):
            result = subprocess.run([binary, *args], input=body, cwd=cwd,
                                    env=environment, capture_output=True, timeout=40)
            assert result.returncode == 0, (args, result.returncode, result.stderr)
            return result.stdout

        def stats():
            return json.loads(command('cache', 'stats'))

        def clean():
            # Root discovery must agree with compilation from the project root.
            return json.loads(command('clean', cwd=nested))

        def compile(body=request(), *args):
            return command('--standard-json', *args, body=body)

        expected = compile(request(), '--no-cache')
        assert json.loads(expected)['contracts']['A.yul']['A']['evm']['bytecode']['object'] == '00'
        assert not stats()['exists']
        assert compile() == expected
        summary = stats()
        assert summary['exists'] and summary['entries'] > 0, summary
        database = Path(summary['path'])
        assert compile() == expected
        assert clean()['removed']
        assert not stats()['exists']
        assert not clean()['removed']
        assert compile() == expected
        assert stats()['entries'] > 0
        assert compile() == expected

        # Both explicit opt-outs still compile after deletion without recreating SQL.
        clean()
        assert compile(request(), '--no-cache') == expected
        assert not stats()['exists']
        project_config = project / 'oksolc.toml'
        project_config.write_text('cache = false\n')
        assert compile() == expected
        assert not stats()['exists']
        project_config.unlink()

        assert compile() == expected
        command('cache', 'prune', '--max-entries', '0')
        assert stats()['entries'] == 0
        assert compile() == expected
        assert stats()['entries'] > 0
        project_config.write_text('cache-max-entries = 0\n')
        assert compile() == expected
        assert stats()['entries'] == 0
        project_config.unlink()
        assert compile() == expected
        assert stats()['entries'] > 0

        # Damaged, old and partially initialized databases all recover on restart.
        for damage in ('garbage', 'old-schema', 'missing-verifier'):
            if damage == 'garbage':
                database.write_bytes(b'not a SQLite database')
            else:
                with sqlite3.connect(database) as sql:
                    sql.execute('PRAGMA user_version=1' if damage == 'old-schema'
                                else 'DELETE FROM cache_authentication')
            assert compile() == expected, damage
            assert stats()['entries'] > 0, damage
            assert list(database.parent.glob('artifacts.sqlite.rejected-*')), damage
            assert compile() == expected, damage
            clean()
            assert compile() == expected

        # Preserve other trust domains and newer formats while compiling in memory.
        previous = stats()['entries']
        wrong_key = dict(env, OKSOLC_CACHE_AUTH_KEY='42' * 32)
        assert command('--standard-json', body=request(), environment=wrong_key) == expected
        assert stats()['entries'] == previous
        with sqlite3.connect(database) as sql:
            sql.execute('PRAGMA user_version=999')
        assert compile() == expected
        with sqlite3.connect(database) as sql:
            assert sql.execute('PRAGMA user_version').fetchone()[0] == 999
        assert not list(database.parent.glob('artifacts.sqlite.rejected-*'))

        # Every cold-start contender must compile correctly, including after clean.
        clean()
        requests = [request(f'C{index}') for index in range(8)]
        outputs = [compile(body, '--no-cache') for body in requests]
        with ThreadPoolExecutor(max_workers=8) as workers:
            assert list(workers.map(compile, requests)) == outputs
        assert stats()['entries'] > 0
        assert not list(database.parent.glob('artifacts.sqlite.rejected-*'))
        with sqlite3.connect(database) as sql:
            assert sql.execute('PRAGMA integrity_check').fetchone()[0] == 'ok'
        for body, output in zip(requests, outputs):
            assert compile(body) == output

    print('cache lifecycle: clean/restart, opt-outs, pruning, zero limits, corruption, '
          'incomplete initialization, trust isolation, concurrent startup passed')


if __name__ == '__main__':
    run(str(Path(sys.argv[1]).resolve()))
