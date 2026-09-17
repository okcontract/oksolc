#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""
// Copyright (C) 2026 OKcontract Pte. Ltd.
Concurrent compilation/publication, HTTP snapshot isolation and recovery.
"""
import concurrent.futures
import hashlib
import json
from pathlib import Path
import socket
import sqlite3
import subprocess
import sys
import tempfile
import time
from browser_smoke import browser, data, request
from source_serve_smoke import Service


def until(check):
    deadline = time.monotonic() + 30
    while time.monotonic() < deadline:
        value = check()
        if value:
            return value
        time.sleep(.04)
    raise AssertionError('live compilation did not reach expected state')


def run(cli):
    with tempfile.TemporaryDirectory(prefix='oksolc-live-browser-') as temporary:
        root = Path(temporary)
        (root / '.git').mkdir()
        (root / 'src/nested').mkdir(parents=True)
        (root / 'lib').mkdir()
        source = root / 'src/Entry.sol'
        library = root / 'lib/Used.sol'
        unused = root / 'lib/Unused.sol'
        preamble = '// SPDX-License-Identifier: MIT\npragma solidity >=0.0.0;\n'
        source.write_text(preamble + 'import "pkg/Used.sol"; contract Entry { function value() external pure returns (uint) { assert(Used.value() > 0); return Used.value(); } }')
        (root / 'remappings.txt').write_text('pkg/=lib/\n')
        library.write_text(preamble + 'library Used { function value() internal pure returns (uint) { return 1; } }')
        unused.write_text('not Solidity')
        database = root / '.oksolc/browser.sqlite'
        args = ['--browse', '--no-cache', '--poll-ms', '30', '--parallel', '--jobs', '4']
        with browser(cli, root / 'src/nested', args, command='serve') as port:
            status = data(port, 'status')
            assert status['live'] and status['source_path'] == 'src' and status['phase'] == 'watching', status
            assert database.is_file() and not (root / 'src/nested/.oksolc').exists()
            first = status['latest']
            assert data(port, 'request')['settings']['remappings'] == ['pkg/=lib/']
            first_output = request(port, f'/api/output?compilation={first}')[2]
            assert {r['name'] for r in data(port, 'project')} == {'src/Entry.sol', 'lib/Used.sol'}
            unused.write_text('still not Solidity')
            time.sleep(.3)
            assert data(port, 'status')['latest'] == first

            def read_snapshots(_):
                for _ in range(8):
                    snapshot = data(port, 'compilations')[0]
                    output = request(port, f'/api/output?compilation={snapshot["id"]}')[2]
                    assert hashlib.sha256(output).hexdigest() == snapshot['output_sha256']
                    parsed = json.loads(output)
                    assert 'src/Entry.sol' in parsed['sources']
                return True
            with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
                readers = [pool.submit(read_snapshots, i) for i in range(4)]
                library.write_text(library.read_text().replace('return 1;', 'return 2;'))
                second = until(lambda: (s := data(port, 'status'))['latest'] > first and s['phase'] == 'watching' and s['latest'])
                assert all(reader.result() for reader in readers)
            second_output = request(port, f'/api/output?compilation={second}')[2]
            assert second_output != first_output
            assert request(port, f'/api/output?compilation={first}')[2] == first_output
            assert 'return 1;' in data(port, f'source?compilation={first}&source=lib%2FUsed.sol')['content']
            assert 'return 2;' in data(port, 'source?source=lib%2FUsed.sol')['content']
            clean = Service(cli, root)
            try:
                assert second_output.rstrip(b'\n') == clean.next()[0], 'published bytes differ from clean compilation'
            finally:
                clean.close()

            # An unreadable remapping revision retains the last published request.
            replacement = root / 'remappings.next'
            replacement.write_bytes(b' ' * (1024 * 1024 + 1))
            replacement.replace(root / 'remappings.txt')
            until(lambda: data(port, 'status')['phase'] == 'stale')
            assert data(port, 'status')['latest'] == second
            assert data(port, 'request')['settings']['remappings'] == ['pkg/=lib/']
            replacement.write_text('pkg/=lib/\n')
            replacement.replace(root / 'remappings.txt')
            until(lambda: data(port, 'status')['phase'] == 'watching')
            assert data(port, 'status')['latest'] == second

            # Failed publication rolls back every index; retries keep watching.
            with sqlite3.connect(database) as sql:
                sql.execute("CREATE TRIGGER fail_publication BEFORE INSERT ON node BEGIN SELECT RAISE(ABORT,'test rejection'); END")
            source.write_text(source.read_text() + '\n// changed\n')
            until(lambda: data(port, 'status')['phase'] == 'stale')
            assert data(port, 'status')['latest'] == second
            assert request(port, '/api/output')[2] == second_output
            with sqlite3.connect(database) as sql:
                for table in ['compilation', 'source', 'contract', 'diagnostic', 'node']:
                    column = 'id' if table == 'compilation' else 'compilation'
                    assert sql.execute(f'SELECT count(*) FROM {table} WHERE {column}>?', (second,)).fetchone()[0] == 0
                sql.execute('DROP TRIGGER fail_publication')
            third = until(lambda: (s := data(port, 'status'))['latest'] > second and s['phase'] == 'watching' and s['latest'])
            until(lambda: data(port, 'status')['phase'] == 'watching')

            (root / 'src').rename(root / 'src-away')
            until(lambda: data(port, 'status')['phase'] == 'stale')
            assert data(port, 'status')['latest'] == third
            (root / 'src-away').rename(root / 'src')
            until(lambda: data(port, 'status')['phase'] == 'watching')
            assert data(port, 'status')['latest'] == third
            source.write_text('syntax error')
            fourth = until(lambda: (s := data(port, 'status'))['latest'] > third and s['phase'] == 'watching' and s['latest'])
            assert any(e['severity'] == 'error' for e in data(port, 'output')['errors'])
            source.write_text(preamble + 'contract Entry {}')
            fifth = until(lambda: (s := data(port, 'status'))['latest'] > fourth and s['phase'] == 'watching' and s['latest'])
            latest_output = request(port, f'/api/output?compilation={fifth}')[2]
            assert not any(e['severity'] == 'error' for e in json.loads(latest_output).get('errors', []))
        with browser(cli, root / 'src/nested', []) as port:
            assert data(port, 'status')['live'] is False
            assert request(port, '/api/output')[2] == latest_output
            # Each accepted revision saves one compiler output.
            assert len(data(port, 'compilations')) == 5
        with browser(cli, root, ['--browse', '--no-cache', '--database', ':memory:'], command='serve') as port:
            assert data(port, 'status')['live'] and len(data(port, 'compilations')) == 1
            assert 'abstractInterpretation' not in data(port, 'request')['settings']
        # The compiler future must be canceled/joined when HTTP binding fails.
        with socket.socket() as sock:
            sock.bind(('127.0.0.1', 0))
            sock.listen()
            result = subprocess.run([cli, 'serve', '--browse', '--no-cache', '--database', ':memory:',
                                     '--port', str(sock.getsockname()[1]), '--poll-ms', '60000'],
                                    cwd=root, capture_output=True, timeout=10)
            assert result.returncode != 0 and b'AddressInUse' in result.stderr, result.stderr
    print('live browser: concurrent SQL snapshots, clean bytes, rollback, stale/recovery, project persistence, memory override and compiler-task cancellation passed')


if __name__ == '__main__':
    run(str(Path(sys.argv[1]).resolve()))
