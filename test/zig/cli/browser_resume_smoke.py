#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""
// Copyright (C) 2026 OKcontract Pte. Ltd.
Persistent live inspection reuse and full source/read-set invalidation.
"""
import os
import json
from pathlib import Path
import sqlite3
import sys
import tempfile
from browser_smoke import browser, data, request
from live_browser_smoke import until


def run(cli):
    with tempfile.TemporaryDirectory(prefix='oksolc-resume-') as temporary:
        parent = Path(temporary).resolve()
        root = parent / 'project'
        (root / '.git').mkdir(parents=True)
        (root / 'src').mkdir()
        (root / 'lib').mkdir()
        env = {**os.environ, 'XDG_CONFIG_HOME': str(parent / 'config'), 'XDG_CACHE_HOME': str(parent / 'cache')}
        env.pop('OKSOLC_CACHE_AUTH_KEY', None)
        source, library = root / 'src/Entry.sol', root / 'lib/Used.sol'
        preamble = '// SPDX-License-Identifier: MIT\npragma solidity >=0.0.0;\n'
        source.write_text(preamble + 'import "pkg/Used.sol"; contract Entry { function value() external pure returns (uint) { assert(Used.value() > 0); return Used.value(); } }')
        library.write_text(preamble + 'library Used { function value() internal pure returns (uint) { return 1; } }')
        (root / 'remappings.txt').write_text('pkg/=lib/\n')
        database = root / '.oksolc/browser.sqlite'
        args = ['--browse', '--poll-ms', '30']

        def launch(previous=None, reused=False, extra=(), environment=env):
            with browser(cli, root, [*args, *extra], command='serve', env=environment) as port:
                status = data(port, 'status')
                assert status['reused'] == reused, (status, 'Reuse requires an available compiler content identity.')
                current = status['current']
                assert current == status['latest']
                if previous is not None:
                    assert (current == previous) if reused else (current > previous), status
                return current, request(port, '/api/output')[2]

        first, original = launch()
        second, output = launch(first, True)
        assert output == original
        with sqlite3.connect(database) as sql:
            assert sql.execute('SELECT count(*) FROM live_receipt').fetchone()[0] == 1
        (root / 'lib/Unused.sol').write_text('unused, invalid Solidity')
        launch(second, True)
        # Byte changes matter even with identical size and restored timestamps.
        stat = library.stat()
        library.write_text(library.read_text().replace('return 1;', 'return 2;'))
        os.utime(library, ns=(stat.st_atime_ns, stat.st_mtime_ns))
        third, changed = launch(second)
        assert changed != original
        # Replayed dependencies remain watched after a successful restart.
        with browser(cli, root, args, command='serve', env=env) as port:
            assert data(port, 'status')['reused']
            library.unlink()
            missing = until(lambda: (s := data(port, 'status'))['current'] > third and s['current'])
        missing, errors = launch(missing, True)
        assert b'not found' in errors
        library.write_text(preamble + 'library Used { function value() internal pure returns (uint) { return 2; } }')
        current, repaired = launch(missing)
        assert repaired == changed
        addition = root / 'src/Added.sol'
        addition.write_text(preamble + 'contract Added {}')
        current, _ = launch(current)
        addition.unlink()
        current, _ = launch(current)
        source.write_text(source.read_text().replace('> 0', '> 1'))
        current, _ = launch(current)
        (root / 'remappings.txt').write_text('pkg/=lib/\nalias/=lib/\n')
        current, _ = launch(current)
        current, _ = launch(current, extra=['--parallel', '--jobs', '4'])
        launch(current, True, extra=['--parallel', '--jobs', '4'])
        current, _ = launch(current, extra=['--base-path', str(root), '--include-path', str(root / 'lib')])
        launch(current, True, extra=['--base-path', str(root), '--include-path', str(root / 'lib')])
        (root / 'alternate').mkdir()
        (root / 'alternate/Entry.sol').write_text(source.read_text())
        current, _ = launch(current, extra=['--source-path', 'alternate'])
        launch(current, True, extra=['--source-path', 'alternate'])
        current, canonical = launch(current)
        # Explicitly disabled reuse also leaves no resumable receipt.
        current, clean = launch(current, extra=['--no-cache'])
        assert clean == canonical
        current, _ = launch(current)
        # Corrupt bodies, manifests and context cannot be accepted as current.
        for statement in [
            "UPDATE compilation SET output='{}' WHERE id=?",
            "UPDATE compilation SET request='{}' WHERE id=?",
            "UPDATE live_receipt SET manifest='[]' WHERE compilation=?",
            "UPDATE live_receipt SET context='changed' WHERE compilation=?",
            "UPDATE live_receipt SET seal=printf('%064d',0) WHERE compilation=?",
        ]:
            with sqlite3.connect(database) as sql:
                sql.execute(statement, (current,))
            current, output = launch(current)
            assert output == canonical
        wrong_key = {**env, 'OKSOLC_CACHE_AUTH_KEY': '42' * 32}
        current, output = launch(current, environment=wrong_key)
        assert output == canonical
        current, _ = launch(current)
        # Additive v1 migration keeps history and recreates snapshot receipts.
        with sqlite3.connect(database) as sql:
            count = sql.execute('SELECT count(*) FROM compilation').fetchone()[0]
            sql.executescript('DROP TABLE live_receipt; PRAGMA user_version=1;')
        current, _ = launch(current)
        with sqlite3.connect(database) as sql:
            assert sql.execute('PRAGMA user_version').fetchone()[0] == 4
            assert sql.execute('SELECT count(*) FROM compilation').fetchone()[0] == count + 1
        launch(current, True)
    print('browser resume: default reuse, canonical bytes, watched replay, same-timestamp edits, failed imports, membership, remappings, scheduler, no-cache, authentication, corruption and migration passed')


if __name__ == '__main__':
    run(str(Path(sys.argv[1]).resolve()))
