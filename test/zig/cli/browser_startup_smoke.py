#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""
// Copyright (C) 2026 OKcontract Pte. Ltd.
HTTP availability before the first successful source read and snapshot.
"""
from pathlib import Path
import sys
import tempfile
from browser_smoke import browser, data, request
from live_browser_smoke import until


def run(cli):
    with tempfile.TemporaryDirectory(prefix='oksolc-startup-') as temporary:
        root = Path(temporary)
        (root / '.git').mkdir()
        args = ['--browse', '--no-cache', '--database', ':memory:', '--poll-ms', '30']
        with browser(cli, root, args, command='serve', wait_for_compilation=False) as port:
            assert request(port, '/')[0] == 200
            until(lambda: data(port, 'status')['phase'] == 'stale')
            assert data(port, 'status')['latest'] is None
            assert data(port, 'compilations') == []
            assert data(port, 'project') == []
            assert request(port, '/api/output')[0] == 404
            assert request(port, '/api/request')[0] == 404
            (root / 'src').mkdir()
            source = 'pragma solidity >=0.0.0; contract Initial { function value() external pure returns (uint) { return 42; } }'
            (root / 'src/Initial.sol').write_text(source)
            until(lambda: data(port, 'status')['current'] is not None)
            status = data(port, 'status')
            assert status['phase'] == 'watching' and status['workspace_revision'] > 0
            workspace = data(port, 'project?compilation=0')
            assert len(workspace) == 1 and workspace[0]['has_ast'] == 0
            assert data(port, 'source?compilation=0&source=src%2FInitial.sol')['content'] == source
            assert data(port, 'source?compilation=0&source=src%2FInitial.sol')['tokens']
            assert data(port, 'search?compilation=0&q=Initial')[0]['name'] == 'src/Initial.sol'
            assert data(port, 'contracts?compilation=0') == []
            assert request(port, '/api/output?compilation=0')[0] == 404
            assert len(data(port, 'compilations')) == 1
    print('browser startup: empty live HTTP, initial read failure/recovery, separate SQL workspace, source highlighting and completed publication passed')


if __name__ == '__main__':
    run(str(Path(sys.argv[1]).resolve()))
