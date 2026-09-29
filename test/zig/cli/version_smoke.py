#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
# Copyright (C) 2026 OKcontract Pte. Ltd.

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


def main():
    cli = str(Path(sys.argv[1]).resolve())
    version, build_identity = sys.argv[2:]
    compatibility = f'0.8.36+oksolc.{version}'
    with tempfile.TemporaryDirectory(prefix='oksolc-version-') as directory:
        root = Path(directory)
        config = root / 'config' / 'oksolc'
        config.mkdir(parents=True)
        # Version inspection must work even if compiler startup would fail.
        (config / 'config.toml').write_text('invalid toml [')
        env = dict(os.environ, XDG_CONFIG_HOME=str(root / 'config'),
                   XDG_CACHE_HOME=str(root / 'cache'))

        def command(*args, success=True):
            result = subprocess.run([cli, *args], cwd=root, env=env,
                                    capture_output=True, text=True, timeout=30)
            if success:
                assert result.returncode == 0, result.stderr
                assert not result.stderr, result.stderr
            else:
                assert result.returncode != 0, result.stdout
                assert not result.stdout, result.stdout
            return result.stdout

        assert command('version') == f'oksolc {version} (Solidity 0.8.36)\n'
        output = command('--version')
        assert output == ('oksolc, a solidity compiler commandline interface\n'
                          f'Version: {compatibility}\n')
        # Foundry parses the final nonempty line as the Solidity SemVer.
        assert output.strip().splitlines()[-1] == f'Version: {compatibility}'
        assert json.loads(command('version', '--json')) == {
            'version': version,
            'solidity_version': '0.8.36',
            'compatibility_version': compatibility,
            'build_identity': build_identity or None,
        }
        help_text = command('version', '--help')
        assert 'usage: oksolc version [--json]' in help_text
        assert '--json' in help_text
        command('version', '--unknown', success=False)
        command('version', 'extra', success=False)
        command('--version', '--json', success=False)
        command('--version', 'version', success=False)
        assert not (root / 'cache').exists()


if __name__ == '__main__':
    main()
