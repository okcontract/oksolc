#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""
// Copyright (C) 2026 OKcontract Pte. Ltd.
Install real Git submodules using isolated local origins; no network required.
"""
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile


def run(cli):
    git = shutil.which('git')
    assert git, 'install-smoke requires system Git'
    with tempfile.TemporaryDirectory(prefix='oksolc-install-') as temporary:
        root = Path(temporary)
        env = dict(os.environ, GIT_CONFIG_NOSYSTEM='1', GIT_CONFIG_GLOBAL=os.devnull,
                   GIT_AUTHOR_NAME='Install test', GIT_AUTHOR_EMAIL='install@example.invalid',
                   GIT_COMMITTER_NAME='Install test', GIT_COMMITTER_EMAIL='install@example.invalid',
                   GIT_ALLOW_PROTOCOL='file', GIT_TERMINAL_PROMPT='0')

        def command(argv, cwd=root, check=True, custom_env=env):
            result = subprocess.run(argv, cwd=cwd, env=custom_env, capture_output=True, timeout=45)
            if check:
                assert result.returncode == 0, (argv, result.returncode, result.stdout, result.stderr)
            return result

        def g(directory, *args):
            return command([git, '-C', str(directory), *args]).stdout.decode().strip()

        def repository(name):
            path = root / name
            path.mkdir()
            g(path, 'init', '-q')
            return path

        def commit(directory):
            g(directory, 'add', '--all')
            g(directory, 'commit', '-qm', 'fixture')
            return g(directory, 'rev-parse', 'HEAD')

        leaf = repository('leaf origin')
        (leaf / 'src').mkdir()
        (leaf / 'src/Leaf.sol').write_text('library Leaf {}')
        leaf_pin = commit(leaf)
        origin = repository('library origin')
        (origin / 'src').mkdir()
        (origin / 'src/Math.sol').write_text('library Math { uint constant VALUE = 1; }')
        g(origin, 'submodule', 'add', '-q', str(leaf), 'vendor/leaf')
        pin = commit(origin)
        unused = repository('unused origin')
        (unused / 'Unused.sol').write_text('library Unused {}')
        commit(unused)

        seed = repository('seed')
        (seed / 'src/deep').mkdir(parents=True)
        (seed / 'src/Local.sol').write_text('library Local {}')
        path = 'lib/pkg [x]'
        decoy = 'lib/pkg x'
        g(seed, 'submodule', 'add', '-q', '--name', 'remapped.library', str(origin), path)
        g(seed, 'submodule', 'add', '-q', str(unused), decoy)
        mappings = f' pkg/={path}/src/\r\n\nsrc/:nested/={path}/vendor/leaf/src/\nlocal=src/Lo\n'
        (seed / 'remappings.txt').write_text(mappings)
        commit(seed)
        (origin / 'src/Math.sol').write_text('library Math { uint constant VALUE = 2; }')
        new_pin = commit(origin)

        def clone(name):
            destination = root / name
            command([git, 'clone', '-q', '--no-local', str(seed), str(destination)])
            (destination / 'src/deep').mkdir(exist_ok=True)
            return destination

        def install(directory, *args, check=True, custom_env=env):
            return command([cli, 'install', *args], cwd=directory, check=check, custom_env=custom_env)

        checkout = clone('working project')
        module = checkout / path
        manifest = (checkout / '.gitmodules').read_bytes()
        result = install(checkout / 'src/deep', '--jobs', '4')
        assert b'Installing 1 Git submodule' in result.stderr, result.stderr
        assert g(module, 'rev-parse', 'HEAD') == pin != new_pin
        assert g(module / 'vendor/leaf', 'rev-parse', 'HEAD') == leaf_pin
        assert not (checkout / decoy / 'Unused.sol').exists(), 'literal path became a glob'
        assert g(checkout, 'status', '--porcelain') == ''
        assert (checkout / '.gitmodules').read_bytes() == manifest
        assert not (checkout / '.oksolc').exists(), 'install created a compiler cache or database'
        install(root, '--base-path', str(checkout))
        assert g(module, 'rev-parse', 'HEAD') == pin

        # Source projects inside a larger Git worktree keep their own remappings.
        application = checkout / 'apps/application'
        application.mkdir(parents=True)
        (application / 'oksolc.toml').write_text('source-path = "src"\n')
        (application / 'remappings.txt').write_text(f'app/=../../{path}/src/\n')
        assert b'Installing 1 Git submodule' in install(application).stderr

        # Git retains dirty work; --checkout overrides a configured update=none.
        g(module, 'checkout', '-q', new_pin)
        g(checkout, 'add', '--', path)
        g(module, 'checkout', '-q', pin)
        g(checkout, 'config', 'submodule.remapped.library.update', 'none')
        dirty = 'library Math { uint constant VALUE = 99; }'
        (module / 'src/Math.sol').write_text(dirty)
        result = install(checkout, check=False)
        assert result.returncode != 0 and b'overwritten' in result.stderr, result.stderr
        assert (module / 'src/Math.sol').read_text() == dirty
        g(module, 'restore', 'src/Math.sol')
        install(checkout)
        assert g(module, 'rev-parse', 'HEAD') == new_pin

        all_modules = clone('all modules')
        (all_modules / 'remappings.txt').unlink()
        install(all_modules)
        assert (all_modules / decoy / 'Unused.sol').exists()
        assert g(all_modules / path / 'vendor/leaf', 'rev-parse', 'HEAD') == leaf_pin

        empty = clone('empty selection')
        (empty / 'remappings.txt').write_text('\n  \n')
        assert b'No Git submodules to install' in install(empty).stderr
        assert not (empty / path / 'src/Math.sol').exists()
        config_before = (empty / '.git/config').read_bytes()
        for invalid in ['bad remapping\n', 'missing/=lib/missing/\n']:
            (empty / 'remappings.txt').write_text(invalid)
            assert install(empty, check=False).returncode != 0
            assert (empty / '.git/config').read_bytes() == config_before
            assert not (empty / path / 'src/Math.sol').exists()
        (empty / 'remappings.txt').write_text('pkg/=lib/\n')
        install(empty)
        assert (empty / decoy / 'Unused.sol').exists(), 'broad remapping omitted a possible module'

        # Local URL overrides survive; the installer must not run submodule sync.
        overridden = clone('URL override')
        g(overridden, 'config', '--file', '.gitmodules', 'submodule.remapped.library.url', str(root / 'absent origin'))
        g(overridden, 'config', 'submodule.remapped.library.url', str(origin))
        install(overridden)
        assert g(overridden / path, 'rev-parse', 'HEAD') == pin
        assert g(overridden, 'config', 'submodule.remapped.library.url') == str(origin)

        no_modules = repository('no modules')
        assert b'No Git submodules to install' in install(no_modules).stderr
        assert install(root, check=False).returncode != 0
        for args in [('--jobs', '0'), ('--base-path', ''), ('unexpected',)]:
            assert install(checkout, *args, check=False).returncode != 0
        assert b'oksolc install' in install(root, '--help').stdout
        assert b'oksolc install' in command([cli, '--help']).stdout
        no_git = root / 'no git'
        no_git.mkdir()
        result = install(checkout, check=False, custom_env=dict(env, PATH=str(no_git)))
        assert result.returncode != 0 and b'Git is required' in result.stderr, result.stderr

        # Git's failure exit and terminal signal survive the final process handoff.
        fake_bin = root / 'fake bin'
        fake_bin.mkdir()
        fake_git = fake_bin / 'git'
        fake_git.write_text(f'#!{sys.executable}\n' +
                            'import os, signal, sys\n' +
                            f'root = {str(seed.resolve())!r}\n' +
                            'if "rev-parse" in sys.argv: print(root)\n' +
                            f'elif "config" in sys.argv: sys.stdout.buffer.write({("submodule.test.path" + chr(10) + path + chr(0)).encode()!r})\n' +
                            'else:\n' +
                            ' assert "--literal-pathspecs" in sys.argv and "--checkout" in sys.argv\n' +
                            ' assert "--force" not in sys.argv and "--remote" not in sys.argv\n' +
                            ' if os.environ.get("TEST_SIGNAL"): os.kill(os.getpid(), signal.SIGTERM)\n' +
                            ' sys.exit(37)\n')
        fake_git.chmod(0o755)
        # Seed has the same remapping targets used by the fake Git metadata.
        fake_env = dict(env, PATH=str(fake_bin))
        result = install(seed, check=False, custom_env=fake_env)
        assert result.returncode == 37, (result.returncode, result.stdout, result.stderr)
        if os.name == 'posix':
            assert install(seed, check=False, custom_env=dict(fake_env, TEST_SIGNAL='1')).returncode == -signal.SIGTERM

        # Malformed Git config is reported by Git before any update.
        (no_modules / '.gitmodules').write_text('[broken\n')
        result = install(no_modules, check=False)
        assert result.returncode != 0 and b'config' in result.stderr
    print('install: selected and nested modules, pins, literal paths, repeat installs, local aliases, project roots, dirty recovery, URL overrides, no-op/error paths and Git exit/signal propagation passed')


if __name__ == '__main__':
    run(str(Path(sys.argv[1]).resolve()))
