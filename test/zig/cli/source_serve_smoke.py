#!/usr/bin/env python3
"""Source-root and dependency watching regression.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""
import json
import os
from pathlib import Path
import queue
import subprocess
import sys
import tempfile
import threading


class Service:
    def __init__(self, binary, root, *args):
        env = dict(os.environ, XDG_CONFIG_HOME=str(root / 'config'), XDG_CACHE_HOME=str(root / 'cache'))
        self.process = subprocess.Popen([binary, 'serve', '--no-cache', '--poll-ms', '30', *args],
                                        cwd=root, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.lines = queue.Queue()
        self.errors = []
        def read():
            for line in self.process.stdout:
                if line.strip():
                    self.lines.put(line.rstrip(b'\n'))
            self.lines.put(None)
        def errors():
            self.errors.extend(self.process.stderr)
        self.reader = threading.Thread(target=read)
        self.error_reader = threading.Thread(target=errors)
        self.reader.start()
        self.error_reader.start()

    def next(self):
        try:
            line = self.lines.get(timeout=40)
        except queue.Empty as exc:
            raise AssertionError(('compilation timed out', self.errors)) from exc
        assert line is not None, self.errors
        return line, json.loads(line)

    def quiet(self):
        try:
            unexpected = self.lines.get(timeout=0.4)
        except queue.Empty:
            return
        raise AssertionError(('unexpected compilation', unexpected, self.errors))

    def close(self):
        self.process.terminate()
        self.process.wait(timeout=10)
        self.reader.join()
        self.error_reader.join()
        self.process.stdout.close()
        self.process.stderr.close()


def run(binary):
    with tempfile.TemporaryDirectory(prefix='oksolc-source-serve-') as temporary:
        root = Path(temporary)
        (root / '.git').mkdir()
        (root / 'src').mkdir()
        (root / 'lib').mkdir()
        entry = root / 'src/Entry.sol'
        used = root / 'lib/Used.sol'
        unused = root / 'lib/Unused.sol'
        preamble = '// SPDX-License-Identifier: MIT\npragma solidity ^0.8.0;\n'
        used.write_text(preamble + 'library Used { function value() internal pure returns (uint) { return 1; } }')
        unused.write_text('not Solidity')
        entry.write_text(preamble + 'import "pkg/Used.sol"; contract Entry { function value() external pure returns (uint) { assert(Used.value() > 0); return Used.value(); } }')
        remappings = root / 'remappings.txt'
        service = Service(binary, root)
        try:
            assert any(e['severity'] == 'error' for e in service.next()[1]['errors'])
            remappings.write_text('pkg/=lib/\n')
            initial, output = service.next()
            assert set(output['sources']) == {'src/Entry.sol', 'lib/Used.sol'}, output
            assert not any(e['severity'] == 'error' for e in output.get('errors', [])), output
            assert 'abi' in output['contracts']['src/Entry.sol']['Entry']
            service.quiet()
            unused.write_text('still not Solidity')
            service.quiet()
            # Same-size dependency edit: timestamps are deliberately restored.
            before = used.stat()
            used.write_text(used.read_text().replace('return 1;', 'return 2;'))
            os.utime(used, ns=(before.st_atime_ns, before.st_mtime_ns))
            changed, output = service.next()
            assert changed != initial
            fresh = Service(binary, root)
            try:
                assert changed == fresh.next()[0], 'incremental output differs from clean compilation'
            finally:
                fresh.close()
            (root / 'src/Added.sol').write_text(preamble + 'contract Added {}')
            assert 'src/Added.sol' in service.next()[1]['sources']
            (root / 'src/Added.sol').unlink()
            assert 'src/Added.sol' not in service.next()[1]['sources']
            used.unlink()
            assert any(e['severity'] == 'error' for e in service.next()[1]['errors'])
            used.write_text(preamble + 'library Used { function value() internal pure returns (uint) { return 3; } }')
            assert not any(e['severity'] == 'error' for e in service.next()[1].get('errors', []))
            remappings.write_text('invalid\n')
            assert any(e['type'] == 'JSONError' for e in service.next()[1]['errors'])
            remappings.write_text('pkg/=lib/\n')
            assert not any(e['severity'] == 'error' for e in service.next()[1].get('errors', []))
            remappings.unlink()
            assert any(e['severity'] == 'error' for e in service.next()[1]['errors'])
            (root / 'lib/other').mkdir()
            (root / 'lib/other/Used.sol').write_text(used.read_text().replace('return 3;', 'return 4;'))
            remappings.write_text('pkg/=lib/other/\n')
            retargeted, output = service.next()
            assert set(output['sources']) == {'src/Entry.sol', 'lib/other/Used.sol'}, output
            fresh = Service(binary, root)
            try:
                assert retargeted == fresh.next()[0], 'remapped output differs from clean compilation'
            finally:
                fresh.close()
            used.write_text('unused after remapping')
            service.quiet()
            entry.write_text(preamble + 'contract Entry {}')
            assert set(service.next()[1]['sources']) == {'src/Entry.sol'}
            used.write_text('broken unused library')
            service.quiet()
            entry.write_text('syntax error')
            assert any(e['severity'] == 'error' for e in service.next()[1]['errors'])
            entry.write_text(preamble + 'contract Entry {}')
            assert not any(e['severity'] == 'error' for e in service.next()[1].get('errors', []))
        finally:
            service.close()
        (root / 'contracts').mkdir()
        (root / 'contracts/Custom.sol').write_text(preamble + 'contract Custom {}')
        (root / 'oksolc.toml').write_text('source-path = "contracts"\n')
        for args, expected in [((), 'contracts/Custom.sol'), (('--source-path', 'src'), 'src/Entry.sol')]:
            service = Service(binary, root, *args)
            try:
                assert set(service.next()[1]['sources']) == {expected}
            finally:
                service.close()
        for args in [('--source-path', '../lib'), ('--stdio', '--source-path', 'src')]:
            result = subprocess.run([binary, 'serve', '--no-cache', *args], cwd=root, capture_output=True, timeout=10)
            assert result.returncode != 0
    print('source serve: roots, imports, live remappings, additions/deletions, failures/recovery, configuration and clean-byte equivalence passed')


if __name__ == '__main__':
    run(str(Path(sys.argv[1]).resolve()))
