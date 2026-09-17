#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""
// Copyright (C) 2026 OKcontract Pte. Ltd.
Diagnostic limits are compiler output, including in a retained session.
"""
import json
from pathlib import Path
import subprocess
import sys
from browser_smoke import browser, data
import tempfile

PREAMBLE = '// SPDX-License-Identifier: MIT\npragma solidity >=0.0.0;\n'


def request(sources):
    return json.dumps({'language': 'Solidity', 'sources': {name: {'content': text} for name, text in sources.items()},
                       'settings': {'viaIR': True, 'optimizer': {'enabled': True},
                                    'outputSelection': {'*': {'': ['ast'], '*': ['abi']}}}}, separators=(',', ':')).encode()


def imports(count):
    return PREAMBLE + ''.join(f'import "missing/{i}.sol";\n' for i in range(count)) + 'contract C {}'


def check(output, limit):
    result = json.loads(output)
    diagnostics = result['errors']
    assert len([e for e in diagnostics if e['severity'] == 'error']) == 256, diagnostics[-2:]
    sentinel = [e for e in diagnostics if e.get('errorCode') == '4013']
    assert len(sentinel) == int(limit), sentinel
    if limit:
        assert 'Aborting' in sentinel[0]['message']
    assert not result.get('contracts') and not result.get('sources'), 'failed parsing must not publish semantic artifacts'
    assert diagnostics[0]['sourceLocation']['file']
    assert '-->' in diagnostics[0]['formattedMessage']


def main(cli):
    inputs = [request({'C.sol': imports(n)}) for n in [256, 257]]
    inputs.append(request({f'C{i:03}.sol': PREAMBLE + 'contract C {' for i in range(257)}))
    outputs = []
    for index, input_bytes in enumerate(inputs):
        result = subprocess.run([cli, 'standard-json', '--no-cache'], input=input_bytes, capture_output=True, timeout=30)
        assert result.returncode == 0, result.stderr
        check(result.stdout, index != 0)
        outputs.append(result.stdout)
    good = request({'Good.sol': PREAMBLE + 'contract Good { function f() external pure { assert(true); } }'})
    changed = request({'Good.sol': PREAMBLE + 'contract Good { function f() external pure { assert(1 == 1); } }'})
    clean_changed = subprocess.run([cli, 'standard-json', '--no-cache'], input=changed, capture_output=True, timeout=30)
    assert clean_changed.returncode == 0, clean_changed.stderr
    sequence = [good, inputs[1], inputs[2], good, changed]
    frames = b''.join(f'Content-Length: {len(payload)}\r\n\r\n'.encode() + payload for payload in sequence)
    run = subprocess.run([cli, 'serve', '--stdio', '--no-cache', '--base-path', '.'], input=frames, capture_output=True, timeout=30)
    assert run.returncode == 0, run.stderr
    remaining = run.stdout
    replies = []
    while remaining:
        header, remaining = remaining.split(b'\r\n\r\n', 1)
        size = int(header.split(b':', 1)[1])
        replies.append(remaining[:size])
        remaining = remaining[size:]
    assert len(replies) == 5
    assert replies[0] == replies[3], 'diagnostic abort changed the previous valid result'
    assert replies[1] == outputs[1] and replies[2] == outputs[2]
    assert replies[4] == clean_changed.stdout, 'recompilation after diagnostic abort differs from clean compilation'
    with tempfile.TemporaryDirectory(prefix='oksolc-diagnostic-limit-') as directory:
        root = Path(directory)
        (root / 'src').mkdir()
        (root / 'src/C.sol').write_text(imports(257))
        with browser(cli, root, ['--browse', '--no-cache', '--database', ':memory:'], command='serve') as port:
            check(json.dumps(data(port, 'output')), True)
            assert data(port, 'status')['live']
    print('diagnostic limits: import and syntax boundaries, source locations, session recovery, canonical output and live browser startup passed')


if __name__ == '__main__':
    main(str(Path(sys.argv[1]).resolve()))
