#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Development-only recursive DSL validation/model and independent EVM checks.
This prerequisite does not claim automatic recursive Solidity translation.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import gzip
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

from check_export import ROOT, compile_request, request
from check_execution import chain, rpc, transact, word, selector

sys.path.insert(0, str(ROOT/'lean'))
import environment as source_check


def canonical(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':'))+'\n').encode()


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def trace_result(trace):
    assert trace['structLogs'], 'opcode tracing is required to distinguish revert from exception'
    terminal = trace['structLogs'][-1]['op']
    return {'kind': ('revert' if terminal == 'REVERT' else 'exceptional') if trace['failed'] else 'success',
            'data': trace['returnValue'].removeprefix('0x')}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert not args.output.exists()
    paths = sorted((ROOT/'lean/Contract').rglob('*.lean')) + [
        ROOT/'lean/Tests/RecursiveHelpers.lean', ROOT/'lean/solidity/library.json',
        ROOT/'test/lean/fixtures/RecursiveHelpers.sol', Path(__file__).resolve(),
        ROOT/'test/lean/check_export.py', ROOT/'test/lean/check_execution.py', ROOT/'lean/environment.py']
    frozen = {str(p.relative_to(ROOT)): digest(p) for p in paths}
    commands = {'native': [str(ROOT/'zig-out/bin/oksolc'), 'standard-json', '-'],
                'official': [shutil.which('solc'), '--standard-json']}
    binaries = {name: Path(cmd[0]).resolve() for name, cmd in commands.items()}
    binaries.update(anvil=Path(shutil.which('anvil')).resolve(), cast=Path(shutil.which('cast')).resolve())
    env, _, lean_tools = source_check.toolchain(None, 4)
    binaries.update({name: Path(tool['path']) for name, tool in lean_tools.items()})
    binary_hashes = {name: digest(p) for name, p in binaries.items()}
    versions = {name: subprocess.run([str(path), '--version'], check=True, capture_output=True,
                                    text=True).stdout.strip() for name, path in binaries.items()}
    assert '0.8.36+' in versions['official'] and '4.29.0' in versions['lean']
    logs = {}

    def lean(label, command):
        run = subprocess.run([str(binaries['lake']), *command], cwd=ROOT/'lean', capture_output=True,
                             timeout=600, env=env)
        logs[label] = {'stdout': run.stdout.decode(), 'stderr': run.stderr.decode(), 'exitCode': run.returncode}
        assert run.returncode == 0, logs[label]
        return run.stdout

    lean('build', ['build', 'Tests.RecursiveHelpers'])
    preflight = json.loads(lean('model', ['env', 'lean', '--run', 'Tests/RecursiveHelpers.lean']).splitlines()[-1])
    assert preflight['graphChecks'] == 87040 and preflight['modelChecks'] == 59
    original = ROOT/'test/lean/fixtures/RecursiveHelpers.sol'
    source_request = {'language': 'Solidity', 'sources': {'RecursiveHelpers.sol': {'content': original.read_text()}},
        'settings': {'viaIR': True, 'evmVersion': 'cancun', 'optimizer': {'enabled': True, 'runs': 200},
                     'outputSelection': {'*': {'*': ['abi', 'evm.bytecode.object', 'evm.deployedBytecode.object']}}}}
    source_output = compile_request(commands['official'], source_request)

    def compile_one(item):
        name, optimize = item
        payload = request(preflight['artifact'])
        payload['settings']['optimizer']['enabled'] = optimize
        return name+('/optimized' if optimize else '/plain'), {
            'request': payload, 'response': compile_request(commands[name], payload)}

    with ThreadPoolExecutor(max_workers=4) as pool:
        compiled = dict(pool.map(compile_one, [(name, opt) for name in commands for opt in [False, True]]))
    for mode in ['plain', 'optimized']:
        assert compiled['native/'+mode]['response']['contracts'] == compiled['official/'+mode]['response']['contracts']
    cases = []
    mask = 2**256-1
    for n in [*range(25), 31, 32, 63]:
        cases.append((f'sum-{n}', selector('sumTo(uint256)')+word(n), 0, 'success', word(n*(n+1)//2), None))
        cases.append((f'parity-{n}', selector('parity(uint256)')+word(n), 0, 'success', word(1-n%2)+word(n%2), None))
        for initial in [0, 17, mask]:
            expected = (initial+n*(n+1)) & mask
            cases.append((f'memory-{n}-{initial}', selector('memorySum(uint256,uint256)')+word(n)+word(initial),
                          0, 'success', word(expected)*2, None))
    for n in [0, 1, 2, 5, 17, 32]:
        for mode in range(6):
            kind = 'revert' if mode == 1 else 'exceptional' if mode == 2 else 'success'
            data = word(57005) if mode in [1, 3] else '' if mode in [2, 4] else word(n*(n+1)//2)
            cases.append((f'effects-{n}-{mode}', selector('effects(uint256,uint256)')+word(n)+word(mode),
                          0, kind, data, (n, mode)))
    for name, data in [('sum-stack', selector('sumTo(uint256)')+word(10000)),
                       ('effects-stack', selector('effects(uint256,uint256)')+word(10000)+word(0)),
                       ('diverge', selector('diverge()'))]:
        cases.append((name, data, 0, 'exceptional', '', None))
    for name, data, value in [('short', '00', 0), ('unknown', 'ffffffff', 0),
                              ('short-arg', selector('sumTo(uint256)'), 0),
                              ('nonpayable', selector('sumTo(uint256)')+word(1), 1)]:
        cases.append((name, data, value, 'revert', '', None))
    observations = {}
    opts = {'disableMemory': True, 'disableStack': True, 'disableStorage': True}
    for key, artifact in compiled.items():
        codes = {'source': source_output['contracts']['RecursiveHelpers.sol']['RecursiveHelpers']['evm'],
                 'lean': artifact['response']['contracts']['RecursiveHelpers.yul']['RecursiveHelpers']['evm']}
        with chain(str(binaries['anvil']), accounts=2, steps_tracing=True, hardfork='cancun') as url:
            sender = rpc(url, 'eth_accounts', [])[0]
            addresses, deployments = {}, {}
            for role, code in codes.items():
                assert 0 < len(code['deployedBytecode']['object'])//2 <= 24576
                _, deployment = transact(url, sender, code['bytecode']['object'], gas=8_000_000)
                assert deployment['status'] == '0x1', deployment
                addresses[role] = deployment['contractAddress']
                assert rpc(url, 'eth_getCode', [addresses[role], 'latest']) == '0x'+code['deployedBytecode']['object']
                deployments[role] = deployment
            rows = []
            for name, data, value, kind, expected, effect in cases:
                paired = {}
                for role, address in addresses.items():
                    before = [rpc(url, 'eth_getStorageAt', [address, hex(slot), 'latest']) for slot in [0, 1]]
                    tx = {'from': sender, 'to': address, 'data': '0x'+data, 'gas': hex(2_000_000), 'value': hex(value)}
                    traced = rpc(url, 'debug_traceCall', [tx, 'latest', opts])
                    observed = trace_result(traced)
                    assert observed == {'kind': kind, 'data': expected}, (key, name, role, observed)
                    _, receipt = transact(url, sender, data, address, value=value, gas=2_000_000)
                    executed = rpc(url, 'debug_traceTransaction', [receipt['transactionHash'], opts])
                    if trace_result(executed) != observed:
                        failure = {'artifact': key, 'case': name, 'role': role, 'transaction': tx,
                                   'call': traced, 'execution': executed, 'receipt': receipt,
                                   'sourceRequest': source_request, 'sourceResponse': source_output,
                                   'compiled': artifact, 'binaryHashes': binary_hashes, 'inputHashes': frozen}
                        args.output.parent.mkdir(parents=True, exist_ok=True)
                        args.output.with_suffix('.failure.json.gz').write_bytes(gzip.compress(canonical(failure), mtime=0))
                        raise AssertionError((key, name, role, observed, trace_result(executed)))
                    assert (receipt['status'] == '0x1') == (kind == 'success')
                    after = [rpc(url, 'eth_getStorageAt', [address, hex(slot), 'latest']) for slot in [0, 1]]
                    balance = rpc(url, 'eth_getBalance', [address, 'latest'])
                    assert int(balance, 16) == 0
                    log_values = [{'topics': x['topics'], 'data': x['data']} for x in receipt['logs']]
                    if effect and kind == 'success':
                        n, mode = effect
                        assert [int(s, 16) for s in after] == [int(before[0], 16)+n+1,
                            int(before[1], 16)+(0 if mode in [3, 4] else n*(n+1)//2)]
                        assert log_values == [{'topics': ['0x'+word(7)], 'data': '0x'+word(i)} for i in range(n, -1, -1)]
                    else:
                        assert before == after and log_values == [], (name, before, after, log_values)
                    paired[role] = {**observed, 'before': before, 'after': after, 'logs': log_values, 'balance': balance,
                                    'gasUsed': receipt['gasUsed'], 'receipt': receipt,
                                    'effects': [s['op'] for s in executed['structLogs'] if s['op'] in ['SSTORE', 'LOG1']],
                                    'traceSha256': hashlib.sha256(canonical(executed)).hexdigest(),
                                    'rawCall': {k: v for k, v in traced.items() if k != 'structLogs'},
                                    'rawExecution': {k: v for k, v in executed.items() if k != 'structLogs'}}
                for field in ['kind', 'data', 'before', 'after', 'logs', 'balance']:
                    assert paired['source'][field] == paired['lean'][field], (key, name, field)
                rows.append({'name': name, 'calldata': data, 'value': value, 'observations': paired})
            observations[key] = {'deployments': deployments, 'cases': rows}
            print(key, len(rows), 'exact comparisons passed', flush=True)
    assert all(digest(ROOT/name) == sha for name, sha in frozen.items())
    assert all(digest(binaries[name]) == sha for name, sha in binary_hashes.items())
    args.output.mkdir(parents=True)
    report = {'scope': 'recursive DSL runtime prerequisite; no automatic Solidity or Chainwall acceptance claim',
              'workers': 4, 'compilerBuildMode': 'ReleaseFast', 'preflight': preflight, 'logs': logs,
              'sourceRequest': source_request, 'sourceResponse': source_output, 'compiled': compiled,
              'observations': observations, 'inputHashes': frozen, 'binaryHashes': binary_hashes, 'versions': versions,
              'environment': {'hardfork': 'cancun', 'chainId': 31337, 'transactionGas': 2000000,
                              'deploymentGas': 8000000, 'stepsTracing': True, 'codeSizeLimit': 24576},
              'exactPairs': len(compiled)*len(cases), 'finalBytecode': 'notProved'}
    (args.output/'execution.json.gz').write_bytes(gzip.compress(canonical(report), mtime=0))
    print(report['exactPairs'], 'exact pairs;', preflight['graphChecks'], 'graph checks;',
          preflight['modelChecks'], 'model cases;', preflight['validationChecks'], 'validation checks', flush=True)


if __name__ == '__main__':
    main()
