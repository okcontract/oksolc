#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Compare actual native dispatcher callback traces with kernel-reduced Lean
executions. This is bounded differential evidence, not universal preservation.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys
import check_compiler as gate
from compiler_dispatch_cases import fixtures
from extract_cache import opcode_values
import extract_dispatch


def encode(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode()


def lean_trace(item, observation, opcodes, usize_bits):
    def option(value):
        return 'none' if value is None else 'some ' + str(value)

    def array(values):
        return '[' + ', '.join(map(str, values)) + ']'

    nodes = '[' + ', '.join('⟨' + option(node.get('constant')) + ', ' +
        option(opcodes[node['instruction']] if node.get('instruction') else None) + ', ' +
        array(node.get('arguments', [])) + '⟩' for node in item['nodes']) + ']'
    version = item['version']
    options = '⟨' + str(item['forYul']).lower() + ', ' + (
        'some .' + version[0].lower() + version[1:] if version else 'none') + '⟩'
    errors = {'OutOfMemory': 'outOfMemory', 'Capacity': 'capacity'}
    result = ('.error .' + errors[observation['failure']] if observation['failure'] else
              '.ok (' + option(observation['result']) + ')')
    calls = '[' + ', '.join('(' + ', '.join([str(call['kind']), str(call['opcode']),
        str(call['value']), array(call['arguments'][:call['length']]), str(call['debug'])]) + ')'
        for call in observation['calls']) + ']'
    return ('-- ' + item['name'] + '\nexample : traceMatches (run ' + nodes + ' ' +
        str(opcodes[item['instruction']]) + ' ' + array(item['arguments']) + ' ' + options + ' ' +
        str(item['failAt']) + ' ' + str(usize_bits) + ') (' + result + ') ' + calls + ' = true := by rfl\n')


def check_batch(output, cases, executable, tools, env, timeout):
    request = encode({'schema': 'oksolc.compiler-dispatch-request.v1', 'cases': [item for item, _ in cases]})
    (output / 'request.json').write_bytes(request)
    if len(request) > 1024 * 1024:
        raise ValueError('native request byte limit exceeded')
    raw = gate.require_success(output, 'native', [executable], env, timeout, data=request)
    (output / 'response.json').write_bytes(raw)
    if (output / 'native.stderr').read_bytes().strip():
        raise ValueError('unexpected native diagnostic')
    response = json.loads(raw)
    if (response['schema'] != 'oksolc.compiler-dispatch-response.v1' or
            response['requestSha256'] != hashlib.sha256(request).hexdigest() or
            response['usizeBits'] not in (16, 32, 64, 128) or
            len(response['observations']) != len(cases)):
        raise ValueError('native response scope/binding mismatch')
    opcodes = opcode_values(extract_dispatch.nested.OPCODES.read_bytes())
    generated = ('import Compiler.Extraction.DispatchTests\n'
        'open Compiler.Extraction.Dispatch Compiler.Extraction.Dispatch.Tests\n'
        'set_option maxRecDepth 8192\nset_option maxHeartbeats 1000000\n'
        'set_option exponentiation.threshold 512\n')
    for (item, expected_calls), observation in zip(cases, response['observations']):
        if observation['name'] != item['name']:
            raise ValueError('native case order mismatch')
        calls = observation['calls']
        if [call['opcode'] for call in calls] != expected_calls:
            raise ValueError(item['name'] + ': intended rule family was preempted or changed')
        expected_failure = 'OutOfMemory' if item['failAt'] else None
        if observation['failure'] != expected_failure:
            raise ValueError(item['name'] + ': wrong native failure checkpoint')
        result = observation['result']
        if (result is not None and (type(result) is not int or not 0 <= result < (1 << 32))) or (
                observation['failure'] is not None and result is not None):
            raise ValueError('invalid native result')
        for call in calls:
            if (call['kind'] not in (1, 2, 3) or call['debug'] != 42 or
                    type(call['opcode']) is not int or not 0 <= call['opcode'] < 256 or
                    type(call['value']) is not int or not 0 <= call['value'] < (1 << 256) or
                    type(call['length']) is not int or not 0 <= call['length'] <= 4 or
                    len(call['arguments']) != 4 or any(type(id) is not int or not 0 <= id < (1 << 32)
                        for id in call['arguments'])):
                raise ValueError('invalid native callback observation')
        generated += lean_trace(item, observation, opcodes, response['usizeBits'])
    (output / 'Trace.lean').write_text(generated)
    gate.require_success(output, 'compare', [tools['lake']['path'], 'env', 'lean',
        '-DwarningAsError=true', '--stdin'], env, timeout,
        data=generated.encode(), cwd=gate.ROOT / 'lean')
    if (output / 'compare.stderr').read_bytes().strip():
        raise ValueError('unexpected Lean diagnostic')
    return dict(status='passed', cases=len(cases), usizeBits=response['usizeBits'],
        injectedFailures=sum(bool(item['failAt']) for item, _ in cases),
        requestSha256=hashlib.sha256(request).hexdigest(), responseSha256=hashlib.sha256(raw).hexdigest(),
        traceSha256=hashlib.sha256(generated.encode()).hexdigest())


def check_batches(output, cases, executable, tools, env, timeout, batch_size, records):
    if not 1 <= batch_size <= 512:
        raise ValueError('batch size must be between 1 and 512')
    if not cases or len(cases) > 4096 or len({item['name'] for item, _ in cases}) != len(cases):
        raise ValueError('fixture bounds or names are invalid')
    width = None
    for index, first in enumerate(range(0, len(cases), batch_size)):
        batch = cases[first:first + batch_size]
        directory = 'batch-' + str(index).zfill(4)
        record = dict(index=index, firstCase=first, directory=directory, cases=len(batch), status='running')
        records.append(record)
        destination = output / directory
        try:
            destination.mkdir()
            result = check_batch(destination, batch, executable, tools, env, timeout)
            record.update(result)
            if width is not None and width != result['usizeBits']:
                raise ValueError('native host width changed between batches')
            width = result['usizeBits']
        except BaseException:
            record['status'] = 'failed'
            raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--lean-bin', type=Path)
    parser.add_argument('--jobs', type=int, default=4)
    parser.add_argument('--timeout', type=float, default=600)
    parser.add_argument('--batch-size', type=int, default=512, choices=range(1, 513), metavar='1..512')
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {'schema': 'oksolc.compiler-dispatch-check.v2', 'status': 'failed',
              'scope': 'boundedNativeDispatcherCallbackComparison', 'wholeCompilerVerified': False,
              'batchSize': args.batch_size, 'batches': []}
    try:
        before = gate.snapshot()
        env, _, tools = gate.source.toolchain(args.lean_bin, args.jobs)
        executable = gate.ROOT / 'zig-out/bin/compiler-dispatch-trace'
        binary_hash = gate.source.file_digest(executable)
        report['sourceSha256'], report['binarySha256'], report['tools'] = before, binary_hash, tools
        gate.require_success(output, 'model', [tools['lake']['path'], 'build',
            'Compiler.Extraction.DispatchTests'], env, args.timeout, cwd=gate.ROOT / 'lean')
        cases = fixtures()
        report.update(requestedCases=len(cases), fixtureSha256=hashlib.sha256(encode(cases)).hexdigest())
        check_batches(output, cases, executable, tools, env, args.timeout, args.batch_size, report['batches'])
        gate.require_stable(before, gate.snapshot())
        if gate.source.file_digest(executable) != binary_hash:
            raise ValueError('native adapter changed during comparison')
        for tool in tools.values():
            if gate.source.file_digest(Path(tool['path'])) != tool['sha256']:
                raise ValueError('Lean tool changed during comparison')
        report.update(status='passed', cases=len(cases),
            injectedFailures=sum(bool(item['failAt']) for item, _ in cases))
    except (Exception, KeyboardInterrupt) as error:
        report['failure'] = {'kind': type(error).__name__, 'message': str(error)}
    (output / 'report.json').write_bytes(encode(report))
    print(json.dumps({key: report[key] for key in ('status', 'scope')}))
    return 0 if report['status'] == 'passed' else 1


if __name__ == '__main__':
    sys.exit(main())
