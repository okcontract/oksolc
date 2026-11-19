#!/usr/bin/env python3
"""Check shared ordinary lookup exits against the complete actual protocol.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import json
from pathlib import Path

import caller_protocol_checks as protocol
import check_argument_memory as python_inputs
import check_native_invocation as interface
import check_recursive_nonempty as source_gate
import check_word_swap as harness
from assembly_item_creation_checks import checked_controls
from build_toolchain import digest, write_json
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NS = protocol.NS
MODULE = 'Compiler.Extraction.InternerCallerProtocolLookupTests'
CLAIMS = [NS + name for name in (
    'lookup_body', 'scoped_lookup', 'lookup_projected', 'classification_projected',
    'cached_events', 'cached_projected', 'initialization_projected', 'lookup_close_projected',
    'LookupTests.existing_family', 'Tests.cache_observed', 'Tests.cache_scope', 'Tests.cache_composed')]


def audit(rows):
    claims = {row['theorem']: set(row['dependencies']) for row in rows}
    required = {
        'lookup_body': {NS + 'findBody', protocol.native.OWNED + 'Caller.Initialization.capture_success'},
        'scoped_lookup': {'Compiler.Extraction.Interner.Scoped.findDetailed', 'Compiler.Extraction.Interner.FindCode.controlRun'},
        'lookup_projected': {NS + name for name in ('lookup_body', 'scoped_lookup', 'initialized_recorded', 'lookup_close_projected')},
        'classification_projected': {NS + 'lookup_projected'},
        'cached_events': {NS + 'lookup_body'},
        'cached_projected': {NS + 'lookup_projected'},
        'LookupTests.existing_family': {NS + 'lookup_projected', protocol.native.OWNED + 'ConstructorItem.CacheTests.prefix_observed'},
    }
    for short, needed in required.items():
        if missing := needed - claims[NS + short]:
            raise ValueError('lookup proof lost shared dependencies: ' + short + ': ' + ', '.join(sorted(missing)))
    statements = {row['theorem']: row['statement'] for row in rows}
    for short in ('lookup_projected', 'classification_projected', 'cached_projected'):
        statement = statements[NS + short]
        entries, conclusion, _ = interface.domains(statement)
        if not {'external', 'budget', 'allocator', 'source', 'before', 'leading', 'trailing', 'observations',
                'valid', 'represented', 'allocated', 'admitted', 'initialized', 'room', 'classified',
                'capacityQuery', 'classificationQuery'} <= entries.keys():
            raise ValueError('lookup proof lost general native inputs or actual source guards: ' + short)
        forbidden = {NS + name for name in ('find', 'findBody', 'finish', 'scopeView', 'lookup_projected')}
        forbidden |= {protocol.native.OWNED + name for name in ('Good', 'Closed', 'cleanup', 'finish', 'Semantic.Ensures')}
        for name, (root, _) in entries.items():
            if interface.step.constants_below(statement, root) & forbidden:
                raise ValueError('lookup proof assumes its completed invocation or cleanup: ' + short + '.' + name)
        if any(part.endswith('Tests') for dep in claims[NS + short] for part in dep.split('.')):
            raise ValueError('general lookup proof depends on a fixture')
        expected = {NS + 'find', NS + 'scopeView', 'Compiler.Extraction.Interner.Scoped.findDetailed',
                    'Compiler.Extraction.Interner.InvocationTrace.resources', protocol.native.OWNED + 'Good',
                    protocol.native.OWNED + 'Closed'}
        if not expected <= interface.step.constants_below(statement, conclusion):
            # Let-bound actual/logical calls occur before the final conjunction.
            if not expected <= {node[1] for node in statement['nodes'] if node[0] == 'const'}:
                raise ValueError('lookup result lost exact source/scoped attachment: ' + short)
    return {'checkedDependencies': sorted(NS + short for short in required),
            'checkedStatements': [NS + name for name in ('lookup_projected', 'classification_projected', 'cached_projected')],
            'successfulInitializationStillRequired': True, 'completeInvocationCorrespondenceVerified': False}


def controls(output, env, lean):
    raw = (harness.ROOT / 'lean/Compiler/Extraction/InternerCallerProtocolLookup.lean').read_text()
    source = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
    source += '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)
    mutations = [
        ('ordinary-guard', '(completed : ordinary (result.mapError Fault.language) = true)',
         '(completed : ordinary (result.mapError Fault.language) = false)', 1),
        ('cache-determinism', 'result.map (fun _ => true)', 'result.map (fun _ => false)', 3),
        ('cache-result', 'before.graph.table key = some id', 'before.graph.table key = some (id + 1)', 2),
        ('cache-key', 'Interner.makeKey request values = .ok key', 'Interner.makeKey request [] = .ok key', 3),
        ('normalized-input', '(represented : Represents before.memory.memory source request.arguments)',
         '(represented : Represents before.memory.memory source [])', 2),
        ('scratch-shape', '(.array 2 word) = .ok (pointer, memory)', '(.array 1 word) = .ok (pointer, memory)', 2),
        ('stream-order', 'resources (actual.2.events ++ trailing)', 'resources (trailing ++ actual.2.events)', 2),
        ('lost-stream', 'resources (actual.2.events ++ trailing)', 'resources trailing', 2),
        ('closed-scope', 'Closed actual.2.native.scope', '¬Closed actual.2.native.scope', 2),
        ('source-retention', 'Good source request.arguments actual.2.native.world', 'Good source [] actual.2.native.world', 2),
        ('lost-completeness', 'actual.2.tokens.incomplete = false', 'actual.2.tokens.incomplete = true', 2),
    ]
    records = checked_controls(output, [mutation_check(output, 'lookup-unchanged', source, True, env, lean)])
    for name, before, after, count in mutations:
        if source.count(before) != count:
            raise ValueError('ambiguous lookup control: ' + name)
        records += checked_controls(output, [mutation_check(output, 'lookup-' + name, source.replace(before, after), False, env, lean)])
    return records


def check(args):
    if args.entry_failures or args.take_failures or args.complete_entry:
        import caller_entry_protocol_checks as entries
    else:
        entries = None
    if args.take_failures or args.complete_entry:
        import caller_take_protocol_checks as takes
    else:
        takes = None
    if args.complete_entry:
        import caller_complete_protocol_checks as complete
    else:
        complete = None
    module = complete.MODULE if complete else (takes.MODULE if takes else (entries.MODULE if entries else MODULE))
    claims = list(dict.fromkeys(CLAIMS + (entries.CLAIMS if entries else []) + (takes.CLAIMS if takes else [])
        + (complete.CLAIMS if complete else [])))
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {'schema': 'oksolc.caller-lookup-protocol.v1', 'status': 'failed', 'jobs': 4,
              'scope': 'complete recorded cache and ordinary classification exits after actual successful initialization',
              'preflightOnly': args.preflight, 'nativeZigGateRun': False,
              'completeInvocationCorrespondenceVerified': False, 'recursiveInductionVerified': False,
              'composedProductionTheoremVerified': False, 'wholeCompilerVerified': False}
    if entries:
        report['scope'] += '; capacity and initialization failures through actual item/scratch return'
        report['earlyEntryProtocolVerified'] = False
    if takes:
        report['scope'] += '; refused borrowing through actual item return'
        report['takeFailureProtocolVerified'] = False
    if complete:
        report['scope'] += '; general caller and all five finite constructor entries; item continuation from local proper-child and replay bindings'
        report['conditionalAllEntryProtocolVerified'] = False
        report['conditionalItemEntryProtocolVerified'] = False
        report['conditionalConstructorEntriesVerified'] = False
        report['itemContinuationDerived'] = False
    try:
        report['inputs'] = python_inputs.inputs()
        report['leanInputs'] = harness.lean_check.source_inputs()
        frozen = source_gate.inputs()
        write_json(output / 'inputs.json', frozen)
        library = args.zig_lib_dir.resolve()
        std, profiles = source_gate.std_inputs(library), source_gate.profiles(library)
        write_json(output / 'std-inputs.json', std)
        write_json(output / 'source-profiles.json', profiles)
        env, _, report['tools'] = harness.lean_check.toolchain(args.lean_bin, 4)
        lean = report['tools']['lean']['path']
        report['audit'] = harness.audit(output, env, lean, module, claims)
        rows = json.loads((output / 'audit.json').read_bytes())['claims']
        report['interfaces'] = audit(rows)
        if entries:
            report['entryInterfaces'] = entries.audit(rows)
        if takes:
            report['takeInterfaces'] = takes.audit(rows)
        if complete:
            report['completeInterfaces'] = complete.audit(rows, complete.continuation_export(output, env, lean))
        report['controls'] = controls(output, env, lean) + protocol.controls(output, env, lean)
        if entries:
            report['controls'] += entries.controls(output, env, lean)
        if takes:
            report['controls'] += takes.controls(output, env, lean)
        if complete:
            report['controls'] += complete.controls(output, env, lean)
        print('Cached lookup audit and semantic controls passed.', flush=True)
        if not args.preflight:
            proof, artifacts = harness.prove.check_module(module, claims, lean_bin=args.lean_bin, jobs=4, fresh=True, timeout=1800)
            for name, data in artifacts.items():
                (output / ('proof-' + name)).write_bytes(data)
            if (proof.get('status') != 'passed' or proof.get('freshKernelReplay') is not True
                    or proof.get('replayIncludesImports') is not True or proof.get('buildInputs') != report['leanInputs']):
                raise ValueError('fresh imported lookup replay failed or inputs differ: ' + str(proof.get('failure')))
            report['proof'] = {'sha256': digest(output / 'proof-report.json'), 'roots': len(claims),
                               'freshKernelReplay': True, 'replayIncludesImports': True}
        if (report['inputs'] != python_inputs.inputs() or report['leanInputs'] != harness.lean_check.source_inputs()
                or frozen != source_gate.inputs() or profiles != source_gate.profiles(library) or std != source_gate.std_inputs(library)):
            raise ValueError('lookup acceptance inputs changed during the run')
        report['frozenNativeInputs'] = len(frozen)
        report['zigLibrary'] = {'path': str(library), 'inputs': len(std), 'sha256': digest(output / 'std-inputs.json')}
        if entries:
            report['earlyEntryProtocolVerified'] = not args.preflight
        if takes:
            report['takeFailureProtocolVerified'] = not args.preflight
        if complete:
            report['conditionalAllEntryProtocolVerified'] = not args.preflight
            report['conditionalItemEntryProtocolVerified'] = not args.preflight
            report['conditionalConstructorEntriesVerified'] = not args.preflight
            report['itemContinuationDerived'] = not args.preflight
        report['status'] = 'passed'
    finally:
        write_json(output / 'report.json', report)
    print(json.dumps({'status': report['status'], 'roots': len(claims), 'controls': len(report['controls']),
                      'preflightOnly': args.preflight}))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-bin', type=Path, required=True)
    parser.add_argument('--zig-lib-dir', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--preflight', action='store_true')
    parser.add_argument('--entry-failures', action='store_true', help='also check capacity and initialization failure through item return')
    parser.add_argument('--take-failures', action='store_true', help='also check refused borrowing, shared prefixes and successful-path regressions')
    parser.add_argument('--complete-entry', action='store_true', help='also check general caller composition and all five finite constructor entries')
    check(parser.parse_args())
