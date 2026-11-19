#!/usr/bin/env python3
"""Check all-entry native invocation preservation under reached local obligations.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import json
import re
from pathlib import Path

import check_argument_memory as python_inputs
import check_recursive_nonempty as source_gate
import check_word_swap as harness
import native_step_checks as step
import native_suffix_word_checks as suffix
import native_candidate_field_checks as candidate
from assembly_item_creation_checks import checked_controls
from build_toolchain import digest, write_json
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
from lean_control_matrix import ControlPlan

NS, ITEM, OWNED = step.NS, step.arguments.ITEM, step.arguments.OWNED
MODULE = 'Compiler.Extraction.InternerNativeSuffixWords'
CLAIMS = step.CLAIMS + [NS + name for name in ('TakenObligations.observed', 'step_invocation_verified_observed', 'step_invocation_verified')] + suffix.CLAIMS + candidate.CLAIMS


def domains(statement):
    if statement.get('encoding') != 'kernelExprDag-v1':
        raise ValueError('unsupported invocation expression encoding')
    nodes, index, context, result = statement['nodes'], statement['root'], [], {}
    while nodes[index][0] in ('forall', 'lambda', 'let'):
        node = nodes[index]
        if node[0] != 'let':
            result[node[1]] = (node[3], context[:])
        context.append(node[1])
        index = node[4]
    return result, index, context


def applied(statement, index):
    nodes, args = statement['nodes'], []
    while nodes[index][0] == 'app':
        args.append(nodes[index][2])
        index = nodes[index][1]
    return nodes[index], list(reversed(args))


def named(statement, index, context):
    node = statement['nodes'][index]
    if node[0] == 'bound':
        return context[-int(node[1]) - 1]
    if node[0] == 'const':
        return node[1]
    if node[0] == 'app':
        return ('app', named(statement, node[1], context), named(statement, node[2], context))
    if node[0] == 'projection':
        return ('projection', node[1], node[2], named(statement, node[3], context))
    return tuple(node)


def interface_export(output, env, lean, module=MODULE, names=('InvocationPost', 'TakenObligations.mk')):
    source = 'import ' + module + '''
import Contract.Check.Declarations
import Lean.Elab.Command
open Lean Elab Command Contract.Check in
run_cmd do
  let mut records := #[]
  for name in #[
''' + ',\n'.join('    ``' + (name if name.startswith('Compiler.') else NS + name) for name in names) + '''] do
    let some info := (← getEnv).find? name | throwError "missing interface: {name}"
    records := records.push (Declarations.encode info)
  liftIO <| IO.println (Json.arr records).compress
'''
    (output / 'interfaces.lean').write_text(source)
    harness.run(output, 'interfaces', [lean, '-DwarningAsError=true', output / 'interfaces.lean'],
                cwd=harness.ROOT / 'lean', env=env)
    raw = (output / 'interfaces.stdout').read_bytes()
    (output / 'interfaces.json').write_bytes(raw)
    return json.loads(raw)


def audit_entry_statement(statement, observed=False):
    entries, conclusion, _ = domains(statement)
    required = {'safety', 'owner', 'usizeBits', 'capacity', 'base', 'host', 'children',
                'source', 'request', 'debug', 'before', 'data', 'rows', 'parent', 'env', 'other', 'expected',
                'external', 'facts', 'represented', 'privateSource', 'admitted', 'domain', 'typed',
                'valid', 'evaluated', 'retained', 'localParent', 'takenObligations'}
    if not observed:
        required |= {'modelChildren', 'modelSeed'}
    elif {'cursor', 'modelChildren', 'modelSeed'} & entries.keys():
        raise ValueError('observed entry fixes child data before branch selection')
    if not required <= entries.keys():
        raise ValueError('invocation lost general inputs or explicit local obligations')
    if {'made', 'room', 'allocated', 'initialized', 'classified', 'keyed', 'missed', 'transferred'} & entries.keys():
        raise ValueError('invocation regained a successful-prefix premise')
    forbidden = {NS + name for name in ('InvocationPost', 'Returns', 'FramePost', 'GraphFrame', 'step_invocation_verified', 'step_invocation_verified_observed')}
    forbidden |= {ITEM + 'invoke', NS + 'step', OWNED + 'Semantic.Ensures'}
    for name, (root, _) in entries.items():
        constants = step.constants_below(statement, root)
        if forbidden & constants or any(part.endswith('Tests') for dep in constants for part in dep.split('.')):
            raise ValueError('invocation assumes its final result/frame or a fixture: ' + name)
    if not {NS + 'InvocationPost', NS + 'GraphFrame', NS + 'step', OWNED + 'Semantic.Ensures'} <= step.constants_below(statement, conclusion):
        raise ValueError('invocation lost native-step attachment or preservation result')
    obligation = entries['takenObligations'][0]
    needed = {ITEM + 'prepare', OWNED + 'Caller.Queries.atCapacity', 'Compiler.ZigAir.Memory.allocate',
              OWNED + 'Caller.initLookup', OWNED + 'Caller.Queries.deterministic', step.INTERNER + 'makeKey',
              OWNED + 'take', OWNED + 'Insertion.Native.CallerInput', NS + ('TakenObligationsAt' if observed else 'TakenObligations')}
    if not needed <= step.constants_below(statement, obligation):
        raise ValueError('taken obligations lost an actual prefix observation')

    if observed:
        index, context = entries['takenObligations']
        while statement['nodes'][index][0] in ('forall', 'let'):
            node = statement['nodes'][index]
            context = context + [node[1]]
            index = node[4]
        for witness in ('cursor', 'modelChildren'):
            head, args = applied(statement, index)
            if head[:2] != ['const', 'Exists']:
                raise ValueError('reached miss lost local existential child data')
            node = statement['nodes'][args[-1]]
            if node[0] != 'lambda' or node[1] != witness:
                raise ValueError('reached miss changed its local witness: ' + witness)
            context = context + [node[1]]
            index = node[4]
        head, args = applied(statement, index)
        if (head[:2] != ['const', NS + 'TakenObligationsAt'] or named(statement, args[1], context) != 'cursor'
                or named(statement, args[7], context) != 'modelChildren'):
            raise ValueError('observed obligations do not bind the chosen cursor and child model')


def audit_statements(rows, interfaces):
    inherited = step.audit_statements(rows)
    statements = {row['theorem']: row['statement'] for row in rows}
    audit_entry_statement(statements[NS + 'step_invocation_verified'])
    audit_entry_statement(statements[NS + 'step_invocation_verified_observed'], observed=True)

    definitions = {record['name']: record for record in interfaces}
    post = definitions[NS + 'InvocationPost']['value']
    if definitions[NS + 'InvocationPost']['kind'] != 'definition':
        raise ValueError('invocation post is no longer a definition')
    post_entries, post_body, context = domains(post)
    guard, guard_context = next(reversed(post_entries.values()))
    head, args = applied(post, guard)
    if head[:2] != ['const', 'Eq'] or len(args) != 3 or named(post, args[-1], guard_context) != 'Bool.true':
        raise ValueError('invocation post lost its ordinary-completion guard')
    if OWNED + 'ordinary' not in step.constants_below(post, args[-2]):
        raise ValueError('invocation post guard does not inspect the actual outcome')
    if not {OWNED + 'Closed', OWNED + 'Semantic.Ensures'} <= step.constants_below(post, post_body):
        raise ValueError('invocation post lost closure or word preservation')

    audit_taken_fields(definitions, statements[NS + 'invoke_step_verified'])
    audit_taken_fields(definitions, statements[NS + 'invoke_step_verified'], observed=True)
    return {'sharedStep': inherited, 'nativeFrame': step.frames.audit_definitions(interfaces), 'nativeWords': step.words.audit_definitions(interfaces),
            'checkedGeneralInterface': NS + 'step_invocation_verified',
            'checkedObservedInterface': NS + 'step_invocation_verified_observed', 'childDataChosenAtReachedMiss': True,
            'successfulEntryPrefixNotAssumed': True, 'onlyReachedMissRequiresChildAndSuffixContracts': True,
            'actualBorrowedStepAttached': True, 'nativeFrameAndWordPostForAllOrdinaryEntryRoutes': True,
            'completeStreamCorrespondenceVerified': False, 'allConstructorFieldsVerified': False,
            'recursiveInductionVerified': False, 'composedProductionTheoremVerified': False}


def audit_taken_fields(definitions, reference, observed=False):
    constructor = definitions[NS + ('TakenObligationsAt.mk' if observed else 'TakenObligations.mk')]
    if constructor['kind'] != 'constructor':
        raise ValueError('taken obligations are no longer explicit fields')
    fields = constructor['type']
    field_entries, _, _ = domains(fields)
    reference_entries, _, _ = domains(reference)
    ref_root, ref_context = reference_entries['dispatchCoupled']
    ref_guard = reference['nodes'][ref_root][3]
    expected = named(reference, ref_guard, ref_context)
    _, guard_args = applied(reference, ref_guard)
    condition = named(reference, guard_args[-2], ref_context)
    for name in ('coupled', 'correct', 'addresses', 'shifts') + (() if observed else ('publishWords',)):
        root, context = field_entries[name]
        if fields['nodes'][root][0] != 'forall' or named(fields, fields['nodes'][root][3], context) != expected:
            raise ValueError('taken field lost the actual simplification guard: ' + name)
    suffixes = (('frames', 'MissFrames'), ('words', 'MissWords')) if observed else (('suffixes', 'MissSteps'),)
    for field, kind in suffixes:
        root, context = field_entries[field]
        head, args = applied(fields, root)
        if (head[:2] != ['const', NS + kind] or named(fields, args[-2], context) != 'deterministic'
                or named(fields, args[-1], context) != condition):
            raise ValueError('taken suffixes lost the actual classifier or branch: ' + field)
    if {'kept', 'initial', 'ready'} & field_entries.keys():
        raise ValueError('taken obligations regained an initial native/parent frame premise')
    checked = ('coupled', 'frames', 'words', 'correct', 'addresses', 'shifts') if observed else ('coupled', 'suffixes', 'correct', 'addresses', 'shifts', 'insertWords', 'publishWords')
    for name in checked:
        constants = step.constants_below(fields, field_entries[name][0])
        if constants & {NS + 'InvocationPost', ITEM + 'invoke', NS + 'step', OWNED + 'Semantic.Ensures'}:
            raise ValueError('taken field assumes whole-invocation preservation: ' + name)
    if observed:
        if 'modelSeed' in field_entries:
            raise ValueError('observed entry regained a raw suffix model')
        for name in checked:
            constants = step.constants_below(fields, field_entries[name][0])
            if {OWNED + 'Recursive.projection', NS + 'Returns', NS + 'MissSteps'} & constants:
                raise ValueError('observed local obligations require raw correspondence')
        observations = step.frames.projection_observers(fields, *field_entries['coupled'])
        if len(observations) != 1:
            raise ValueError('observed local child relation missing')
        root, context = observations[0]
        head, args = applied(fields, root)
        if head[:2] != ['const', OWNED + 'Recursive.cursorGraph'] or named(fields, args[-1], context) != 'cursor':
            raise ValueError('local proper-child relation does not use its chosen cursor')


def audit(claims):
    inherited = step.audit(claims)
    name = NS + 'step_invocation_verified'
    required = {NS + n for n in ('InvocationPost', 'TakenObligations', 'TakenObligations.observed', 'step_invocation_verified_observed', 'step_invocation_verified_miss', 'taken_miss_verified_cursor', 'GraphFrame.locals',
                                'invocation_entry', 'EntryLeaf.parent', 'EntryLeaf.words', 'step')}
    required |= {ITEM + n for n in ('prepare_success', 'prepare_scratch', 'caller_input', 'invoke_rejected',
                                   'invoke_init_rejected', 'invoke_classification_rejected', 'invoke_entry_failed_native',
                                   'invoke_initialized_native', 'invoke_cached_native', 'invoke_take_failed_native')}
    required.add(OWNED + 'Caller.initialized_key')
    required |= {ITEM + 'ProtocolTrace.TakenSite.Reached.' + name for name in ('native_inputs', 'key_value', 'return_verified')}
    if missing := required - claims[name]:
        raise ValueError('all-entry step lost a source route or shared proof: ' + ', '.join(sorted(missing)))
    if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
        raise ValueError('all-entry step depends on a fixture')
    observed = NS + 'step_invocation_verified_observed'
    local_required = (required - {NS + 'TakenObligations', NS + 'TakenObligations.observed', observed}) | {NS + 'TakenObligationsAt'}
    if missing := local_required - claims[observed]:
        raise ValueError('observed entry lost source routes or native composition: ' + ', '.join(sorted(missing)))
    adapter = NS + 'TakenObligations.observed'
    if not {NS + 'TakenObligationsAt', NS + 'MissSteps.frames', NS + 'MissSteps.words'} <= claims[adapter]:
        raise ValueError('raw entry no longer supplies the shared native frame/word data')
    if any(part.endswith('Tests') for root in (observed, adapter) for dep in claims[root] for part in dep.split('.')):
        raise ValueError('observed entry depends on a fixture')
    return {'sharedStep': inherited, 'checkedDependencies': [name, observed, adapter], 'allEntryRouteCompositionVerified': True,
            'completeStreamCorrespondenceVerified': False, 'recursiveInductionVerified': False,
            'composedProductionTheoremVerified': False}


def mutation_cases():
    raw = (harness.ROOT / 'lean/Compiler/Extraction/InternerNativeInvocation.lean').read_text()
    preparation = (harness.ROOT / 'lean/Compiler/Extraction/AssemblyItemConstructorLocal.lean').read_text()
    preparation = preparation[preparation.index('theorem prepare_error_nonordinary'):preparation.rindex('\nend ')]
    source = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
    source += '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n'
    source += 'namespace ' + ITEM[:-1] + '\nopen Compiler.Algebraic Compiler.Extraction.Cache\n'
    source += 'open Compiler.ZigAir.Memory.WordArray AssemblyItem.Fields\n' + preparation + '\nend ' + ITEM[:-1] + '\n'
    source += without_imports(raw)
    source = re.sub(r'\bprepare_error_nonordinary\b', 'prepare_error_nonordinaryMutation', source)
    mutations = [
        ('wrong-local-child-cursor', '(projectionAt (cursorGraph cursor) (CallFrame',
         '(projectionAt (cursorGraph (fun _ => 0)) (CallFrame', 1),
        ('shift-entry-cursor', '∃ cursor modelChildren, TakenObligationsAt cursor safety',
         '∃ (cursor : World (Publication.Effects σ) → Nat), ∃ modelChildren, TakenObligationsAt (fun world => cursor world + 1) safety', 1),
        ('rewind-raw-adapter', 'TakenObligationsAt (fun world => world.graph.allocationCursor)',
         'TakenObligationsAt (fun _ => 0)', 1),
        ('admit-rejection', 'ordinary actual.1 = true → Closed', 'ordinary actual.1 = false → Closed', 1),
        ('leave-locals-open', 'ordinary actual.1 = true → Closed', 'ordinary actual.1 = true → ¬Closed', 1),
        ('rewind-word-graph', 'Semantic.Ensures meaning before actual.1 actual.2.world.graph',
         'Semantic.Ensures meaning before actual.1 before', 1),
        ('invent-word', 'before actual.1 actual.2.world.graph\n      (fun id after => after.read id = some expected)',
         'before actual.1 actual.2.world.graph\n      (fun id after => after.read id = some (expected + 1))', 1),
        ('wrong-suffix-classifier', 'key normalized lookup deterministic (deterministic &&',
         'key normalized lookup (!deterministic) (deterministic &&', 3),
        ('wrong-word-classifier', '(modelSeed.insert key deterministic) heap', '(modelSeed.insert key (!deterministic)) heap', 1),
        ('rewind-parent-law', 'Retains before after → parent after', 'Retains before after → parent before', 3),
        ('wrong-taken-classification', 'base.queries.deterministic request.item = .ok deterministic →',
         'base.queries.deterministic request.item = .ok (!deterministic) →', 2),
        ('skip-miss-observation', '(deterministic = true → constructed.graph.table key = none) →',
         '(deterministic = false → constructed.graph.table key = none) →', 2),
        ('wrong-taken-key', 'Interner.makeKey request values = .ok key →',
         'Interner.makeKey request [] = .ok key →', 2),
        ('wrong-source-values', '(represented : Represents before.memory.memory source request.arguments)',
         '(represented : Represents before.memory.memory source [])', 3),
        ('reject-preparation-as-ordinary', 'ordinary (.error fault : Except Fault NodeId) = false := by',
         'ordinary (.error fault : Except Fault NodeId) = true := by', 1),
        ('rewind-native-step-word', 'before.graph ran.1 ran.2.graph\n            (fun id after => after.read id = some expected)',
         'before.graph ran.1 before.graph\n            (fun id after => after.read id = some expected)', 3),
    ]
    for field in ('coupled', 'correct', 'addresses', 'shifts', 'publishWords'):
        mutations.append(('wrong-' + field + '-guard',
            field + ' : (deterministic && (request.item.kind == 1)) = true →',
            field + ' : (deterministic && (request.item.kind == 1)) = false →', 1 if field == 'publishWords' else 2))
    return source, mutations


def controls(output, env, lean):
    source, mutations = mutation_cases()
    records = checked_controls(output, [mutation_check(output, 'invocation-unchanged', source, True, env, lean)])
    for name, before, after, count in mutations:
        if source.count(before) != count:
            raise ValueError('ambiguous invocation control: ' + name)
        records += checked_controls(output, [mutation_check(output, 'invocation-' + name,
            source.replace(before, after), False, env, lean)])
    return step.controls(output, env, lean) + records


def control_plan(output, env, lean, constructors=None):
    plan = ControlPlan(output, env, lean)
    records = controls(output, env, plan) + suffix.controls(output, env, plan) + candidate.controls(output, env, plan)
    if constructors:
        records += constructors.controls(output, env, plan)
    return plan.seal(records)


def check(args):
    if args.constructors:
        import native_constructor_checks as constructors
    else:
        constructors = None
    module = constructors.MODULE if constructors else MODULE
    claims = CLAIMS + (constructors.CLAIMS if constructors else [])
    names = (suffix.INSERTION + 'CandidateWords', suffix.INSERTION + 'PushValues') + candidate.INTERFACES + ('InvocationPost', 'TakenObligations.mk', 'FramePost', 'MissFrames.mk', 'MissWords.mk', 'TakenObligationsAt.mk') + (('ConstructorPost', 'EntryObligations.mk', 'ObservedEntryObligations.mk', 'TakenFramesAt.mk', 'EntryFrames.mk') + constructors.INTERFACES if constructors else ())
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {'schema': 'oksolc.native-invocation-acceptance.v1', 'status': 'failed', 'jobs': 4,
              'scope': 'all ordinary native item-entry routes under proper-child and reached local suffix obligations',
              'preflightOnly': args.preflight, 'nativeZigGateRun': False,
              'observedChildFramePreservationVerified': False,
              'observedChildWordPreservationVerified': False,
              'observedAllEntryPreservationVerified': False,
              'nativeSuffixWordPreservationVerified': False,
              'nativeCandidateWordBindingVerified': False,
              'completeStreamCorrespondenceVerified': False, 'allConstructorFieldsVerified': False,
              'recursiveInductionVerified': False, 'composedProductionTheoremVerified': False}
    if constructors:
        report.update(schema='oksolc.native-constructor-acceptance.v1',
                      scope='all five native constructor entries under proper-child and reached local suffix obligations',
                      allConstructorEntryPreservationVerified=False, observedConstructorEntryPreservationVerified=False,
                      nativeConstructorSuffixWordsVerified=False, jointItemPreservationVerified=False,
                      jointConstructorPreservationVerified=False, finiteJointConstructorPreservationVerified=False, entryReplayModelConstructed=False,
                      enclosingParentFramesDerived=False, sourceProvenanceCarried=False, earlyInsertionFailureFramesDerived=False,
                      allEntryNativeFrameInductionVerified=False,
                      successfulInsertionFramesDerived=False, publicationRollbackFramesDerived=False, bothPreparationFramesDerived=False, bothBackingFramesDerived=False, transferredGrowthFramesDerived=False, transferredFirstAndSpareFramesDerived=False)
    try:
        report['inputs'] = python_inputs.inputs()
        report['leanInputs'] = harness.lean_check.source_inputs()
        frozen = source_gate.inputs()
        write_json(output / 'inputs.json', frozen)
        library = args.zig_lib_dir.resolve()
        std = source_gate.std_inputs(library)
        profiles = source_gate.profiles(library)
        write_json(output / 'std-inputs.json', std)
        write_json(output / 'source-profiles.json', profiles)
        env, _, report['tools'] = harness.lean_check.toolchain(args.lean_bin, 4)
        lean = report['tools']['lean']['path']
        report['audit'] = harness.audit(output, env, lean, module, claims)
        exported = json.loads((output / 'audit.json').read_bytes())['claims']
        interfaces = interface_export(output, env, lean, module, names)
        report['interfacesSha256'] = digest(output / 'interfaces.json')
        report['statements'] = audit_statements(exported, interfaces)
        report['dependencies'] = audit({row['theorem']: set(row['dependencies']) for row in exported})
        report['nativeSuffixWords'] = suffix.audit(exported, interfaces)
        report['nativeCandidateFields'] = candidate.audit(exported, interfaces)
        if constructors:
            report['constructorStatements'] = constructors.audit_statements(exported, interfaces)
            report['constructorDependencies'] = constructors.audit({row['theorem']: set(row['dependencies']) for row in exported})
        plan = control_plan(output, env, lean, constructors)
        report['controls'], report['controlMatrix'] = plan.run(getattr(args, 'control_jobs', 4))
        print('Cached audit and invocation controls passed.', flush=True)
        if not args.preflight:
            proof, artifacts = harness.prove.check_module(module, claims, lean_bin=args.lean_bin,
                                                         jobs=4, fresh=True, timeout=1800)
            for name, data in artifacts.items():
                (output / ('proof-' + name)).write_bytes(data)
            if (proof.get('status') != 'passed' or not proof.get('freshKernelReplay')
                    or not proof.get('replayIncludesImports') or proof.get('buildInputs') != report['leanInputs']):
                raise ValueError('fresh invocation replay failed or used different inputs: ' + str(proof.get('failure')))
            report['proof'] = {'sha256': digest(output / 'proof-report.json'), 'roots': len(claims),
                               'freshKernelReplay': True, 'replayIncludesImports': True}
        if (report['inputs'] != python_inputs.inputs() or report['leanInputs'] != harness.lean_check.source_inputs()
                or frozen != source_gate.inputs() or profiles != source_gate.profiles(library)
                or std != source_gate.std_inputs(library)):
            raise ValueError('invocation gate inputs changed during the run')
        report['frozenNativeInputs'] = len(frozen)
        report['zigLibrary'] = {'path': str(library), 'inputs': len(std), 'sha256': digest(output / 'std-inputs.json')}
        if constructors:
            report['allConstructorEntryPreservationVerified'] = True
            report['observedConstructorEntryPreservationVerified'] = not args.preflight
            report['nativeConstructorSuffixWordsVerified'] = not args.preflight
            report['jointItemPreservationVerified'] = not args.preflight
            report['jointConstructorPreservationVerified'] = not args.preflight
            report['finiteJointConstructorPreservationVerified'] = not args.preflight
            report['entryReplayModelConstructed'] = not args.preflight
            report['enclosingParentFramesDerived'] = not args.preflight
            report['earlyInsertionFailureFramesDerived'] = not args.preflight
            report['successfulInsertionFramesDerived'] = not args.preflight
            report['publicationRollbackFramesDerived'] = not args.preflight
            report['bothPreparationFramesDerived'] = not args.preflight
            report['bothBackingFramesDerived'] = not args.preflight
            report['transferredGrowthFramesDerived'] = not args.preflight
            report['transferredFirstAndSpareFramesDerived'] = not args.preflight
            report['sourceProvenanceCarried'] = not args.preflight
            report['allEntryNativeFrameInductionVerified'] = not args.preflight
        report['observedChildFramePreservationVerified'] = not args.preflight
        report['observedChildWordPreservationVerified'] = not args.preflight
        report['observedAllEntryPreservationVerified'] = not args.preflight
        report['nativeSuffixWordPreservationVerified'] = not args.preflight
        report['nativeCandidateWordBindingVerified'] = not args.preflight
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
    parser.add_argument('--constructors', action='store_true', help='also check all five native constructor entry wrappers')
    parser.add_argument('--control-jobs', type=int, choices=range(1, 5), default=4,
                        help='control processes (default: 4 with one Lean thread each; 1 retains the serial four-thread baseline)')
    check(parser.parse_args())
