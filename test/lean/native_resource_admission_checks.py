"""Audit resource-conditional composition through the complete native dispatcher.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
import constructor_replay_choice_checks as choice
from native_miss_frame_checks import named
from native_algebraic_dispatch_checks import source
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check

NS, OWNED, ITEM = gate.NS, gate.OWNED, gate.ITEM
RESOURCE = OWNED + 'Recursive.Resource.'
RECURSIVE = OWNED + 'Recursive.'
TESTS = ITEM + 'NativeResourceAdmissionTests.'
PRIOR = ITEM + 'NativeAllocationAdmissionTests.'
IDENTITY = ITEM + 'NativeAllocationIdentityTests.'
TRACE = NS + 'ProtocolTrace.'
CORE = ('Admitted.captured', 'Admitted.entry', 'Grows.bind', 'Admitted.first', 'Admitted.next',
        'Projects.of_projects', 'Projects.bind', 'Projects.safe')
NATIVE = ('operand_world', 'operand_grows', 'resource_read_bind', 'InputFrame.resource_queries',
          'InputFrame.resource_root', 'dispatch_resource_projected', 'dispatcher_resource_projected',
          'dispatcher_captured_projected')
REGRESSIONS = ('capture_native', 'recorded_grows', 'recorded_history', 'recorded_result', 'recorded_admitted',
               'actual_item_decision', 'wrong_stream_rejected', 'same_graph_both_outcomes')
CLAIMS = [RESOURCE + n for n in CORE] + [NS + n for n in NATIVE] + [TESTS + n for n in REGRESSIONS]
IDENTITY_REGRESSIONS = ('extra_prepared', 'before_frame', 'initial_graph', 'histories_equal', 'native_result',
                        'native_address', 'recorded_history', 'both_admitted', 'recorded_result', 'no_cursor_model')
CLAIMS += [IDENTITY + n for n in IDENTITY_REGRESSIONS]
INTERFACES = tuple(RESOURCE + n for n in ('Grows', 'Admitted', 'Projects.mk', 'projection'))
INTERFACES += (RECURSIVE + 'ProjectsAt',)
INTERFACES += tuple(TESTS + n for n in ('capture', 'recorded', 'before', 'events', 'itemDecision'))
INTERFACES += tuple(IDENTITY + n for n in ('prior', 'child', 'capture', 'recorded', 'extra', 'native',
                                         'before', 'frame', 'events', 'lastAddress'))


def audit(claims):
    required = {
        RESOURCE + 'Admitted.entry': {RESOURCE + 'Grows', RESOURCE + 'Admitted', 'List.IsPrefix.trans'},
        RESOURCE + 'Projects.bind': {RESOURCE + 'Grows.bind', RESOURCE + 'Admitted.first', RESOURCE + 'Admitted.next'},
        RESOURCE + 'Projects.safe': {RECURSIVE + 'safe_at'},
        NS + 'operand_keeps': {NS + 'operand_world'},
        NS + 'operand_grows': {NS + 'operand_world'},
        NS + 'InputFrame.resource_queries': {NS + 'InputFrame.queries_at', NS + 'operand_grows', RESOURCE + 'Projects.of_projects'},
        NS + 'InputFrame.resource_root': {NS + 'InputFrame.root_at', NS + 'operand_grows', RESOURCE + 'Projects.of_projects'},
        NS + 'dispatch_resource_projected': {'Compiler.Extraction.Dispatch.Effects.simplify_with_inputs_at',
            NS + 'resource_read_bind', NS + 'InputFrame.resource_queries', NS + 'InputFrame.resource_root', RESOURCE + 'Projects.bind'},
        NS + 'dispatcher_resource_projected': {NS + 'dispatch_resource_projected', NS + 'dispatcher_snapshot', OWNED + 'NativeGraph.Facts.reads'},
        NS + 'dispatcher_captured_projected': {NS + 'dispatcher_resource_projected', RESOURCE + 'Admitted.captured'},
        TESTS + 'capture_native': {TRACE + 'unfold_erases'},
        TESTS + 'recorded_result': {PRIOR + 'successful', PRIOR + 'refused'},
        TESTS + 'recorded_admitted': {RESOURCE + 'Admitted.captured', TESTS + 'recorded_history'},
        TESTS + 'wrong_stream_rejected': {TESTS + 'actual_item_decision', TESTS + 'recorded_history'},
        TESTS + 'same_graph_both_outcomes': {PRIOR + 'same_graph', TESTS + 'recorded_result'},
        IDENTITY + 'before_frame': {NS + 'CallFrame.arguments', ITEM + 'Arguments.prepare_success', PRIOR + 'admitted_frame'},
        IDENTITY + 'histories_equal': {TESTS + 'capture'},
        IDENTITY + 'recorded_history': {IDENTITY + 'histories_equal'},
        IDENTITY + 'both_admitted': {IDENTITY + 'recorded_history'},
        IDENTITY + 'no_cursor_model': {IDENTITY + n for n in ('before_frame', 'initial_graph', 'both_admitted',
                                                            'recorded_result', 'native_address')},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('resource admission lost composition: ' + name + ': ' + ', '.join(sorted(missing)))
    for name in [RESOURCE + n for n in CORE] + [NS + n for n in NATIVE]:
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('resource composition depends on a fixture: ' + name)
    return {'checkedDependencies': sorted(required), 'resourceAdmissionComposesThroughBind': True,
            'completeNativeDispatcherConsumesResourceContracts': True, 'sameNativeReadsReused': True,
            'capturedDispatcherAdmissionDerived': True, 'nativeSuccessAndOomStreamsDistinguished': True,
            'protocolStreamInsufficientForNativeIdentity': True,
            'allEntryResourceInductionVerified': False, 'completeStreamCorrespondenceVerified': False,
            'recursiveInductionVerified': False}


def telescope(value, root=None, context=()):
    root = value['root'] if root is None else root
    context, fields, lets, counts = list(context), {}, {}, {}
    while value['nodes'][root][0] in ('forall', 'lambda', 'let'):
        node = value['nodes'][root]
        count = counts.get(node[1], 0)
        name = node[1] if count == 0 else node[1] + '#' + str(count)
        counts[node[1]] = count + 1
        if node[0] == 'let':
            lets[name] = (node[3], context[:])
        else:
            fields[name] = (node[3], context[:])
        context.append(name)
        root = node[4]
    return fields, lets, root, context


def local_call(value, term, context, function):
    args = []
    while value['nodes'][term][0] == 'app':
        node = value['nodes'][term]
        args.append(node[2])
        term = node[1]
    if gate.named(value, term, context) != function:
        raise ValueError('resource admission rebound a function: ' + function)
    return list(reversed(args))


def final_history(value, term, context):
    args = local_call(value, term, context, 'history')
    if len(args) != 1:
        raise ValueError('resource admission changed history arity')
    state = joint.app(value, args[0], 'Prod.snd')
    named(value, local_call(value, state[-1], context, 'physical'), context, ('before',))


def audit_identity(statements, definitions):
    """Keep the obstruction bound to native execution and its actual frame."""
    for alias, target in (('prior', PRIOR + 'before'), ('child', PRIOR + 'child'),
                          ('capture', TESTS + 'capture'), ('recorded', TESTS + 'recorded')):
        value = definitions[IDENTITY + alias]['value']
        if joint.app(value, value['root'], target):
            raise ValueError('native identity regression changed its actual execution: ' + alias)
    for name in IDENTITY_REGRESSIONS:
        fields, _, _, _ = telescope(statements[IDENTITY + name])
        expected = {'safety', 'position'} if name == 'no_cursor_model' else (
            {'safety'} if name == 'extra_prepared' else {'safety', 'shifted'})
        if set(fields) != expected:
            raise ValueError('native identity regression gained an outcome premise: ' + name)

    value = definitions[IDENTITY + 'extra']['value']
    _, _, root, context = telescope(value)
    after = joint.app(value, root, 'Prod.snd')
    prepared = joint.app(value, after[-1], ITEM + 'Arguments.prepare')
    prior = joint.app(value, prepared[-1], IDENTITY + 'prior')
    named(value, prior[-2:], context, ('safety', 'Bool.true'))
    literal = joint.app(value, prepared[-2], 'List.cons')
    joint.app(value, literal[-1], 'List.nil')

    value = definitions[IDENTITY + 'frame']['value']
    _, _, root, context = telescope(value)
    frame = joint.app(value, root, PRIOR + 'frame')
    named(value, frame[-2:-1], context, ('safety',))
    erased = joint.app(value, frame[-1], NS + 'ChildTrace.erase')
    named(value, erased[-1:], context, ('world',))

    value = definitions[IDENTITY + 'before']['value']
    _, _, root, context = telescope(value)
    restored = joint.app(value, root, NS + 'ChildTrace.restore')
    joint.app(value, restored[-2], 'List.nil')
    native = joint.app(value, restored[-1], IDENTITY + 'native')
    named(value, native[-2:], context, ('safety', 'shifted'))

    value = statements[IDENTITY + 'no_cursor_model']
    _, _, root, context = telescope(value)
    absent = joint.app(value, root, 'Not')
    exists = joint.app(value, absent[-1], 'Exists')
    body = value['nodes'][exists[-1]]
    if body[0] != 'lambda':
        raise ValueError('native identity obstruction lost its model quantifier')
    context += [body[1]]
    projected = joint.app(value, body[4], RESOURCE + 'Projects')
    joint.app(value, projected[-6], NS + 'ChildTrace.history')
    for term, name in ((projected[-5], 'events'), (projected[-3], 'frame'), (projected[-2], 'recorded')):
        named(value, joint.app(value, term, IDENTITY + name)[-1:], context, ('safety',))
    named(value, projected[-1:], context, (body[1],))
    observed = joint.app(value, projected[-4], RECURSIVE + 'cursorGraph')
    cursor = joint.app(value, observed[-1], OWNED + 'MissStream.childCursor')
    named(value, cursor[-2:-1], context, ('position',))
    before = joint.app(value, cursor[-1], IDENTITY + 'before')
    named(value, before[-2:], context, ('safety', 'Bool.false'))


def audit_statements(rows, interfaces):
    from native_constructor_checks import expression
    statements = {r['theorem']: r['statement'] for r in rows}
    definitions = {r['name']: r for r in interfaces}
    for name in ('Grows', 'Admitted'):
        value = definitions[RESOURCE + name]['value']
        fields, _, root, context = telescope(value)
        expected = {'Native', 'Event', 'α', 'history', 'physical', 'before'} | ({'stream'} if name == 'Admitted' else set())
        if set(fields) != expected:
            raise ValueError('resource admission added outcome premises: ' + name)
        prefix = joint.app(value, root, 'List.IsPrefix')
        if name == 'Admitted':
            final_history(value, prefix[-2], context)
            named(value, prefix[-1:], context, ('stream',))
        else:
            named(value, local_call(value, prefix[-2], context, 'history'), context, ('before',))
            final_history(value, prefix[-1], context)

    value = definitions[RESOURCE + 'Projects.mk']['type']
    fields, _, _, _ = telescope(value)
    grow = joint.app(value, fields['grows'][0], RESOURCE + 'Grows')
    named(value, grow[-2:], fields['grows'][1], ('history', 'physical'))
    run, _, root, context = telescope(value, *fields['run'])
    original = definitions[RECURSIVE + 'ProjectsAt']['value']
    old, _, old_root, old_context = telescope(original)
    if len(run) != 4:
        raise ValueError('resource projection gained an unreviewed hypothesis')
    current, previous = list(run.values()), list(old.values())[-3:]
    for new, prior in zip((current[0], current[1], current[3]), previous):
        if expression(value, *new) != expression(original, *prior):
            raise ValueError('resource projection weakened the original native or ordinary inputs')
    admitted = joint.app(value, current[2][0], RESOURCE + 'Admitted')
    named(value, admitted[-4:], current[2][1], ('history', 'stream', 'physical', 'before'))
    if expression(value, root, context) != expression(original, old_root, old_context):
        raise ValueError('resource projection weakened frame, result or reached observation')

    value = statements[NS + 'dispatcher_resource_projected']
    fields, lets, root, context = telescope(value)
    common = {'σ', 'Event', 'history', 'safety', 'owner', 'usizeBits', 'base', 'children', 'model', 'debug', 'source',
              'values', 'address', 'native', 'key', 'normalized', 'rows', 'before', 'data', 'capacity', 'facts',
              'aligned', 'predicate', 'initial', 'input'}
    wanted = common | {'stream', 'observe', 'proper'}
    extra = list(fields.keys() - wanted)
    if len(extra) != 2 or set(fields) != wanted | set(extra):
        raise ValueError('native dispatcher resource statement changed its boundary')
    guards = {}
    for name in extra:
        term, scope = fields[name]
        head, args = gate.applied(value, term)
        if head[:2] == ['const', RESOURCE + 'Admitted']:
            named(value, args[-4:], scope, ('history', 'stream', 'action', 'before'))
            guards['admitted'] = fields[name]
        elif head[:2] == ['const', 'Eq']:
            completed = joint.app(value, args[-2], OWNED + 'ordinary')
            result = joint.app(value, completed[-1], 'Prod.fst')
            named(value, local_call(value, result[-1], scope, 'action'), scope, ('before',))
            named(value, args[-1:], scope, ('Bool.true',))
            guards['completed'] = fields[name]
        else:
            raise ValueError('native dispatcher gained a different completion guard')
    if set(guards) != {'admitted', 'completed'}:
        raise ValueError('native dispatcher lost admission or ordinary completion')
    proper, scope = choice.one_call(value, *fields['proper'], 'Compiler.Extraction.Dispatch.Effects.SourceConstructorsAt')
    effect = joint.app(value, proper[-5], RESOURCE + 'projection')
    named(value, effect[-4:], scope, ('history', 'stream', 'observe', 'predicate'))
    named(value, proper[-3:], scope, ('debug', 'children', 'model'))
    reads = joint.app(value, proper[-4], 'Compiler.Extraction.Nested.storageReads')
    named(value, reads[-1:], scope, ('rows',))
    action = lets['action']
    call, scope = choice.one_call(value, *action, NS + 'context')
    named(value, call[-5:], scope, ('base', 'owner', 'usizeBits', 'children', 'debug'))

    captured = statements[NS + 'dispatcher_captured_projected']
    cap_fields, cap_lets, cap_root, cap_context = telescope(captured)
    wanted = common | {'trailing'}
    extra = cap_fields.keys() - wanted
    if len(extra) != 2:
        raise ValueError('captured dispatcher regained an admission or outcome premise')
    expected = [expression(value, *fields['proper']), expression(value, *guards['completed'])]
    actual = [expression(captured, *cap_fields[name]) for name in extra]
    if not all(actual.count(term) == 1 for term in expected):
        raise ValueError('captured dispatcher changed the child contract or ordinary guard')
    for field in common:
        if expression(value, *fields[field]) != expression(captured, *cap_fields[field]):
            raise ValueError('captured dispatcher changed a native input: ' + field)
    for let in ('action', 'logical'):
        if expression(value, *lets[let]) != expression(captured, *cap_lets[let]):
            raise ValueError('captured dispatcher changed the actual execution: ' + let)
    if expression(value, root, context) != expression(captured, cap_root, cap_context):
        raise ValueError('captured dispatcher changed frame or result conclusions')
    combined, scope = choice.one_call(captured, *cap_lets['stream'], 'HAppend.hAppend')
    named(captured, combined[-1:], scope, ('trailing',))
    history = local_call(captured, combined[-2], scope, 'history')
    after = joint.app(captured, history[0], 'Prod.snd')
    named(captured, local_call(captured, after[-1], scope, 'action'), scope, ('before',))
    observed = joint.app(captured, cap_lets['observe'][0], RECURSIVE + 'cursorGraph')
    cursor = captured['nodes'][observed[-1]]
    if cursor[0] != 'lambda':
        raise ValueError('captured resource cursor is not computed from actual history')
    scope = cap_lets['observe'][1] + [cursor[1]]
    length = joint.app(captured, cursor[4], 'List.length')
    named(captured, local_call(captured, length[-1], scope, 'history'), scope, (cursor[1],))
    for name in REGRESSIONS:
        fields, _, _, _ = telescope(statements[TESTS + name])
        expected = {'safety'}
        if name in ('recorded_history', 'recorded_result', 'recorded_admitted', 'actual_item_decision', 'wrong_stream_rejected'):
            expected.add('permitted')
        if name == 'capture_native':
            expected.add('before')
        if name == 'recorded_admitted':
            expected.add('trailing')
        if set(fields) != expected:
            raise ValueError('native resource regression assumes its outcome: ' + name)
    audit_identity(statements, definitions)
    return {'resourceAdmissionUsesActualFinalHistoryOnly': True, 'sameExactNativeProjectionConclusion': True,
            'resourceChildContractsUseOneFixedStream': True, 'capturedAdmissionNotAssumed': True,
            'cursorCountsSameCapturedHistory': True, 'nativeRegressionsHaveNoOutcomePremises': True,
            'nativeIdentityCounterexampleHasNoOutcomePremises': True,
            'allEntryResourceInductionVerified': False, 'completeStreamCorrespondenceVerified': False}


def controls(output, env, lean):
    groups = (
        ('core', 'Compiler.Extraction.InternerResourceProjection', (
            ('rewind-admission', '  history (physical before).2 <+: stream', '  history before <+: stream', 1),
            ('reverse-admission', '  history (physical before).2 <+: stream', '  stream <+: history (physical before).2', 1),
            ('missing-tail-growth', '(following : ∀ value, Grows history (next value))', '(following : True)', 2),
            ('missing-admission', 'predicate before → Admitted history stream physical before →', 'predicate before → True →', 1),
            ('different-child-stream', '(following : ∀ value, Projects history stream observe predicate (next value) (nextModel value))',
             '(following : ∀ value, Projects history [] observe predicate (next value) (nextModel value))', 1),
        )),
        ('dispatch', 'Compiler.Extraction.InternerNativeResourceDispatch', (
            ('missing-initial-frame', '(initial : predicate before)', '(initial : True)', 2),
            ('missing-key-binding', '(aligned : key.arguments = normalized.items)', '(aligned : True)', 3),
            ('wrong-query-owner', 'NativeGraph.Facts safety base.allocator owner data capacity before rows',
             'NativeGraph.Facts safety base.allocator (owner + 1) data capacity before rows', 2),
            ('wrong-child-rows', '(Nested.storageReads rows) debug children model', '(Nested.storageReads []) debug children model', 3),
            ('wrong-captured-stream', 'let stream := history (action before).2 ++ trailing',
             'let stream := trailing ++ history (action before).2', 1),
        )),
        ('native', 'Compiler.Extraction.InternerNativeResourceAdmissionTests', (
            ('flip-allocation-decision', '=> some accepted', '=> some (!accepted)', 1),
            ('admit-wrong-stream', '(events safety (!permitted)) (recorded safety)', '(events safety permitted) (recorded safety)', 1),
            ('replace-native-oom', 'if permitted then .ok 5 else .error (.language .outOfMemory)',
             'if permitted then .ok 5 else .error (.language .unsupported)', 1),
        )),
        ('identity', 'Compiler.Extraction.InternerNativeAllocationIdentityTests', (
            ('omit-extra-allocation', 'def extra (safety : Bool) := (Arguments.prepare [0]',
             'def extra (safety : Bool) := (Arguments.prepare []', 1),
            ('erase-history', '(capture safety (native safety shifted) []).2.events = events safety',
             '(capture safety (native safety shifted) []).2.events = []', 1),
            ('equate-addresses', 'some (if shifted then 31 else 30)', 'some 30', 1),
        )),
    )
    records = []
    for group, module, changes in groups:
        code = source(module)
        records += checked_controls(output, [mutation_check(output, 'resource-' + group + '-unchanged', code, True, env, lean)])
        for name, old, new, count in changes:
            if code.count(old) != count:
                raise ValueError('ambiguous resource mutation: ' + group + '-' + name + ': ' + str(code.count(old)))
            records += checked_controls(output, [mutation_check(output, 'resource-' + group + '-' + name,
                code.replace(old, new), False, env, lean)])
    return records
