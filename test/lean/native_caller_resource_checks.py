"""Audit resource-conditioned replay of the actual native caller body and close.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
import guarded_induction_checks as guarded
from native_miss_frame_checks import named
from native_algebraic_dispatch_checks import source
from native_resource_admission_checks import telescope, local_call
from native_resource_miss_checks import expanded, child_contract, appended
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check

NATIVE = gate.OWNED + 'Caller.ProtocolTrace.Native.'
CALLER = gate.OWNED + 'Caller.ProtocolTrace.'
MISS = gate.OWNED + 'MissStream.'
RESOURCE = gate.OWNED + 'Recursive.Resource.'
CHILD = gate.NS + 'ChildTrace.'
ALLOCATION = gate.NS + 'AllocationTrace.'
CLAIMS = [NATIVE + n for n in ('miss_from_projection', 'miss_resource_verified', 'miss_resource_traced')]
CLAIMS += [ALLOCATION + 'caller_from_bodies', CALLER + 'HistoryTests.spare_traced']
INTERFACES = (NATIVE + 'MissProjected',)


def audit(claims):
    required = {
        NATIVE + 'miss_from_projection': {NATIVE + 'miss_recorded', NATIVE + 'miss_cleanup_segment', CALLER + 'finish_projected'},
        NATIVE + 'miss_verified': {NATIVE + 'miss_from_projection', MISS + 'selected_preserved', MISS + 'scoped_from_children'},
        NATIVE + 'miss_resource_verified': {NATIVE + 'miss_from_projection', MISS + 'selected_resource_preserved', MISS + 'scoped_from_resources'},
        NATIVE + 'miss_resource_traced': {NATIVE + 'miss_resource_verified', NATIVE + 'history_boundaries', RESOURCE + 'Admitted.captured'},
        ALLOCATION + 'caller_from_bodies': {NATIVE + 'miss_resource_traced', ALLOCATION + 'step_source_projects', ALLOCATION + 'frame_input'},
        CALLER + 'HistoryTests.spare_traced': {NATIVE + 'miss_resource_traced',
            gate.OWNED + 'Insertion.Native.NativeSpareTests.reached_frame'},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('caller resource replay lost shared reasoning: ' + name + ': ' + ', '.join(sorted(missing)))
    for name in CLAIMS[:-1]:
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('caller resource replay depends on a fixture: ' + name)
    return {'checkedDependencies': sorted(required), 'sameNativeBodyAndCloseForBothRelations': True,
            'markedChildContractsReachRecordedCaller': True, 'admissionAndCursorBoundariesDerived': True,
            'completeConstructorBodyReplayVerified': False, 'allEntryResourceInductionVerified': False,
            'recursiveWordPreservationVerified': False, 'composedProductionTheoremVerified': False}


def audit_statements(rows, interfaces):
    from native_constructor_checks import expression
    statements = {row['theorem']: row['statement'] for row in rows}
    definitions = {row['name']: row for row in interfaces}
    value = definitions[NATIVE + 'MissProjected']['value']
    fields, lets, root, context = telescope(value)
    # This endpoint is the actual recorded body and deferred close, with one
    # ordinary-outcome guard; it must not collapse to a child-only simulation.
    term, scope = list(fields.values())[-1]
    equation = joint.app(value, term, 'Eq')
    named(value, equation[-1:], scope, ('Bool.true',))
    completed = joint.app(value, equation[-2], gate.OWNED + 'ordinary')
    joint.path(value, completed[-1], scope, ('Prod.fst',), 'body')
    body = joint.app(value, lets['body'][0], CALLER + 'missBody')
    named(value, body[-6:], lets['body'][1], ('source', 'buffer', 'request', 'key', 'deterministic', 'initialRecord'))
    actual = joint.app(value, lets['actual'][0], CALLER + 'finish')
    for term, member in zip(actual[-2:], ('Prod.fst', 'Prod.snd')):
        joint.path(value, term, lets['actual'][1], (member,), 'body')
    logical = joint.app(value, lets['logical'][0], 'Compiler.Extraction.Interner.FindCode.controlMiss')
    named(value, logical[-6:-5], lets['logical'][1], ('Compiler.Extraction.Interner.findCode',))
    execution = joint.app(value, logical[-5], 'Compiler.Extraction.Interner.Scoped.execution')
    named(value, execution[-2:], lets['logical'][1], ('resources', 'logicalModel'))
    named(value, logical[-4:-1], lets['logical'][1], ('request', 'key', 'deterministic'))
    claims = []
    for _ in range(3):
        first, root = joint.app(value, root, 'And')
        claims.append(first)
    claims.append(root)
    for index, world in enumerate(('body', 'actual')):
        equation = joint.app(value, claims[index], 'Eq')
        left, right = [joint.app(value, term, 'Prod.mk') for term in equation[-2:]]
        joint.path(value, left[-2], context, ('Prod.fst',), world)
        joint.path(value, left[-1], context, (CALLER + 'scopeView', 'Prod.snd'), world)
        mapped = joint.app(value, right[-2], 'Except.mapError')
        joint.path(value, mapped[-1], context, ('Prod.fst',), 'logical')
        reached = right[-1]
        if index:
            closed = joint.app(value, reached, 'Compiler.Extraction.Interner.Scoped.close')
            named(value, closed[-2:-1], context, ('resources',))
            reached = closed[-1]
        joint.path(value, reached, context, ('Prod.snd',), 'logical')
    equation = joint.app(value, claims[2], 'Eq')
    joint.path(value, equation[-2], context, (CALLER + 'Recorded.events', 'Prod.snd'), 'actual')
    parts = appended(value, equation[-1])
    named(value, parts[:2], context, ('leading', 'middle'))
    if len(parts) != 4:
        raise ValueError('recorded caller lost complete body/cleanup history')
    for term, member in zip(parts[2:], ('body', 'cleanup')):
        joint.path(value, term, context, (MISS + 'Segment.' + member,), 'observed')
    equation = joint.app(value, claims[3], 'Eq')
    named(value, equation[-1:], context, ('Bool.false',))
    joint.path(value, equation[-2], context,
               (CALLER + 'Tokens.incomplete', CALLER + 'Recorded.tokens', 'Prod.snd'), 'actual')
    guard = guarded.source_guard(interfaces)
    for current, reference in (('miss_resource_verified', 'miss_verified'), ('miss_resource_traced', 'miss_traced_verified')):
        value, prior = statements[NATIVE + current], statements[NATIVE + reference]
        fields, lets, root, context = telescope(value)
        old, old_lets, old_root, old_context = telescope(prior)
        if expanded(value, root, context, lets) != expanded(prior, old_root, old_context, old_lets):
            raise ValueError('resource caller changed the complete recorded result: ' + current)
        for name in ('initial', 'frame', 'aligned', 'detached', 'unowned', 'caller'):
            if expression(value, *fields[name]) != expression(prior, *old[name]):
                raise ValueError('resource caller changed native input admission: ' + name)
        if current == 'miss_resource_verified':
            if set(fields) != set(old) | {'ε', 'history', 'stream', 'admitted'}:
                raise ValueError('resource caller gained an outcome premise')
            child_contract(value, fields['coupled'], guard)
            term, scope = fields['admitted']
            admitted = joint.app(value, term, RESOURCE + 'Admitted')
            named(value, admitted[-4:-2], scope, ('history', 'stream'))
            named(value, admitted[-1:], scope, ('before',))
            selected = joint.app(value, admitted[-2], MISS + 'selected')
            named(value, selected[-4:], scope, ('request', 'key', 'slice', 'deterministic'))
            native = joint.app(value, selected[-5], NATIVE + 'physical')
            named(value, native[-13:], scope, ('ops', 'allocate', 'safety', 'owner', 'meaning', 'base', 'growth',
                                               'usizeBits', 'children', 'debug', 'source', 'address', 'input'))
        else:
            extra = set(fields) - set(old)
            if len(extra) != 1 or set(fields) != set(old) - {'coupled'} | extra:
                raise ValueError('captured caller assumes admission, outcome or a boundary')
            term, scope = guarded.guarded_body(value, *fields[next(iter(extra))], guard)
            child_fields, _, conclusion, local = telescope(value, term, scope)
            if list(child_fields) != ['rows']:
                raise ValueError('captured caller lost its reached row quantifier')
            proper = joint.app(value, conclusion, 'Compiler.Extraction.Dispatch.Effects.SourceConstructorsAt')
            effect = joint.app(value, proper[-5], RESOURCE + 'projection')
            joint.app(value, effect[-4], CHILD + 'history')
            named(value, effect[-3:-2], local, ('stream',))
            named(value, proper[-3:], local, ('debug', 'child', 'model'))
            cursor = joint.app(value, joint.app(value, effect[-2], gate.OWNED + 'Recursive.cursorGraph')[-1], MISS + 'childCursor')
            named(value, cursor[-1:], local, ('before',))
            named(value, joint.app(value, cursor[-2], 'List.length')[-1:], local, ('leading',))
            parts = appended(value, lets['stream'][0])
            if len(parts) != 4:
                raise ValueError('captured caller lost its complete raw stream')
            scope = lets['stream'][1]
            after = joint.app(value, joint.app(value, parts[0], CHILD + 'history')[-1], 'Prod.snd')
            named(value, local_call(value, after[-1], scope, 'action'), scope, ('before',))
            for term, member in zip(parts[1:3], ('body', 'cleanup')):
                joint.path(value, term, scope, (MISS + 'Segment.' + member,), 'observed')
            named(value, parts[-1:], scope, ('trailing',))

    value, old = statements[ALLOCATION + 'caller_from_bodies'], statements[ALLOCATION + 'scoped_from_bodies']
    fields, lets, root, context = telescope(value)
    prior, old_lets, _, _ = telescope(old)
    if set(fields) != set(prior) | {'buffer'}:
        raise ValueError('marked caller changed the existing proper-child body premises')
    for name in fields.keys() - {'buffer'}:
        if expression(value, *fields[name]) != expression(old, *prior[name]):
            raise ValueError('marked caller changed an entry/body premise: ' + name)
    for name in ('traced', 'action', 'observed', 'stream', 'model'):
        if expression(value, *lets[name]) != expression(old, *old_lets[name]):
            raise ValueError('marked caller changed the captured source family or model: ' + name)
    result = joint.app(value, root, NATIVE + 'MissProjected')
    named(value, result[-17:], context, ('debug', 'source', 'buffer', 'address', 'input', 'request', 'key', 'slice',
                                         'deterministic', 'before', 'handle', 'lookup', 'model', 'seed', 'leading', 'trailing', 'mismatch'))
    return {'sameCompleteCallerResultAndCleanup': True, 'actualAdmissionAndCapturedSuffixBound': True,
            'sameMarkedBodyHypothesisAndModel': True, 'completeConstructorBodyReplayVerified': False,
            'allEntryResourceInductionVerified': False, 'composedProductionTheoremVerified': False}


def controls(output, env, lean):
    groups = (
        ('body', 'InternerCallerProtocolMissReplay', (
            ('wrong-return', '= (result, projected) ∧', '= (.error (.language .outOfMemory), projected) ∧'),
            ('lost-close-history', 'actual.2.events = leading ++ captured.2.events.map Event.normalization', 'actual.2.events = leading'),
            ('lost-cleanup', 'actual.2.events = leading ++ middle ++ observed.body ++ observed.cleanup',
             'actual.2.events = leading ++ middle ++ observed.body'),
        )),
        ('resource', 'InternerCallerResourceReplay', (
            ('wrong-guard', '(deterministic && (request.item.kind == 1)) = true →', '(!deterministic && (request.item.kind == 1)) = true →'),
            ('rewind-stream', 'let stream := ChildTrace.history (action before).2 ++', 'let stream := ChildTrace.history before ++'),
            ('discarded-admission', 'initial frame aligned coupled admitted', 'initial frame aligned coupled (by exact Resource.Admitted.captured history _ before [])'),
        )),
        ('marked', 'InternerAllocationCallerReplay', (
            ('lose-body-stream', 'let stream := ChildTrace.history (action before).2 ++ observed.body ++',
             'let stream := ChildTrace.history (action before).2 ++'),
            ('lose-cleanup-stream', '++ observed.cleanup ++ trailing', '++ trailing'),
            ('wrong-replay-prefix', 'let model := replay leading stream before models', 'let model := replay [] stream before models'),
        )),
    )
    records = []
    for group, module, changes in groups:
        code = source('Compiler.Extraction.' + module)
        records += checked_controls(output, [mutation_check(output, 'caller-resource-' + group + '-unchanged', code, True, env, lean)])
        for name, old, new in changes:
            count = 2 if name == 'wrong-guard' else 1
            if code.count(old) != count:
                raise ValueError('ambiguous caller resource mutation: ' + name)
            records += checked_controls(output, [mutation_check(output, 'caller-resource-' + group + '-' + name,
                code.replace(old, new), False, env, lean)])
    return records
