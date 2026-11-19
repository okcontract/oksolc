"""Audit resource-conditional child composition through the complete scoped miss.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
import constructor_replay_choice_checks as choice
import guarded_induction_checks as guarded
from native_resource_admission_checks import telescope, local_call
from native_miss_frame_checks import named, replace_names
from native_algebraic_dispatch_checks import source
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check

MISS = gate.OWNED + 'MissStream.'
RESOURCE = gate.OWNED + 'Recursive.Resource.'
TRACE = gate.NS + 'ProtocolTrace.'
CHILD = gate.NS + 'ChildTrace.'
CAPTURED = TRACE + 'scoped_resource_miss'
CLAIMS = [MISS + n for n in ('from_frame', 'selected_resource_preserved', 'scoped_from_resources')] + [CAPTURED]
INTERFACES = (MISS + 'Completion', MISS + 'Projected', TRACE + 'children')


def audit(claims):
    required = {
        MISS + 'from_frame': {MISS + n for n in ('tail_inputs', 'inserted', 'published', 'failed')},
        MISS + 'from_children': {MISS + 'from_frame', MISS + 'selected_preserved'},
        MISS + 'selected_resource_preserved': {gate.NS + 'dispatcher_resource_projected'},
        MISS + 'scoped_from_resources': {MISS + n for n in ('from_frame', 'selected_resource_preserved', 'projected')},
        CAPTURED: {MISS + 'child_boundaries', MISS + 'scoped_from_resources', RESOURCE + 'Admitted.captured'},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('resource miss lost shared composition: ' + name + ': ' + ', '.join(sorted(missing)))
    for name in CLAIMS:
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('resource miss depends on a fixture: ' + name)
    return {'checkedDependencies': sorted(required), 'sameSuffixProofUsedByBothRelations': True,
            'resourceContractsReachCompleteScopedMiss': True, 'capturedAdmissionAndCursorDerived': True,
            'allEntryResourceInductionVerified': False, 'completeStreamCorrespondenceVerified': False,
            'recursiveInductionVerified': False}


def expanded(value, root, context, lets):
    """Compare conclusions after expanding their local action aliases only."""
    from native_constructor_checks import expression
    bindings = {}
    for name, (term, scope) in lets.items():
        bindings[name] = replace_names(expression(value, term, scope), bindings)
    return replace_names(expression(value, root, context), bindings)


def appended(value, root):
    head, args = gate.applied(value, root)
    if head[:2] == ['const', 'HAppend.hAppend']:
        return appended(value, args[-2]) + appended(value, args[-1])
    return [root]


def action(value, term, context, outer=False, applied=False):
    selected = joint.app(value, term, MISS + 'selected')
    if applied:
        named(value, selected[-1:], context, ('before',))
        selected = selected[:-1]
    named(value, selected[-4:], context, ('request', 'key', 'slice', 'deterministic'))
    physical = joint.app(value, selected[-5], MISS + 'physical')
    expected = ('outerOps', 'outerAllocate', 'safety', 'owner', 'meaning', 'outerBase', 'outerGrowth',
                'owner', 'usizeBits', 'traced', 'debug', 'source', 'address', 'input') if outer else (
                'ops', 'allocate', 'safety', 'owner', 'meaning', 'base', 'growth',
                'owner', 'usizeBits', 'children', 'debug', 'source', 'address', 'input')
    named(value, physical[-len(expected):], context, expected)


def child_contract(value, field, guard, outer=False):
    term, context = guarded.guarded_body(value, *field, guard)
    node = value['nodes'][term]
    if node[0] != 'forall' or node[1] != 'rows':
        raise ValueError('resource miss lost its reached row quantifier')
    context = context + ['rows']
    proper = joint.app(value, node[4], 'Compiler.Extraction.Dispatch.Effects.SourceConstructorsAt')
    effect = joint.app(value, proper[-5], RESOURCE + 'projection')
    if outer:
        joint.app(value, effect[-4], CHILD + 'history')
        named(value, effect[-3:-2], context, ('stream',))
    else:
        named(value, effect[-4:-2], context, ('history', 'stream'))
    observed = joint.app(value, effect[-2], gate.OWNED + 'Recursive.cursorGraph')
    named(value, observed[-1:], context, ('cursor',))
    frame, scope = choice.one_call(value, effect[-1], context, gate.NS + 'InputFrame')
    named(value, frame[-6:], scope, ('owner', 'rows', 'source', 'values', 'slice', scope[-1]))
    joint.path(value, frame[-7], scope, (gate.ITEM + 'ShiftInput.Context.allocator',), 'outerBase' if outer else 'base')
    reads = joint.app(value, proper[-4], 'Compiler.Extraction.Nested.storageReads')
    named(value, reads[-1:], context, ('rows',))
    named(value, proper[-3:], context, ('debug', 'traced' if outer else 'children', 'model'))


def audit_statements(rows, interfaces):
    from native_constructor_checks import expression
    statements = {r['theorem']: r['statement'] for r in rows}
    definitions = {r['name']: r for r in interfaces}
    guard = guarded.source_guard(interfaces)
    value = definitions[TRACE + 'children']['value']
    _, _, root, context = telescope(value)
    family = joint.app(value, root, CHILD + 'constructors')
    native = joint.app(value, family[-2], gate.NS + 'unfold')
    named(value, native[-3:], context, ('owner', 'usizeBits', 'depth'))
    native_base = joint.app(value, native[-4], gate.NS + 'callerContext')
    named(value, native_base[-7:], context, ('ops', 'allocate', 'safety', 'owner', 'meaning', 'base', 'growth'))
    observed = joint.app(value, family[-1], TRACE + 'observe')
    captured = joint.app(value, observed[-1], TRACE + 'unfold')
    named(value, captured[-9:], context, ('ops', 'allocate', 'safety', 'owner', 'meaning', 'base', 'growth', 'usizeBits', 'depth'))
    for current, reference in (('selected_resource_preserved', 'selected_preserved'),
                               ('scoped_from_resources', 'scoped_from_children')):
        value, old = statements[MISS + current], statements[MISS + reference]
        fields, lets, root, context = telescope(value)
        prior, prior_lets, prior_root, prior_context = telescope(old)
        if expanded(value, root, context, lets) != expanded(old, prior_root, prior_context, prior_lets):
            raise ValueError('resource miss changed the original conclusion: ' + current)
        for name in ('initial', 'frame', 'aligned'):
            if expression(value, *fields[name]) != expression(old, *prior[name]):
                raise ValueError('resource miss changed native entry inputs: ' + name)
        child_contract(value, fields['coupled'], guard)
        action(value, *lets['action'])
        extra = set(fields) - set(prior) - {'ε', 'history', 'stream'}
        # Anonymous admission and ordinary guards can share their Lean binder name.
        admissions = []
        for name, (term, scope) in fields.items():
            head, args = gate.applied(value, term)
            if head[:2] == ['const', RESOURCE + 'Admitted']:
                named(value, args[-4:], scope, ('history', 'stream', 'action', 'before'))
                admissions.append(name)
        if len(admissions) != 1 or len(fields) != len(prior) + 4 or len(extra) != 1:
            raise ValueError('resource miss gained an outcome premise: ' + current)

    value = statements[MISS + 'from_frame']
    fields, _, root, context = telescope(value)
    prior, _, _, _ = telescope(statements[MISS + 'from_children'])
    if set(fields) != set(prior) - {'cursor', 'model', 'seed', 'predicate', 'initial', 'frame', 'coupled'} | {'preserved'}:
        raise ValueError('shared suffix changed its native premises')
    preserved, lets, tail, scope = telescope(value, *fields['preserved'])
    if len(preserved) != 1:
        raise ValueError('shared suffix changed its ordinary reached-frame guard')
    action(value, *lets['decision'], applied=True)
    term, local = next(iter(preserved.values()))
    equation = joint.app(value, term, 'Eq')
    named(value, equation[-1:], local, ('Bool.true',))
    completed = joint.app(value, equation[-2], gate.OWNED + 'ordinary')
    joint.path(value, completed[-1], local, ('Prod.fst',), 'decision')
    frame = joint.app(value, tail, gate.NS + 'InputFrame')
    joint.path(value, frame[-1], scope, ('Prod.snd',), 'decision')
    named(value, frame[-5:-1], scope, ('originalRows', 'source', 'values', 'slice'))
    joint.app(value, root, MISS + 'Completion')

    value = statements[CAPTURED]
    fields, lets, root, context = telescope(value)
    expected = {'σ', 'depth', 'ops', 'allocate', 'safety', 'owner', 'usizeBits', 'meaning', 'base', 'growth',
                'outerOps', 'outerAllocate', 'outerBase', 'outerGrowth', 'debug', 'source', 'address', 'input',
                'request', 'key', 'slice', 'deterministic', 'before', 'model', 'seed', 'predicate', 'values',
                'originalRows', 'initial', 'frame', 'aligned', 'handle', 'lookup', 'leading', 'trailing',
                'mismatch', 'detached', 'unowned', 'caller'}
    extra = set(fields) - expected
    if len(extra) != 1 or set(fields) != expected | extra:
        raise ValueError('captured resource miss gained admission, boundary or outcome premises')
    child_contract(value, fields[next(iter(extra))], guard, outer=True)
    traced = joint.app(value, lets['traced'][0], TRACE + 'children')
    named(value, traced[-9:], lets['traced'][1],
          ('ops', 'allocate', 'safety', 'owner', 'meaning', 'base', 'growth', 'usizeBits', 'depth'))
    action(value, *lets['action'], outer=True)
    call = local_call(value, *lets['captured'], 'action')
    restored = joint.app(value, call[0], CHILD + 'restore')
    joint.app(value, restored[-2], 'List.nil')
    erased = joint.app(value, restored[-1], CHILD + 'erase')
    named(value, erased[-1:], lets['captured'][1], ('before',))
    history = joint.app(value, lets['middle'][0], CHILD + 'history')
    joint.path(value, history[-1], lets['middle'][1], ('Prod.snd',), 'captured')
    cursor = joint.app(value, lets['cursor'][0], MISS + 'childCursor')
    named(value, cursor[-1:], lets['cursor'][1], ('before',))
    length = joint.app(value, cursor[-2], 'List.length')
    named(value, length[-1:], lets['cursor'][1], ('leading',))
    named(value, appended(value, lets['tailLeading'][0]), lets['tailLeading'][1], ('leading', 'middle'))
    parts = appended(value, lets['stream'][0])
    if len(parts) != 4:
        raise ValueError('captured resource stream lost its complete suffix')
    scope = lets['stream'][1]
    history = joint.app(value, parts[0], CHILD + 'history')
    after = joint.app(value, history[-1], 'Prod.snd')
    named(value, local_call(value, after[-1], scope, 'action'), scope, ('before',))
    joint.path(value, parts[1], scope, (MISS + 'Segment.body',), 'observed')
    joint.path(value, parts[2], scope, (MISS + 'Segment.cleanup',), 'observed')
    named(value, parts[3:], scope, ('trailing',))
    common = ('outerOps', 'outerAllocate', 'safety', 'owner', 'meaning', 'outerBase', 'outerGrowth', 'usizeBits',
              'traced', 'debug', 'source', 'address', 'input', 'request', 'key', 'slice', 'deterministic',
              'before', 'handle', 'lookup')
    observed = joint.app(value, lets['observed'][0], MISS + 'segment')
    named(value, observed[-len(common):], lets['observed'][1], common)
    for name, suffix in (('Completion', ('values', 'tailLeading', 'trailing', 'mismatch')),
                         ('Projected', ('cursor', 'model', 'seed', 'tailLeading', 'trailing', 'mismatch'))):
        args, scope = choice.one_call(value, root, context, MISS + name)
        named(value, args[-len(common + suffix):], scope, common + suffix)
    return {'sameExactSelectedAndScopedConclusions': True, 'sharedSuffixNeedsOnlyReachedNativeFrame': True,
            'actualGuardAndReachedRowsRetained': True, 'finiteNativeChildrenAndAllInputsBound': True,
            'capturedAdmissionAndCursorNotAssumed': True, 'sameHistoryAndFullSuffixBound': True,
            'allEntryResourceInductionVerified': False, 'completeStreamCorrespondenceVerified': False}


def controls(output, env, lean):
    groups = (
        ('core', 'Compiler.Extraction.InternerResourceMiss', (
            ('wrong-source-guard', '(deterministic && (request.item.kind == 1)) = true →',
             '(!deterministic && (request.item.kind == 1)) = true →', 2),
            ('missing-admission', 'Resource.Admitted history stream action before →', 'True →', 2),
            ('stale-child-rows', '(coupled selected (originalRows ++ added))', '(coupled selected originalRows)', 1),
        )),
        ('captured', 'Compiler.Extraction.InternerRecursiveResourceMiss', (
            ('rewind-stream', 'let stream := ChildTrace.history (action before).2 ++', 'let stream := ChildTrace.history before ++', 1),
            ('shift-cursor', 'let cursor := MissStream.childCursor leading.length before',
             'let cursor := MissStream.childCursor (leading.length + 1) before', 1),
            ('lose-child-segment', 'let tailLeading := leading ++ middle', 'let tailLeading := leading', 1),
        )),
    )
    records = []
    for group, module, changes in groups:
        code = source(module)
        records += checked_controls(output, [mutation_check(output, 'resource-miss-' + group + '-unchanged', code, True, env, lean)])
        for name, old, new, count in changes:
            if code.count(old) != count:
                raise ValueError('ambiguous resource miss mutation: ' + name)
            records += checked_controls(output, [mutation_check(output, 'resource-miss-' + group + '-' + name,
                code.replace(old, new), False, env, lean)])
    code = source('Compiler.Extraction.InternerMissAdmission')
    old = 'ordinary decision.1 = true → InputFrame safety base.allocator owner originalRows source values slice decision.2)'
    if code.count(old) != 1:
        raise ValueError('ambiguous reached suffix frame mutation')
    # Its positive control is already in guarded_induction_checks.
    records += checked_controls(output, [mutation_check(output, 'resource-miss-stale-suffix-frame',
        code.replace(old, old.replace('slice decision.2)', 'slice before)')), False, env, lean)])
    return records
