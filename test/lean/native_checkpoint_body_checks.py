"""Audit proper-child replay through the fixed checkpoint caller and close.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
import guarded_induction_checks as guarded
from native_miss_frame_checks import named
from native_resource_admission_checks import telescope
from native_resource_miss_checks import appended
from native_checkpoint_constructor_checks import numeral
from native_algebraic_dispatch_checks import source
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check

CALLER = gate.OWNED + 'Caller.ProtocolTrace.'
NATIVE = CALLER + 'Native.'
TRACE = gate.NS + 'AllocationTrace.'
CHILD = gate.NS + 'ChildTrace.'
MISS = gate.OWNED + 'MissStream.'
CLAIMS = [CALLER + 'missBody_selected_ordinary', TRACE + 'selected_from_bodies', TRACE + 'checkpoint_from_bodies']
INTERFACES = ()


def audit(claims):
    required = {
        CLAIMS[0]: {CALLER + 'missBody_erases', MISS + 'routed'},
        CLAIMS[1]: {TRACE + 'step_source_projects', TRACE + 'frame_input', MISS + 'selected_resource_preserved',
                    NATIVE + 'history_boundaries', gate.OWNED + 'Recursive.Resource.Admitted.captured'},
        CLAIMS[2]: {CLAIMS[0], CLAIMS[1], NATIVE + 'checkpoint_miss', TRACE + 'insertionReplay_inputs',
                    gate.NS + 'CallFrame.mapAllocator_iff', MISS + 'scoped_ports'},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('checkpoint body lost shared composition: ' + name + ': ' + ', '.join(sorted(missing)))
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('checkpoint body depends on fixtures: ' + name)
    return {'checkedDependencies': sorted(required), 'properBodiesSupplyDispatcherAndFrame': True,
            'actualHistorySuppliesAdmissionAndCursors': True, 'fixedInputModelReachesRecordedMissAndClose': True,
            'completeConstructorBodyReplayVerified': False, 'recursiveWordPreservationVerified': False,
            'nativeAdmissionDerived': False, 'composedProductionTheoremVerified': False}


def audit_statements(rows, interfaces):
    statements = {row['theorem']: row['statement'] for row in rows}
    guard = guarded.source_guard(interfaces)
    common = {'σ', 'depth', 'ops', 'allocate', 'safety', 'owner', 'usizeBits', 'meaning', 'base', 'growth',
              'outerOps', 'outerAllocate', 'outerBase', 'outerGrowth', 'debug', 'source', 'address', 'input',
              'request', 'key', 'slice', 'deterministic', 'before', 'models', 'seed', 'values', 'originalRows',
              'parent', 'frame', 'aligned', 'leading'}
    for name in CLAIMS[1:]:
        value = statements[name]
        fields, lets, root, context = telescope(value)
        complete = name == CLAIMS[2]
        unnamed = [key for key in fields if key.startswith('a.')]
        expected = common | ({'buffer', 'handle', 'lookup', 'incoming', 'incomingAddress', 'trailing', 'mismatch',
                              'admitted', 'detached', 'unowned', 'caller'} if complete else {'suffix'})
        if set(fields) != expected | set(unnamed) or len(unnamed) != (2 if complete else 1):
            raise ValueError('checkpoint body gained a reached frame, stream admission, cursor or result premise')
        frame, scope = fields['frame']
        initial = joint.app(value, frame, gate.NS + 'CallFrame')
        joint.path(value, initial[-1], scope, (CHILD + 'erase',), 'before')
        named(value, initial[-8:-1], scope, ('originalRows', 'source', 'values', 'slice', 'address', 'input', 'parent'))
        proper, scope = guarded.guarded_body(value, *fields[unnamed[0]], guard)
        child_fields, _, body, local = telescope(value, proper, scope)
        if list(child_fields) != ['rows']:
            raise ValueError('checkpoint body lost reached-row quantification')
        body = joint.app(value, body, TRACE + 'BodiesAt')
        named(value, body[1:4], local, ('leading', 'rawStream' if complete else 'stream', 'before'))
        _, _, framed, world = telescope(value, body[4], local)
        retained, reached = joint.app(value, framed, 'And')
        retained = joint.app(value, retained, gate.NS + 'CallFrame')
        named(value, retained[-8:], world, ('originalRows', 'source', 'values', 'slice', 'address', 'input', 'parent', 'world'))
        reached = joint.app(value, reached, gate.NS + 'InputFrame')
        named(value, reached[-5:], world, ('rows', 'source', 'values', 'slice', 'world'))
        named(value, body[-3:-2] + body[-1:], local, ('debug', 'models'))
        native = joint.app(value, body[-2], TRACE + 'body')
        named(value, native[1:], local, ('ops', 'allocate', 'safety', 'owner', 'meaning', 'base', 'growth', 'usizeBits', 'depth'))
        traced = joint.app(value, lets['traced'][0], TRACE + 'children')
        named(value, traced[1:-1], lets['traced'][1], ('ops', 'allocate', 'safety', 'owner', 'meaning', 'base', 'growth', 'usizeBits'))
        successor = joint.app(value, traced[-1], 'HAdd.hAdd')
        named(value, successor[-2:-1], lets['traced'][1], ('depth',))
        numeral(value, successor[-1], 1)
        replay = joint.app(value, lets['model'][0], TRACE + 'replay')
        named(value, replay[-4:], lets['model'][1], ('leading', 'rawStream' if complete else 'stream', 'before', 'models'))
        if not complete:
            continue
        # The raw stream retains its native prefix; the local stream retains
        # the caller prefix. They share the same child body and close suffix.
        raw = appended(value, lets['rawStream'][0])
        if len(raw) != 4:
            raise ValueError('checkpoint body lost its complete raw suffix')
        scope = lets['rawStream'][1]
        joint.path(value, raw[0], scope, (CHILD + 'history', 'Prod.snd'), 'decision')
        named(value, raw[1:2] + raw[-1:], scope, ('bodyEvents', 'trailing'))
        joint.path(value, raw[2], scope, (MISS + 'Segment.cleanup',), 'observed')
        history = appended(value, lets['history'][0])
        if len(history) != 4:
            raise ValueError('checkpoint body lost local history')
        named(value, history[:3], lets['history'][1], ('leading', 'middle', 'bodyEvents'))
        joint.path(value, history[-1], lets['history'][1], (MISS + 'Segment.cleanup',), 'observed')
        named(value, appended(value, lets['stream'][0]), lets['stream'][1], ('history', 'trailing'))
        model = joint.app(value, lets['logicalModel'][0], gate.NS + 'dispatchModel')
        named(value, model[-3:], lets['logicalModel'][1], ('model', 'usizeBits', 'debug'))
        fixed = joint.app(value, model[-4], TRACE + 'inputGraphReplay')
        named(value, fixed, lets['logicalModel'][1], ('seed', 'input', 'incoming', 'meaning', 'stream', 'mismatch'))
        physical = joint.app(value, lets['p'][0], NATIVE + 'physical')
        named(value, physical[1:], lets['p'][1], ('outerOps', 'outerAllocate', 'safety', 'owner', 'meaning', 'outerBase',
                                                'outerGrowth', 'usizeBits', 'traced', 'debug', 'source', 'address', 'input'))
        logical = joint.app(value, lets['logical'][0], 'Compiler.Extraction.Interner.FindCode.controlMiss')
        execution = joint.app(value, logical[-5], 'Compiler.Extraction.Interner.Scoped.execution')
        named(value, execution[-2:], lets['logical'][1], ('resources', 'logicalModel'))
        named(value, logical[-4:-1], lets['logical'][1], ('request', 'key', 'deterministic'))
        joint.path(value, logical[-1], lets['logical'][1], (CALLER + 'scopeView',), 'initialRecord')
        called = joint.app(value, lets['actualBody'][0], CALLER + 'missBody')
        named(value, called[-9:-8] + called[-7:], lets['actualBody'][1],
              ('p', 'ports', 'source', 'buffer', 'request', 'key', 'deterministic', 'initialRecord'))
        joint.path(value, called[-8], lets['actualBody'][1], (gate.ITEM + 'ShiftInput.Context.queries',), 'outerBase')
        actual = joint.app(value, lets['actual'][0], CALLER + 'finish')
        for term, member in zip(actual[-2:], ('Prod.fst', 'Prod.snd')):
            joint.path(value, term, lets['actual'][1], (member,), 'actualBody')
        outcome, scope = fields[unnamed[1]]
        equality = joint.app(value, outcome, 'Eq')
        named(value, equality[-1:], scope, ('Bool.true',))
        joint.path(value, joint.app(value, equality[-2], gate.OWNED + 'ordinary')[-1], scope, ('Prod.fst',), 'actualBody')
        claims = []
        for _ in range(3):
            first, root = joint.app(value, root, 'And')
            claims.append(first)
        claims.append(root)
        for index, world in enumerate(('actualBody', 'actual')):
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
        named(value, equation[-1:], context, ('history',))
        equation = joint.app(value, claims[3], 'Eq')
        named(value, equation[-1:], context, ('Bool.false',))
        joint.path(value, equation[-2], context,
                   (CALLER + 'Tokens.incomplete', CALLER + 'Recorded.tokens', 'Prod.snd'), 'actual')
    return {'properChildDepthAndSourceGuard': True, 'noReachedFrameOrProjectionPremise': True,
            'rawAndRelativeHistoriesRetained': True, 'fixedInputModelAndCompleteClose': True,
            'completeConstructorBodyReplayVerified': False, 'composedProductionTheoremVerified': False}


def controls(output, env, lean):
    code = source('Compiler.Extraction.InternerCheckpointBodyReplay')
    # Keep mismatched recursive constructors explicit in diagnostics. This
    # changes printing for both partners, not proof limits or rejection rules.
    code = code.replace('namespace Compiler.Extraction.',
                        'set_option pp.all true\n\nnamespace Compiler.Extraction.', 1)
    changes = (
        ('wrong-depth', '(depth + 1)', '(depth + 2)', 5),
        ('wrong-guard', '(deterministic && (request.item.kind == 1)) = true →',
         '(!deterministic && (request.item.kind == 1)) = true →', 2),
        ('wrong-body-stream', 'BodiesAt leading rawStream before', 'BodiesAt leading [] before', 1),
        ('wrong-child-prefix', 'let model := replay leading rawStream before models', 'let model := replay [] rawStream before models', 1),
        ('stale-frame', 'parent (ChildTrace.erase decision.2) ∧', 'parent (ChildTrace.erase before) ∧', 1),
        ('rewind-raw-stream', 'let rawStream := ChildTrace.history decision.2 ++', 'let rawStream := ChildTrace.history before ++', 1),
        ('missing-checkpoint', 'let ports := graphObservations outerOps', 'let ports := Caller.ProtocolTrace.Native.graphObservations outerOps', 1),
        ('wrong-input-address', 'inputGraphReplay seed input incoming meaning', 'inputGraphReplay seed input (incoming + 1) meaning', 1),
        ('wrong-return', '= (logical.1.mapError Fault.language, logical.2) ∧', '= (.error (.language .outOfMemory), logical.2) ∧', 1),
        ('lost-close', '(logical.1.mapError Fault.language, Interner.Scoped.close resources logical.2) ∧',
         '(logical.1.mapError Fault.language, logical.2) ∧', 1),
        ('lost-history', 'actual.2.events = history ∧ actual.2.tokens.incomplete = false := by',
         'actual.2.events = leading ∧ actual.2.tokens.incomplete = false := by', 1),
    )
    records = checked_controls(output, [mutation_check(output, 'checkpoint-bodies-unchanged', code, True, env, lean)])
    for name, old, new, count in changes:
        if code.count(old) != count:
            raise ValueError('ambiguous checkpoint body mutation: ' + name + ': ' + str(code.count(old)))
        records += checked_controls(output, [mutation_check(output, 'checkpoint-bodies-' + name,
            code.replace(old, new), False, env, lean)])
    return records
