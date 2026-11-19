"""Audit shared native-entry replay and its complete scoped-miss consumer.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
import constructor_replay_choice_checks as choice
from native_miss_frame_checks import named
from native_algebraic_dispatch_checks import source
from native_resource_admission_checks import telescope, local_call
from native_frame_step_checks import recursive_children
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check

NS, ITEM, OWNED = gate.NS, gate.ITEM, gate.OWNED
TRACE = NS + 'AllocationTrace.'
CHILD = NS + 'ChildTrace.'
RESOURCE = OWNED + 'Recursive.Resource.'
MISS = OWNED + 'MissStream.'
TESTS = ITEM + 'NativeAllocationEntryTests.'
CORE = ('rebase_slot', 'enter_relative_admitted', 'record_grows', 'record_mark', 'enter_native_keeps',
        'enter_projects', 'marked_projects', 'source_projects', 'record_marked_map', 'step_source_projects',
        'scoped_resource_miss', 'frame_input', 'scoped_from_bodies')
REGRESSIONS = ('history_retains_outcome', 'later_entry', 'split_real_capture', 'raw_stream_rejected')
CLAIMS = [TRACE + n for n in CORE] + [TESTS + n for n in REGRESSIONS]
CLAIMS += [NS + 'InputFrame.mapAllocator_iff', MISS + 'scoped_recorded_resources']
INTERFACES = tuple(TRACE + n for n in ('rebase', 'record', 'enterNative', 'Prefixed', 'Frame', 'BodyReplay',
                                      'replay', 'BodiesAt.mk', 'Prefixes', 'body')) + (MISS + 'CapturedMiss',)


def audit(claims):
    required = {
        TRACE + 'enter_relative_admitted': {TRACE + 'rebase_slot', TRACE + 'admitted_entry'},
        TRACE + 'enter_projects': {TRACE + 'rebase_slot', TRACE + 'enter_native_keeps'},
        TRACE + 'marked_projects': {TRACE + 'record_mark', TRACE + 'enter_projects',
                                    RESOURCE + 'Admitted.first', RESOURCE + 'Admitted.next'},
        TRACE + 'source_projects': {TRACE + 'marked_projects'},
        TRACE + 'step_source_projects': {TRACE + 'source_projects', TRACE + 'children_recorded',
                                         TRACE + 'step_prefix'},
        TRACE + 'frame_input': {NS + 'InputFrame.mapAllocator_iff'},
        TRACE + 'scoped_from_bodies': {TRACE + 'step_source_projects', TRACE + 'frame_input',
                                      TRACE + 'scoped_resource_miss'},
        TRACE + 'scoped_resource_miss': {MISS + 'scoped_recorded_resources'},
        MISS + 'scoped_recorded_resources': {MISS + 'child_boundaries', MISS + 'scoped_from_resources',
                                            RESOURCE + 'Admitted.captured'},
        NS + 'CallFrame.mapAllocator_iff': {NS + 'InputFrame.mapAllocator_iff'},
        TESTS + 'history_retains_outcome': {ITEM + 'NativeAllocationTraceTests.recorded_result'},
        TESTS + 'later_entry': {TRACE + 'enter_relative_admitted'},
        TESTS + 'split_real_capture': {TRACE + 'record_mark', TRACE + 'step_prefix'},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('allocation entry lost shared composition: ' + name + ': ' + ', '.join(sorted(missing)))
    for name in [TRACE + n for n in CORE] + [MISS + 'scoped_recorded_resources']:
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('allocation entry depends on a fixture: ' + name)
    return {'checkedDependencies': sorted(required), 'entryReplayConsumedByScopedMiss': True,
            'sameMissCompositionForBothCaptureFamilies': True, 'allFiveSourceRoutesUseSharedEntry': True,
            'nativeBodyReplayStillRequired': True, 'allEntryResourceInductionVerified': False,
            'recursiveWordPreservationVerified': False, 'composedProductionTheoremVerified': False}


def audit_statements(rows, interfaces):
    statements = {r['theorem']: r['statement'] for r in rows}
    definitions = {r['name']: r for r in interfaces}
    expected = {
        'rebase_slot': {'leading', 'stream', 'origin', 'position', 'reached'},
        'enter_projects': {'σ', 'leading', 'stream', 'root', 'predicate'},
        'marked_projects': {'σ', 'action', 'prefixed', 'leading', 'stream', 'root', 'predicate', 'model', 'body'},
        'source_projects': {'σ', 'captured', 'prefixed', 'leading', 'stream', 'root', 'predicate', 'reads', 'debug', 'models', 'bodies'},
        'step_source_projects': {'σ', 'ops', 'allocate', 'safety', 'owner', 'meaning', 'base', 'growth', 'usizeBits',
                                 'depth', 'leading', 'stream', 'root', 'predicate', 'reads', 'debug', 'models', 'bodies'},
    }
    for name, wanted in expected.items():
        if set(telescope(statements[TRACE + name])[0]) != wanted:
            raise ValueError('allocation entry changed its premises: ' + name)
    value = definitions[TRACE + 'rebase']['value']
    _, _, root, context = telescope(value)
    append = joint.app(value, root, 'HAppend.hAppend')
    named(value, append[-2:-1], context, ('leading',))
    named(value, joint.app(value, append[-1], 'List.drop')[-2:], context, ('origin', 'stream'))

    value = definitions[TRACE + 'Frame']['value']
    _, _, root, context = telescope(value)
    parts = joint.app(value, root, 'And')
    prefix = joint.app(value, parts[-1], 'List.IsPrefix')
    for term, world in zip(prefix[-2:], ('root', 'before')):
        named(value, joint.app(value, term, CHILD + 'history')[-1:], context, (world,))
    erased = joint.app(value, local_call(value, parts[-2], context, 'predicate')[-1], CHILD + 'erase')
    named(value, erased[-1:], context, ('before',))

    # Replay's body receives both cursors of its actual entry state. Its only
    # guards are the native frame, actual admission and ordinary outcome.
    value = definitions[TRACE + 'BodyReplay']['value']
    fields, _, root, context = telescope(value)
    # Local model calls occur once in each result/graph equation.
    parts = joint.app(value, root, 'And')
    pair = joint.app(value, parts[-1], 'And')
    for term, wrapped in zip(pair[-2:], (True, False)):
        equation = joint.app(value, term, 'Eq')
        right = equation[-1]
        if wrapped:
            right = joint.app(value, right, 'Except.mapError')[-1]
        result = joint.app(value, right, 'Prod.fst' if wrapped else 'Prod.snd')
        args = local_call(value, result[-1], context, 'model')
        ids = joint.app(value, args[-2], 'Prod.mk')
        for item, cursor in zip(ids[-2:], ('nextId', 'nextAddress')):
            joint.path(value, item, context, ('Compiler.ZigAir.Memory.State.' + cursor,
                'Compiler.Extraction.Memory.Arguments.Normalization.Session.memory', OWNED + 'World.memory'), 'before')
        observed = joint.app(value, args[-1], OWNED + 'Recursive.cursorGraph')
        named(value, observed[-1:], context, ('before',))
        cursor = joint.app(value, observed[-2], MISS + 'childCursor')
        named(value, cursor[-1:], context, ('root',))
        named(value, joint.app(value, cursor[-2], 'List.length')[-1:], context, ('leading',))
    if len(fields) != 11:
        raise ValueError('body replay gained an outcome assumption')

    value = definitions[TRACE + 'BodiesAt.mk']['type']
    fields, _, _, _ = telescope(value)
    routes = {'operation': ('operation', ('opcode', 'values', 'debug')),
              'constant': ('constant', ('value', 'debug')),
              'materialize': ('materialize', ('id', 'value', 'debug')),
              'borrowed': ('borrowedOperation', None), 'namedLocal': ('localOperation', None)}
    if set(fields) != {'σ', 'leading', 'stream', 'root', 'predicate', 'reads', 'debug', 'captured', 'models'} | routes.keys():
        raise ValueError('body replay lost a constructor route')
    for field, (route, arguments) in routes.items():
        parameters, _, root, context = telescope(value, *fields[field])
        ordered = list(parameters.values())
        if field in ('borrowed', 'namedLocal'):
            if len(ordered) != (5 if field == 'borrowed' else 9):
                raise ValueError('source body changed its query/shape guards')
            equation = joint.app(value, ordered[3][0], 'Eq')
            query = joint.app(value, equation[-2], 'Compiler.Extraction.Nested.Reads.operation')
            named(value, query[-3:], ordered[3][1], ('reads', 'id', 'queried' if field == 'borrowed' else 'opcode'))
            found = joint.app(value, joint.app(value, equation[-1], 'Except.ok')[-1], 'Option.some')
            named(value, found[-1:], ordered[3][1], ('source',))
            if field == 'namedLocal':
                shape = joint.app(value, ordered[4][0], 'Eq')
                joint.path(value, shape[-2], ordered[4][1],
                           ('List.length', 'Compiler.Extraction.Storage.ArgumentSlice.items'), 'source')
                bound = joint.app(value, ordered[6][0], 'LT.lt')
                named(value, bound[-2:-1], ordered[6][1], ('selected',))
                for term in (shape[-1], bound[-1]):
                    number = joint.app(value, term, 'OfNat.ofNat')
                    if value['nodes'][number[-2]] != ['natural', '2']:
                        raise ValueError('source body lost binary local admission')
        replayed = joint.app(value, root, TRACE + 'BodyReplay')
        named(value, replayed[-6:-2], context, ('leading', 'stream', 'root', 'predicate'))
        for item, family in zip(replayed[-2:], ('captured', 'models')):
            selected = joint.app(value, item, 'Compiler.Extraction.Associative.Constructors.' + route)
            named(value, selected[2:3], context, (family,))
            if arguments:
                named(value, selected[3:], context, arguments)
            elif field == 'borrowed':
                for term, member in ((selected[-4], 'address'), (selected[-2], 'items')):
                    joint.path(value, term, context, ('Compiler.Extraction.Storage.ArgumentSlice.' + member,), 'source')
                named(value, [selected[-3], selected[-1]], context, ('opcode', 'debug'))
            else:
                named(value, selected[-6:], context, ('opcode', 'source', 'selected', 'repeated', 'first', 'debug'))

    for name in ('source_projects', 'step_source_projects'):
        value = statements[TRACE + name]
        fields, _, root, context = telescope(value)
        proper = joint.app(value, root, 'Compiler.Extraction.Dispatch.Effects.SourceConstructorsAt')
        effect = joint.app(value, proper[-5], RESOURCE + 'projection')
        joint.app(value, effect[-4], CHILD + 'history')
        named(value, effect[-3:-2], context, ('stream',))
        held = joint.app(value, effect[-1], TRACE + 'Frame')
        named(value, held[-2:], context, ('root', 'predicate'))
        named(value, proper[-4:-2], context, ('reads', 'debug'))
        model = joint.app(value, proper[-1], TRACE + 'replay')
        named(value, model[-4:], context, ('leading', 'stream', 'root', 'models'))
        obligation = joint.app(value, fields['bodies'][0], TRACE + 'BodiesAt')
        named(value, obligation[-8:-2], fields['bodies'][1], ('leading', 'stream', 'root', 'predicate', 'reads', 'debug'))
        named(value, obligation[-1:], fields['bodies'][1], ('models',))

    value = definitions[TRACE + 'body']['value']
    _, _, root, context = telescope(value)
    step = joint.app(value, root, TRACE + 'step')
    recursive_children(value, step[-2], context, False)
    observed = joint.app(value, step[-1], NS + 'ProtocolTrace.observe')
    captured = joint.app(value, observed[-1], TRACE + 'unfold')
    named(value, captured[-9:], context, ('ops', 'allocate', 'safety', 'owner', 'meaning', 'base', 'growth', 'usizeBits', 'depth'))

    value = statements[TRACE + 'scoped_from_bodies']
    fields, lets, root, context = telescope(value)
    # The complete stream and cursor remain locally derived, not new premises.
    for name in ('stream', 'cursor', 'traced', 'model', 'action', 'middle', 'tailLeading'):
        if name in fields or name not in lets:
            raise ValueError('body miss assumes a derived boundary: ' + name)
    model = joint.app(value, lets['model'][0], TRACE + 'replay')
    named(value, model[-4:], lets['model'][1], ('leading', 'stream', 'before', 'models'))
    proper, scope = choice.one_call(value, fields[next(reversed(fields))][0], fields[next(reversed(fields))][1], TRACE + 'BodiesAt')
    named(value, proper[-8:-5], scope, ('leading', 'stream', 'before'))
    actual = joint.app(value, proper[-2], TRACE + 'body')
    named(value, actual[-9:], scope, ('ops', 'allocate', 'safety', 'owner', 'meaning', 'base', 'growth', 'usizeBits', 'depth'))
    named(value, proper[-1:], scope, ('models',))
    return {'actualEntryCursorsForwardedToBody': True, 'rawHistoryPrefixRetained': True,
            'relativeCursorUsesRebasedStream': True, 'immediateNativeAndMarkedChildrenBound': True,
            'allFiveBodiesAndSharedMissBound': True, 'nativeBodyReplayStillRequired': True,
            'allEntryResourceInductionVerified': False, 'composedProductionTheoremVerified': False}


def controls(output, env, lean):
    groups = (
        ('entry', 'InternerNativeAllocationEntry', (
            ('raw-stream', 'leading ++ stream.drop origin', 'leading ++ stream.drop (origin - origin)'),
            ('origin-underflow', '(reached : origin ≤ position)', '(reached : origin ≤ position + 1)'),
            ('skip-entry', '(enter (rebase leading (ChildTrace.history root).length stream) >>= model)', '(model (0, 0))'),
            ('wrong-forwarded-id', '(enter (rebase leading (ChildTrace.history root).length stream) >>= model)',
             '(enter (rebase leading (ChildTrace.history root).length stream) >>= fun ids => model (ids.1 + 1, ids.2))'),
            ('wrong-forwarded-address', '(enter (rebase leading (ChildTrace.history root).length stream) >>= model)',
             '(enter (rebase leading (ChildTrace.history root).length stream) >>= fun ids => model (ids.1, ids.2 + 1))'),
        )),
        ('source', 'InternerAllocationSourceReplay', (
            ('wrong-constant', '(models.constant value debug)', '(models.constant 0 debug)'),
            ('borrowed-query', 'reads.operation id queried = .ok (some source)', 'reads.operation id queried = .ok none'),
            ('local-shape', 'source.items.length = 2 →', 'source.items.length = 1 →'),
            ('local-bound', 'selected < 2 →', 'selected ≤ 2 →'),
        )),
        ('miss', 'InternerAllocationResourceMiss', (
            ('lost-child-prefix', 'let tailLeading := leading ++ middle', 'let tailLeading := leading'),
            ('shift-cursor', 'let cursor := MissStream.childCursor leading.length before',
             'let cursor := MissStream.childCursor (leading.length + 1) before'),
            ('stale-stream', 'let stream := ChildTrace.history (action before).2 ++', 'let stream := ChildTrace.history before ++'),
        )),
    )
    records = []
    for group, module, changes in groups:
        code = source('Compiler.Extraction.' + module)
        records += checked_controls(output, [mutation_check(output, 'allocation-entry-' + group + '-unchanged', code, True, env, lean)])
        for name, old, new in changes:
            if code.count(old) != 1:
                raise ValueError('ambiguous allocation entry mutation: ' + name)
            records += checked_controls(output, [mutation_check(output, 'allocation-entry-' + group + '-' + name,
                code.replace(old, new), False, env, lean)])
    return records
