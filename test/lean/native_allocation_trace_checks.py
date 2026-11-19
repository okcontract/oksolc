"""Audit native entry identities in the actual recursive resource capture.
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
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NS, ITEM, OWNED = gate.NS, gate.ITEM, gate.OWNED
TRACE = NS + 'AllocationTrace.'
TESTS = ITEM + 'NativeAllocationTraceTests.'
MEMORY = 'Compiler.ZigAir.Memory.'
RESOURCE = OWNED + 'Recursive.Resource.'
CHILD = NS + 'ChildTrace.'
CAPTURE = ITEM + 'ProtocolTrace.'
CORE = ('mark_begins', 'marked_map', 'mark_erases', 'unfold_erases', 'unfold_marked',
        'children_recorded', 'children_erases', 'admitted_entry', 'admitted_identity',
        'enter_admitted', 'admitted_allocate', 'step_erases', 'step_prefix', 'insertion_read', 'insertion_replayed')
REGRESSIONS = ('marked', 'capture_native', 'recorded_result', 'recorded_admitted',
               'parent_retained', 'wrong_stream_rejected', 'replay_entry', 'shifted_rejected',
               'nested_entries', 'entry_is_foreign', 'replay_rejects_foreign', 'replay_rejects_missing',
               'reached_insertion', 'shifted_insertion', 'insertion_is_foreign', 'checkpoint_kind_rejected')
CLAIMS = [MEMORY + 'allocate_same_cursors'] + [TRACE + n for n in CORE] + [TESTS + n for n in REGRESSIONS]
CLAIMS += [NS + 'ProtocolTrace.' + n for n in ('stepWith_erases', 'stepWith_prefix')]
CLAIMS += [NS + 'CallFrame.' + n for n in ('insertion_checkpoint_stream', 'insertion_checkpoint_agrees')]
CLAIMS += [OWNED + 'Caller.ProtocolTrace.' + n for n in ('miss_insert_recorded', 'Native.miss_recorded', 'Native.checkpoint_insert_miss')]
CLAIMS += [OWNED + 'MissStream.scoped_insert_irrelevant', OWNED + 'Caller.ProtocolTrace.miss_insert_irrelevant',
           OWNED + 'Caller.ProtocolTrace.Native.checkpoint_miss']
INTERFACES = tuple(TRACE + n for n in ('entry', 'mark', 'Begins', 'Marked.mk', 'unfold', 'children', 'enter'))
INTERFACES += tuple(TRACE + n for n in ('insertionEntry', 'graphObservations', 'step', 'insertionRead', 'insertionReplay'))
INTERFACES += (NS + 'ProtocolTrace.stepWith', 'Compiler.Extraction.Interner.InvocationTrace.Event.nativeEntry',
               'Compiler.Extraction.Interner.InvocationTrace.Event.nativeInsertion')
INTERFACES += (TRACE + 'graphReplay',)


def audit(claims):
    required = {
        MEMORY + 'allocate_same_cursors': {MEMORY + 'allocate'},
        TRACE + 'marked_map': {TRACE + 'mark_begins'},
        TRACE + 'unfold_erases': {TRACE + 'mark_erases', TRACE + 'step_erases'},
        TRACE + 'unfold_marked': {TRACE + 'marked_map', TRACE + 'step_prefix', NS + 'ProtocolTrace.unfold_prefix'},
        TRACE + 'step_erases': {NS + 'ProtocolTrace.stepWith_erases'},
        TRACE + 'step_prefix': {NS + 'ProtocolTrace.stepWith_prefix'},
        NS + 'ProtocolTrace.stepWith_erases': {CAPTURE + 'constructors_erases', NS + 'ProtocolTrace.map_atDebug'},
        NS + 'ProtocolTrace.stepWith_prefix': {CAPTURE + 'constructors_prefix', NS + 'ProtocolTrace.map_atDebug'},
        TRACE + 'insertion_read': {TRACE + 'insertionRead', TRACE + 'insertionEntry'},
        TRACE + 'insertion_replayed': {TRACE + 'insertion_read', OWNED + 'Insertion.Native.insert_allocation_replayed'},
        NS + 'CallFrame.insertion_checkpoint_stream': {TRACE + 'insertion_replayed', OWNED + 'Caller.ProtocolTrace.Native.insertion_events'},
        NS + 'CallFrame.insertion_checkpoint_agrees': {NS + 'CallFrame.insertion_checkpoint_stream'},
        OWNED + 'Caller.ProtocolTrace.miss_insert_recorded': {OWNED + 'Caller.ProtocolTrace.miss_routed'},
        OWNED + 'MissStream.scoped_insert_irrelevant': {OWNED + 'MissStream.scoped_routed'},
        OWNED + 'Caller.ProtocolTrace.miss_insert_irrelevant': {OWNED + 'Caller.ProtocolTrace.miss_routed'},
        OWNED + 'Caller.ProtocolTrace.Native.checkpoint_miss': {
            OWNED + 'Caller.ProtocolTrace.Native.checkpoint_insert_miss', OWNED + 'Caller.ProtocolTrace.Native.miss_from_projection',
            OWNED + 'MissStream.from_frame', OWNED + 'MissStream.projected',
            OWNED + 'MissStream.scoped_insert_irrelevant', OWNED + 'Caller.ProtocolTrace.miss_insert_irrelevant'},
        OWNED + 'Caller.ProtocolTrace.Native.miss_recorded': {OWNED + 'Caller.ProtocolTrace.miss_insert_recorded'},
        OWNED + 'Caller.ProtocolTrace.Native.checkpoint_insert_miss': {
            NS + 'CallFrame.insertion_checkpoint_stream', OWNED + 'Caller.ProtocolTrace.miss_insert_recorded',
            OWNED + 'MissStream.scoped_selected', OWNED + 'Caller.Close.transferred_stream',
            OWNED + 'Caller.ProtocolTrace.finish_projected'},
        TRACE + 'children_recorded': {TRACE + 'unfold_erases'},
        TRACE + 'children_erases': {CHILD + 'constructors_erase'},
        TRACE + 'admitted_identity': {TRACE + 'admitted_entry'},
        TRACE + 'enter_admitted': {TRACE + 'admitted_entry'},
        TRACE + 'admitted_allocate': {TRACE + 'admitted_identity', MEMORY + 'allocate_same_cursors'},
        TESTS + 'marked': {TRACE + 'unfold_marked'},
        TESTS + 'capture_native': {TRACE + 'unfold_erases'},
        TESTS + 'recorded_result': {TESTS + 'capture_native', ITEM + 'NativeAllocationAdmissionTests.successful',
                                    ITEM + 'NativeAllocationAdmissionTests.refused'},
        TESTS + 'recorded_admitted': {RESOURCE + 'Admitted.captured'},
        TESTS + 'parent_retained': {TESTS + 'capture_native', ITEM + 'NativeFrameInductionTests.parent_retained'},
        TESTS + 'replay_entry': {TRACE + 'enter_admitted', TESTS + 'recorded_admitted'},
        TESTS + 'shifted_rejected': {TRACE + 'admitted_identity', ITEM + 'Arguments.prepare_success',
                                    ITEM + 'NativeAllocationIdentityTests.extra_prepared'},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('native allocation capture lost composition: ' + name + ': ' + ', '.join(sorted(missing)))
    for name in [n for n in required if not n.startswith(TESTS)]:
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('native allocation capture depends on fixtures: ' + name)
    return {'checkedDependencies': sorted(required), 'nativeEntryIdentityDerivedFromAdmission': True,
            'nativeAllocationObservationAgreementDerived': True, 'actualNestedEntriesExercised': True,
            'reachedInsertionCheckpointConsumed': True, 'ordinaryInsertionAgreementWithoutIdentityPremise': True,
            'checkpointReplayReachesSelectedCallerAndClose': True, 'allSelectedMissBranchesConsumed': True,
            'allEntryResourceInductionVerified': False, 'completeStreamCorrespondenceVerified': False,
            'recursiveWordPreservationVerified': False, 'composedProductionTheoremVerified': False}


def audit_statements(rows, interfaces):
    statements = {r['theorem']: r['statement'] for r in rows}
    definitions = {r['name']: r for r in interfaces}
    # Bound the general result to initial observations and admission. In
    # particular no success, returned graph, or completed child proof is an input.
    expected = {
        MEMORY + 'allocate_same_cursors': {'state', 'other', 'child', 'valid', 'otherValid', 'identity', 'address'},
        TRACE + 'admitted_entry': {'σ', 'action', 'marked', 'stream', 'before', 'admitted'},
        TRACE + 'admitted_identity': {'σ', 'left', 'right', 'leftMarked', 'rightMarked', 'stream',
                                     'before', 'other', 'position', 'leftAdmitted', 'rightAdmitted'},
        TRACE + 'admitted_allocate': {'σ', 'left', 'right', 'leftMarked', 'rightMarked', 'stream',
                                     'before', 'other', 'observed', 'leftAdmitted', 'rightAdmitted', 'valid', 'otherValid', 'child'},
        TRACE + 'enter_admitted': {'σ', 'action', 'marked', 'stream', 'before', 'admitted'},
    }
    for name, wanted in expected.items():
        fields, _, _, _ = telescope(statements[name])
        if set(fields) != wanted:
            raise ValueError('native allocation proof changed its premises: ' + name + ': ' + str(set(fields) ^ wanted))
    for name in ('admitted_identity', 'admitted_allocate'):
        value = statements[TRACE + name]
        fields, _, _, _ = telescope(value)
        for premise, action, world in (('leftAdmitted', 'left', 'before'), ('rightAdmitted', 'right', 'other')):
            term, context = fields[premise]
            admitted = joint.app(value, term, RESOURCE + 'Admitted')
            joint.app(value, admitted[-4], CHILD + 'history')
            named(value, [admitted[-3], admitted[-1]], context, ('stream', world))
            recorded = joint.app(value, admitted[-2], CHILD + 'record')
            erased = joint.app(value, recorded[-2], CAPTURE + 'eraseCapture')
            joint.app(value, erased[-2], 'List.nil')
            named(value, erased[-1:], context, (action,))
            _, _, body, local = telescope(value, recorded[-1], context)
            events = joint.app(value, body, OWNED + 'Caller.ProtocolTrace.Recorded.events')
            captured = joint.app(value, events[-1], 'Prod.snd')
            actual = local_call(value, captured[-1], local, action)
            named(value, actual[:1], local, ('world',))
            joint.app(value, actual[-1], 'List.nil')
        for premise, action in (('leftMarked', 'left'), ('rightMarked', 'right')):
            term, context = fields[premise]
            named(value, joint.app(value, term, TRACE + 'Begins')[-1:], context, (action,))
    memory_path = ('Compiler.Extraction.Memory.Arguments.Normalization.Session.memory', OWNED + 'World.memory')
    for theorem in (MEMORY + 'allocate_same_cursors', TRACE + 'admitted_allocate'):
        value = statements[theorem]
        fields, _, _, _ = telescope(value)
        for premise, world in (('valid', 'state' if theorem.startswith(MEMORY) else 'before'), ('otherValid', 'other')):
            term, context = fields[premise]
            equal = joint.app(value, term, 'Eq')
            named(value, equal[-1:], context, ('Bool.true',))
            path = (MEMORY + 'State.valid',) + (() if theorem.startswith(MEMORY) else memory_path)
            joint.path(value, equal[-2], context, path, world)
    value = statements[TRACE + 'admitted_identity']
    _, _, root, context = telescope(value)
    conjunction = joint.app(value, root, 'And')
    for term, cursor in zip(conjunction, ('nextId', 'nextAddress')):
        equality = joint.app(value, term, 'Eq')
        for side, world in zip(equality[-2:], ('before', 'other')):
            joint.path(value, side, context, (MEMORY + 'State.' + cursor,) + memory_path, world)
    value = definitions[TRACE + 'entry']['value']
    _, _, root, context = telescope(value)
    entry = joint.app(value, root, 'Compiler.Extraction.Interner.InvocationTrace.Event.nativeEntry')
    for term, cursor in zip(entry[-2:], ('nextId', 'nextAddress')):
        joint.path(value, term, context, (MEMORY + 'State.' + cursor,
            'Compiler.Extraction.Memory.Arguments.Normalization.Session.memory', OWNED + 'World.memory'), 'before')
    value = definitions[TRACE + 'Marked.mk']['type']
    fields, _, _, _ = telescope(value)
    routes = {'operation': 'operation', 'constant': 'constant', 'materialize': 'materialize',
              'borrowed': 'borrowedOperation', 'namedLocal': 'localOperation'}
    if set(fields) != {'σ', 'captured'} | routes.keys():
        raise ValueError('native allocation capture lost a constructor entry')
    for field, route in routes.items():
        args, _, root, context = telescope(value, *fields[field])
        marked = joint.app(value, root, TRACE + 'Begins')
        selected = joint.app(value, marked[-1], 'Compiler.Extraction.Associative.Constructors.' + route)
        named(value, selected[2:], context, ('captured', *args))

    value = definitions[TRACE + 'unfold']['value']
    # The compiled recursive step must use the actual native child family and
    # the immediate smaller *marked* capture from its course-of-values tuple.
    step, context = choice.one_call(value, value['root'], [], TRACE + 'step')
    named(value, step[:9], context, ('σ', 'ops', 'allocate', 'safety', 'owner', 'meaning', 'base', 'growth', 'usizeBits'))
    recursive_children(value, step[-2], context, False)
    observed = joint.app(value, step[-1], NS + 'ProtocolTrace.observe')
    lower = value['nodes'][observed[-1]]
    if lower[:3] != ['projection', 'PProd', '0'] or value['nodes'][lower[3]] != ['bound', '0']:
        raise ValueError('recursive capture no longer observes its immediate marked child')
    joint.app(value, telescope(value)[2], 'Nat.brecOn')
    for name in ('allocate_same_cursors', 'admitted_allocate'):
        value = statements[(MEMORY if name == 'allocate_same_cursors' else TRACE) + name]
        _, _, root, context = telescope(value)
        equality = joint.app(value, root, 'Eq')
        for term, world in zip(equality[-2:], ('state' if name == 'allocate_same_cursors' else 'before', 'other')):
            mapped = joint.app(value, term, 'Except.map')
            allocated = joint.app(value, mapped[-1], MEMORY + 'allocate')
            named(value, allocated[-1:], context, ('child',))
            if name == 'allocate_same_cursors':
                named(value, allocated[-2:-1], context, (world,))
            else:
                joint.path(value, allocated[-2], context,
                    ('Compiler.Extraction.Memory.Arguments.Normalization.Session.memory', OWNED + 'World.memory'), world)
            _, _, result, local = telescope(value, mapped[-2], context)
            pair = joint.app(value, result, 'Prod.mk')
            joint.path(value, pair[-2], local, ('Prod.fst',), 'result')
            cursors = joint.app(value, pair[-1], 'Prod.mk')
            for item, cursor in zip(cursors[-2:], ('nextId', 'nextAddress')):
                joint.path(value, item, local, (MEMORY + 'State.' + cursor, 'Prod.snd'), 'result')
    checkpoint = audit_checkpoint(statements, definitions)
    caller = audit_checkpoint_miss(statements, definitions)
    return {'noReturnedGraphOrSuccessPremise': True, 'sameActualStreamAndCapture': True,
            'bothNativeAllocationCursorsRecorded': True, 'allFiveNativeEntriesMarked': True,
            'recursiveObserverUsesImmediateMarkedChild': True, 'sameActualAllocatorIncludingFailures': True,
            'checkpoint': checkpoint,
            'caller': caller, 'allSelectedMissBranchesConsumed': True,
            'completeStreamCorrespondenceVerified': False,
            'composedProductionTheoremVerified': False}


def audit_checkpoint(statements, definitions):
    value = definitions[TRACE + 'insertionEntry']['value']
    _, _, root, context = telescope(value)
    call = joint.app(value, root, 'Compiler.Extraction.Interner.InvocationTrace.Event.nativeInsertion')
    for term, cursor in zip(call[-2:], ('nextId', 'nextAddress')):
        joint.path(value, term, context, (MEMORY + 'State.' + cursor,
            'Compiler.Extraction.Memory.Arguments.Normalization.Session.memory', OWNED + 'World.memory'), 'before')
    value = definitions[TRACE + 'graphObservations']['value']
    original, context = choice.one_call(value, value['root'], [], OWNED + 'Caller.ProtocolTrace.Native.graphObservations')
    named(value, original[1:], context, ('ops', 'allocate', 'safety', 'owner', 'meaning', 'base', 'growth',
        'usizeBits', 'children', 'observations', 'debug', 'source', 'address', 'input'))
    _, _, root, context = telescope(value)
    ports = joint.app(value, root, OWNED + 'Caller.ProtocolTrace.GraphObservations.mk')
    for term, field in zip(ports[-3:-1], ('simplify', 'publish')):
        joint.path(value, term, context, (OWNED + 'Caller.ProtocolTrace.GraphObservations.' + field,), 'original')
    _, _, root, context = telescope(value, ports[-1], context)
    events = joint.app(value, root, 'List.cons')
    named(value, joint.app(value, events[-2], TRACE + 'insertionEntry')[-1:], context, ('before',))
    original = joint.app(value, events[-1], OWNED + 'Caller.ProtocolTrace.GraphObservations.insert')
    named(value, original[-5:], context, ('original', 'key', 'slice', 'deterministic', 'before'))

    value = definitions[TRACE + 'step']['value']
    _, _, root, context = telescope(value)
    step = joint.app(value, root, NS + 'ProtocolTrace.stepWith')
    named(value, step[1:-1], context, ('ops', 'allocate', 'safety', 'owner', 'meaning', 'base', 'growth', 'usizeBits', 'children'))
    ports = joint.app(value, step[-1], TRACE + 'graphObservations')
    named(value, ports[1:], context, ('ops', 'allocate', 'safety', 'owner', 'meaning', 'base', 'growth', 'usizeBits', 'children', 'observations'))
    value = definitions[NS + 'ProtocolTrace.stepWith']['value']
    wrapped, context = choice.one_call(value, value['root'], [], CAPTURE + 'constructors')
    named(value, local_call(value, wrapped[-1], context, 'ports'), context, ('debug',))

    value = definitions[TRACE + 'insertionReplay']['value']
    fields, _, _, _ = telescope(value)
    if set(fields) != {'input', 'normalized', 'meaning', 'key', 'deterministic', 'stream', 'mismatch'}:
        raise ValueError('checkpoint model takes a native identity or completed result')
    constants = gate.step.constants_below(value, value['root'])
    if constants & {OWNED + 'Insertion.Native.' + n for n in ('execution', 'recordExecution', 'observedCandidate', 'insert')}:
        raise ValueError('checkpoint model consults native execution')
    read, context = choice.one_call(value, value['root'], [], TRACE + 'insertionRead')
    named(value, read, context, ('stream',))
    replay, context = choice.one_call(value, value['root'], [], OWNED + 'Insertion.Native.allocationReplay')
    named(value, replay[:5], context, ('input', 'key', 'normalized', 'meaning', 'deterministic'))
    joint.path(value, replay[5], context, ('Prod.fst',), 'ids')
    named(value, joint.app(value, replay[6], 'Compiler.Extraction.Interner.InvocationTrace.insertions')[-1:], context, ('stream',))
    named(value, replay[7:], context, ('mismatch',))
    for name in (TRACE + 'insertion_replayed', NS + 'CallFrame.insertion_checkpoint_stream', NS + 'CallFrame.insertion_checkpoint_agrees'):
        fields, _, _, _ = telescope(statements[name])
        if set(fields) & {'identity', 'candidate', 'binding', 'model', 'projected', 'safe'}:
            raise ValueError('checkpoint proof assumes native identity or final correspondence: ' + name)
    value = statements[NS + 'CallFrame.insertion_checkpoint_agrees']
    fields, _, _, _ = telescope(value)
    for premise, world in (('insideLeft', 'left'), ('insideRight', 'right')):
        term, context = fields[premise]
        prefix = joint.app(value, term, 'List.IsPrefix')
        named(value, prefix[-1:], context, ('stream',))
        appended = joint.app(value, prefix[-2], 'HAppend.hAppend')
        named(value, appended[-2:-1], context, ('leading',))
        called = joint.app(value, appended[-1], OWNED + 'Caller.ProtocolTrace.GraphObservations.insert')
        named(value, called[-4:], context, ('key', 'normalized', 'deterministic', world))
        joint.app(value, called[-5], TRACE + 'graphObservations')
    return {'actualReachedInsertionCursors': True, 'sharedConstructorRecorder': True,
            'oneStreamModelWithoutNativeIdentityParameter': True, 'ordinaryAgreementWithoutIdentityPremise': True,
            'completeBodyReplayVerified': False, 'nativeAdmissionDerived': False}


def audit_checkpoint_miss(statements, definitions):
    caller = OWNED + 'Caller.ProtocolTrace.'
    value = definitions[TRACE + 'graphReplay']['value']
    fields, _, _, _ = telescope(value)
    if set(fields) != {'seed', 'input', 'normalized', 'meaning', 'stream', 'mismatch'}:
        raise ValueError('caller checkpoint model gained a native result parameter')
    replay, context = choice.one_call(value, value['root'], [], TRACE + 'insertionReplay')
    named(value, replay, context, ('input', 'normalized', 'meaning', 'key', 'deterministic', 'stream', 'mismatch'))
    published, context = choice.one_call(value, value['root'], [], 'Compiler.Extraction.Interner.InvocationTrace.publish')
    named(value, published[-1:], context, ('stream',))

    audit_checkpoint_caller(statements[caller + 'Native.checkpoint_insert_miss'], False)
    audit_checkpoint_caller(statements[caller + 'Native.checkpoint_miss'], True)
    return {'fixedStreamCheckpointModel': True, 'actualRecordedBodyAndClose': True,
            'sharedSelectedInsertionRecorder': True, 'completeBodyReplayVerified': False,
            'dispatcherProjectionAndReachedFrameDerived': False, 'nativeAdmissionDerived': False}


def audit_checkpoint_caller(value, complete):
    caller = OWNED + 'Caller.ProtocolTrace.'
    fields, lets, root, context = telescope(value)
    expected = {'σ', 'ops', 'allocate', 'safety', 'owner', 'meaning', 'base', 'growth', 'usizeBits', 'children',
                'observations', 'debug', 'source', 'buffer', 'address', 'input', 'request', 'key', 'slice',
                'deterministic', 'before', 'handle', 'lookup', 'model', 'seed', 'values', 'rows', 'parent',
                'leading', 'stream', 'mismatch', 'admitted', 'detached', 'unowned', 'caller',
                '_chosen', '_frame', '_inside', '_selected', '_reached', '_completed'}
    if complete:
        expected = expected - {'_chosen'} | {'aligned'}
    if set(fields) != expected:
        raise ValueError('checkpoint caller changed its native/dispatcher premises')
    ports = joint.app(value, lets['ports'][0], TRACE + 'graphObservations')
    named(value, ports[1:], lets['ports'][1], ('ops', 'allocate', 'safety', 'owner', 'meaning', 'base', 'growth',
        'usizeBits', 'children', 'observations', 'debug', 'source', 'address', 'input'))
    model = joint.app(value, lets['logicalModel'][0], NS + 'dispatchModel')
    named(value, model[-3:], lets['logicalModel'][1], ('model', 'usizeBits', 'debug'))
    replay = joint.app(value, model[-4], TRACE + 'graphReplay')
    named(value, replay, lets['logicalModel'][1], ('seed', 'input', 'slice', 'meaning', 'stream', 'mismatch'))
    decision = joint.app(value, lets['decision'][0], OWNED + 'MissStream.selected')
    named(value, decision[-6:], lets['decision'][1], ('p', 'request', 'key', 'slice', 'deterministic', 'before'))
    from native_resource_miss_checks import appended
    history_name = 'history' if complete else 'closeLeading'
    history = appended(value, lets[history_name][0])
    if len(history) != (4 if complete else 3):
        raise ValueError('checkpoint caller lost its source-order history')
    named(value, history[:2], lets[history_name][1], ('leading', 'middle'))
    if complete:
        named(value, history[2:3], lets[history_name][1], ('bodyEvents',))
        joint.path(value, history[-1], lets[history_name][1], (OWNED + 'MissStream.Segment.cleanup',), 'observed')
        inserted, local = choice.one_call(value, lets['bodyEvents'][0], lets['bodyEvents'][1], caller + 'GraphObservations.insert')
    else:
        inserted = joint.app(value, history[-1], caller + 'GraphObservations.insert')
        local = lets[history_name][1]
    named(value, inserted[-5:-1], local, ('ports', 'key', 'slice', 'deterministic'))
    joint.path(value, inserted[-1], local, ('Prod.snd',), 'decision')
    term, scope = fields['_inside']
    named(value, joint.app(value, term, 'List.IsPrefix')[-2:], scope, (history_name, 'stream'))
    term, scope = fields['_frame']
    if complete:
        conditions, _, term, scope = telescope(value, term, scope)
        if len(conditions) != 1:
            raise ValueError('complete miss changed its ordinary reached-frame guard')
        guard, local = next(iter(conditions.values()))
        guard = joint.app(value, guard, 'Eq')
        named(value, guard[-1:], local, ('Bool.true',))
        joint.path(value, joint.app(value, guard[-2], OWNED + 'ordinary')[-1], local, ('Prod.fst',), 'decision')
    frame = joint.app(value, term, NS + 'CallFrame')
    named(value, frame[-8:-1], scope, ('rows', 'source', 'values', 'slice', 'address', 'input', 'parent'))
    joint.path(value, frame[-1], scope, ('Prod.snd',), 'decision')
    term, scope = fields['_completed']
    completed = joint.app(value, term, 'Eq')
    named(value, completed[-1:], scope, ('Bool.true',))
    joint.path(value, joint.app(value, completed[-2], OWNED + 'ordinary')[-1], scope, ('Prod.fst',), 'body')
    body = joint.app(value, lets['body'][0], caller + 'missBody')
    named(value, body[-7:-6], lets['body'][1], ('ports',))
    named(value, body[-6:], lets['body'][1], ('source', 'buffer', 'request', 'key', 'deterministic', 'initialRecord'))
    logical = joint.app(value, lets['logical'][0], 'Compiler.Extraction.Interner.FindCode.controlMiss')
    named(value, logical[-6:-5], lets['logical'][1], ('Compiler.Extraction.Interner.findCode',))
    execution = joint.app(value, logical[-5], 'Compiler.Extraction.Interner.Scoped.execution')
    named(value, execution[-2:], lets['logical'][1], ('resources', 'logicalModel'))
    named(value, logical[-4:-1], lets['logical'][1], ('request', 'key', 'deterministic'))
    named(value, joint.app(value, logical[-1], caller + 'scopeView')[-1:], lets['logical'][1], ('initialRecord',))
    actual = joint.app(value, lets['actual'][0], caller + 'finish')
    for term, member in zip(actual[-2:], ('Prod.fst', 'Prod.snd')):
        joint.path(value, term, lets['actual'][1], (member,), 'body')
    # Audit both body and completed caller projections, including the scoped
    # close and the exact consumed history; replay of insertion alone is weaker.
    conclusions = []
    for _ in range(3):
        first, root = joint.app(value, root, 'And')
        conclusions.append(first)
    conclusions.append(root)
    for index, world in enumerate(('body', 'actual')):
        equation = joint.app(value, conclusions[index], 'Eq')
        left, right = [joint.app(value, term, 'Prod.mk') for term in equation[-2:]]
        joint.path(value, left[-2], context, ('Prod.fst',), world)
        joint.path(value, left[-1], context, (caller + 'scopeView', 'Prod.snd'), world)
        mapped = joint.app(value, right[-2], 'Except.mapError')
        joint.path(value, mapped[-1], context, ('Prod.fst',), 'logical')
        reached = right[-1]
        if index:
            closed = joint.app(value, reached, 'Compiler.Extraction.Interner.Scoped.close')
            named(value, closed[-2:-1], context, ('resources',))
            reached = closed[-1]
        joint.path(value, reached, context, ('Prod.snd',), 'logical')
    equation = joint.app(value, conclusions[2], 'Eq')
    joint.path(value, equation[-2], context, (caller + 'Recorded.events', 'Prod.snd'), 'actual')
    named(value, equation[-1:], context, (history_name,))
    equation = joint.app(value, conclusions[3], 'Eq')
    joint.path(value, equation[-2], context, (caller + 'Tokens.incomplete', caller + 'Recorded.tokens', 'Prod.snd'), 'actual')
    named(value, equation[-1:], context, ('Bool.false',))



def controls(output, env, lean):
    code = source('Compiler.Extraction.InternerNativeAllocationTrace')
    changes = (
        ('wrong-id', '.nativeEntry before.memory.memory.nextId before.memory.memory.nextAddress',
         '.nativeEntry (before.memory.memory.nextId + 1) before.memory.memory.nextAddress', 1),
        ('wrong-address', '.nativeEntry before.memory.memory.nextId before.memory.memory.nextAddress',
         '.nativeEntry before.memory.memory.nextId (before.memory.memory.nextAddress + 1)', 1),
        ('missing-entry', 'action before (leading ++ [entry before])', 'action before leading', 1),
        ('rewind-history', 'action before (leading ++ [entry before])', 'action before [entry before]', 1),
        ('wrong-entry-position', 'stream[(ChildTrace.history before).length]?', 'stream[(ChildTrace.history before).length + 1]?', 1),
        ('different-position', '(position : (ChildTrace.history before).length = (ChildTrace.history other).length)',
         '(position : (ChildTrace.history before).length + 1 = (ChildTrace.history other).length)', 1),
        ('different-stream', '(rightAdmitted : Resource.Admitted ChildTrace.history stream',
         '(rightAdmitted : Resource.Admitted ChildTrace.history (stream.reverse)', 2),
        ('missing-consumption', 'allocationCursor := before.allocationCursor + 1', 'allocationCursor := before.allocationCursor', 1),
        ('wrong-child-type', '(Compiler.ZigAir.Memory.allocate other.memory.memory child).map',
         '(Compiler.ZigAir.Memory.allocate other.memory.memory (.array 0 child)).map', 1),
    )
    records = checked_controls(output, [mutation_check(output, 'native-allocation-trace-unchanged', code, True, env, lean)])
    for name, old, new, count in changes:
        if code.count(old) != count:
            raise ValueError('ambiguous native allocation control: ' + name)
        records += checked_controls(output, [mutation_check(output, 'native-allocation-trace-' + name,
            code.replace(old, new), False, env, lean)])
    memory = source('Compiler.ZigAir.MemoryAllocationLaws')
    records += checked_controls(output, [mutation_check(output, 'native-allocation-cursors-unchanged', memory, True, env, lean)])
    for name, old, new in (
        ('invalid-left', '(valid : state.valid = true) (otherValid : other.valid = true)',
         '(valid : state.valid = false) (otherValid : other.valid = true)'),
        ('invalid-right', '(valid : state.valid = true) (otherValid : other.valid = true)',
         '(valid : state.valid = true) (otherValid : other.valid = false)'),
        ('different-id', '(identity : state.nextId = other.nextId)', '(identity : state.nextId + 1 = other.nextId)'),
        ('different-address', '(address : state.nextAddress = other.nextAddress)',
         '(address : state.nextAddress = other.nextAddress + 1)'),
    ):
        if memory.count(old) != 1:
            raise ValueError('ambiguous native allocation cursor control: ' + name)
        records += checked_controls(output, [mutation_check(output, 'native-allocation-cursors-' + name,
            memory.replace(old, new), False, env, lean)])
    tests = source('Compiler.Extraction.InternerNativeAllocationTraceTests')
    checkpoint = source('Compiler.Extraction.InternerInsertionCheckpoint')
    records += checked_controls(output, [mutation_check(output, 'native-insertion-checkpoint-unchanged', checkpoint, True, env, lean)])
    for name, old, new, count in (
        ('wrong-kind', 'some (.nativeInsertion id address)', 'some (.nativeEntry id address)', 1),
        ('skip-checkpoint', 'allocationCursor := before.allocationCursor + 1', 'allocationCursor := before.allocationCursor', 1),
        ('wrong-identity', 'deterministic ids.1 (insertions stream)', 'deterministic (ids.1 + 1) (insertions stream)', 1),
        ('wrong-stream', 'ids.1 (insertions stream)', 'ids.1 (insertions ([] : List ProtocolEvent))', 1),
        ('wrong-ending-cursor', 'leading.length + 1 + captured.2.events.length', 'leading.length + 2 + captured.2.events.length', 1),
        ('different-admitted-stream', 'deterministic right <+: stream)', 'deterministic right <+: stream.reverse)', 1),
    ):
        if checkpoint.count(old) != count:
            raise ValueError('ambiguous insertion checkpoint control: ' + name)
        records += checked_controls(output, [mutation_check(output, 'native-insertion-checkpoint-' + name,
            checkpoint.replace(old, new), False, env, lean)])
    records += checked_controls(output, [mutation_check(output, 'native-allocation-trace-regression', tests, True, env, lean)])
    # Only this control needs the actual nested fixture. The others exercise
    # general statements without repeatedly evaluating native initialization.
    imports = '\n'.join(dict.fromkeys(line for line in (code + '\n' + checkpoint + '\n' + tests).splitlines()
        if line.startswith('import ') and line not in ('import Compiler.Extraction.InternerNativeAllocationTrace',
            'import Compiler.Extraction.InternerInsertionCheckpoint')))
    combined = imports + '\n' + without_imports(code) + '\n' + without_imports(checkpoint) + '\n' + without_imports(tests)
    records += checked_controls(output, [mutation_check(output, 'native-allocation-trace-nested-unchanged', combined, True, env, lean)])
    old = '(ProtocolTrace.observe (unfold depth))'
    if combined.count(old) != 1:
        raise ValueError('ambiguous nested allocation observer')
    changed = combined.replace(old,
        '(ProtocolTrace.observe (ProtocolTrace.unfold ops allocate safety owner meaning base growth usizeBits depth))')
    records += checked_controls(output, [mutation_check(output, 'native-allocation-trace-missing-nested-entry', changed, False, env, lean)])
    old = 'insertionEntry before :: original.insert key slice deterministic before'
    if combined.count(old) != 1:
        raise ValueError('ambiguous reached insertion observation')
    records += checked_controls(output, [mutation_check(output, 'native-allocation-trace-missing-insertion-checkpoint',
        combined.replace(old, 'original.insert key slice deterministic before'), False, env, lean)])
    miss = source('Compiler.Extraction.InternerInsertionCheckpointMiss')
    records += checked_controls(output, [mutation_check(output, 'native-checkpoint-miss-unchanged', miss, True, env, lean)])
    for name, old, new in (
        ('wrong-stream', 'key deterministic stream mismatch }', 'key deterministic stream.reverse mismatch }'),
        ('wrong-source', 'insertionReplay input normalized meaning', 'insertionReplay { input with item := { input.item with data := 0 } } normalized meaning'),
        ('missing-checkpoint-history', 'actual.2.events = closeLeading', 'actual.2.events = leading ++ middle'),
        ('unclosed-scope', 'Interner.Scoped.close resources logical.2) ∧', 'logical.2) ∧'),
        ('wrong-admission', '(_inside : closeLeading <+: stream)', '(_inside : closeLeading <+: stream.reverse)'),
        ('rewound-decision', 'allocationCursor := (leading ++ middle).length } = logicalDecision.2',
         'allocationCursor := leading.length } = logicalDecision.2'),
    ):
        if miss.count(old) != 1:
            raise ValueError('ambiguous checkpoint caller control: ' + name)
        records += checked_controls(output, [mutation_check(output, 'native-checkpoint-miss-' + name,
            miss.replace(old, new), False, env, lean)])
    complete = source('Compiler.Extraction.InternerCheckpointCallerReplay')
    records += checked_controls(output, [mutation_check(output, 'native-checkpoint-complete-miss-unchanged', complete, True, env, lean)])
    for name, old, new in (
        ('lost-cleanup-history', 'actual.2.events = history', 'actual.2.events = leading ++ middle ++ bodyEvents'),
        ('unclosed-scope', 'Interner.Scoped.close resources logical.2) ∧', 'logical.2) ∧'),
        ('wrong-admission', '(_inside : history <+: stream)', '(_inside : history <+: stream.reverse)'),
        ('lost-publication-history', '| _ => observed.body', '| _ => []'),
        ('wrong-source', 'AllocationTrace.graphReplay seed input slice meaning stream mismatch',
         'AllocationTrace.graphReplay seed { input with item := { input.item with data := 0 } } slice meaning stream mismatch'),
        ('rewound-decision', 'allocationCursor := (leading ++ middle).length } = logicalDecision.2',
         'allocationCursor := leading.length } = logicalDecision.2'),
    ):
        if complete.count(old) != 1:
            raise ValueError('ambiguous complete checkpoint miss control: ' + name)
        records += checked_controls(output, [mutation_check(output, 'native-checkpoint-complete-miss-' + name,
            complete.replace(old, new), False, env, lean)])
    imports = '\n'.join(dict.fromkeys(line for line in (miss + '\n' + complete).splitlines()
        if line.startswith('import ') and line != 'import Compiler.Extraction.InternerInsertionCheckpointMiss'))
    combined = imports + '\n' + without_imports(miss) + '\n' + without_imports(complete)
    records += checked_controls(output, [mutation_check(output, 'native-checkpoint-complete-model-unchanged', combined, True, env, lean)])
    old = 'publish := Interner.InvocationTrace.publish stream'
    if combined.count(old) != 1:
        raise ValueError('ambiguous complete checkpoint publication port')
    records += checked_controls(output, [mutation_check(output, 'native-checkpoint-complete-model-wrong-publication',
        combined.replace(old, old + '.reverse'), False, env, lean)])
    for label, module, old in (
        ('scoped', 'InternerMissReplay', 'else (.ok none, before.heap)).1 ≠ .ok none'),
        ('recorded', 'InternerCallerProtocolMiss', 'deterministic before.native.world).1 ≠ .ok none'),
    ):
        code = source('Compiler.Extraction.' + module)
        if code.count(old) != 1:
            raise ValueError('ambiguous non-insertion guard: ' + label)
        records += checked_controls(output, [mutation_check(output, 'native-checkpoint-irrelevant-' + label + '-unchanged', code, True, env, lean)])
        records += checked_controls(output, [mutation_check(output, 'native-checkpoint-irrelevant-' + label + '-wrong-guard',
            code.replace(old, old.replace('≠ .ok none', '≠ .ok (some 0)')), False, env, lean)])
    return records
