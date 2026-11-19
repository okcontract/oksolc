"""Audit one recorded/native item proof under shared reached-miss witnesses.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import guarded_induction_checks as guarded
from assembly_item_creation_checks import checked_controls
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NS, OWNED = gate.NS, gate.OWNED
TRACE = OWNED + 'Caller.ProtocolTrace.'
PNS = OWNED + 'ConstructorItem.ProtocolTrace.'
MODULE = 'Compiler.Extraction.InternerConstructorJointInduction'
CLAIMS = [PNS + name for name in ('takenPrefix_tokens', 'JointEntry.native_frames', 'JointEntry.recorded',
                                 'item_joint_verified', 'item_induction_projected')]
CLAIMS += [TRACE + 'Native.entry_continuation']
CLAIMS += guarded.CLAIMS
INTERFACES = tuple(PNS + name for name in ('TakenModel', 'replayModel', 'JointEntry.mk', 'takenPrefix', 'EntryProjected')) + guarded.INTERFACES
PARAMETERS = {'σ', 'ops', 'allocate', 'safety', 'owner', 'usizeBits', 'base', 'growth', 'children',
              'observations', 'env', 'other', 'debug', 'source', 'request', 'rows', 'parent'}


def app(value, root, name):
    head, args = gate.applied(value, root)
    if head[:2] != ['const', name]:
        raise ValueError('joint proof changed a compiled operation: ' + name)
    return args


def path(value, root, context, names, variable):
    for name in names:
        root = app(value, root, name)[-1]
    if gate.named(value, root, context) != variable:
        raise ValueError('joint proof rebound a native observation: ' + variable)


def audit_binding(value, guard):
    fields, root, context = gate.domains(value)
    expected = PARAMETERS | {'address', 'key', 'normalized', 'remaining', 'deterministic',
                             'recorded', 'model', 'trailing', 'token'}
    if set(list(fields)[:-1]) != expected or len(fields) != len(expected) + 1:
        raise ValueError('joint miss added a premise or lost an actual input')
    tokens, local = list(fields.values())[-1]
    equality = app(value, tokens, 'Eq')
    path(value, equality[-2], local, (TRACE + 'Recorded.tokens',), 'recorded')
    state = app(value, equality[-1], TRACE + 'Tokens.mk')
    scope = app(value, state[-2], 'Compiler.Extraction.Interner.Scoped.Scope.mk')
    path(value, scope[-3], local, ('Option.some',), 'token')
    path(value, scope[-2], local, (OWNED.removesuffix('OwnedCall.') + 'Handle.values',), 'remaining')
    if gate.named(value, scope[-1], local) != 'Compiler.Extraction.Cache.NormalizationOwnership.Exit.cleanup':
        raise ValueError('joint miss lost its reached take phase')
    if gate.named(value, state[-1], local) != 'Bool.false':
        raise ValueError('joint miss allows an incomplete prefix')
    for name in ('childModel', 'seed', 'mismatch'):
        args = app(value, root, 'Exists')
        node = value['nodes'][args[-1]]
        if node[:2] != ['lambda', name]:
            raise ValueError('joint miss lost its shared witness: ' + name)
        context += [name]
        root = node[4]
    lets, conjuncts = {}, []
    while True:
        while value['nodes'][root][0] == 'let':
            node = value['nodes'][root]
            lets[node[1]] = (node[3], context[:])
            context += [node[1]]
            root = node[4]
        head, args = gate.applied(value, root)
        if head[:2] != ['const', 'And']:
            break
        conjuncts.append((args[0], context[:]))
        root = args[1]
    if len(conjuncts) != 5 or set(lets) != {'child', 'cursor'}:
        raise ValueError('joint miss added a premise or changed replay construction')
    child, local = lets['child']
    args = app(value, child, NS + 'ChildTrace.constructors')
    if [gate.named(value, x, local) for x in args[-2:]] != ['children', 'observations']:
        raise ValueError('joint miss replaced its actual children or observations')
    cursor, local = lets['cursor']
    args = app(value, cursor, OWNED + 'MissStream.childCursor')
    path(value, args[-2], local, ('List.length', TRACE + 'Recorded.events'), 'recorded')
    path(value, args[-1], local, (OWNED + 'State.world', TRACE + 'Recorded.native'), 'recorded')
    coupled, local = conjuncts[0]
    coupled, local = guarded.guarded_body(value, coupled, local, guard)
    node = value['nodes'][coupled]
    if node[:2] != ['forall', 'rows']:
        raise ValueError('joint correspondence lost arbitrary reached rows')
    args = app(value, node[4], 'Compiler.Extraction.Dispatch.Effects.SourceConstructorsAt')
    local += ['rows']
    if [gate.named(value, x, local) for x in args[-2:]] != ['child', 'childModel']:
        raise ValueError('joint correspondence replaced the shared child model')
    if gate.named(value, args[-3], local) != 'debug':
        raise ValueError('joint child relation lost its actual debug value')
    read = app(value, args[-4], 'Compiler.Extraction.Nested.storageReads')
    if gate.named(value, read[-1], local) != 'rows':
        raise ValueError('joint child relation lost its actual source rows')
    effects = app(value, args[-5], OWNED + 'Recursive.projectionAt')
    cursor_args = app(value, effects[-2], OWNED + 'Recursive.cursorGraph')
    if gate.named(value, cursor_args[-1], local) != 'cursor':
        raise ValueError('joint child relation lost the recorded cursor')
    app(value, effects[-1], NS + 'CallFrame')
    app(value, conjuncts[1][0], NS + 'MissFrames')
    for (condition, local), constructor in zip(conjuncts[2:], (
        'Compiler.Extraction.Associative.ConstructorSound',
        'Compiler.Extraction.AddressMask.Constructs', 'Compiler.Extraction.ArithmeticShift.Constructs')):
        body, local = guarded.guarded_body(value, condition, local, guard)
        args = app(value, body, constructor)
        target = args[-1]
        if constructor.endswith('ConstructorSound'):
            if gate.named(value, target, local) != 'childModel':
                raise ValueError('joint child word proof uses a different model')
        else:
            path(value, target, local, ('Compiler.Extraction.Associative.Constructors.operation',), 'childModel')
    args = app(value, root, 'Eq')
    if gate.named(value, args[-2], context) != 'model':
        raise ValueError('joint miss does not bind the fixed entry model')
    replay = app(value, args[-1], PNS + 'replayModel')
    expected = ['σ', 'ops', 'allocate', 'safety', 'owner', 'usizeBits', 'base', 'growth', 'children', 'observations',
                'env', 'other', 'debug', 'source', 'request', 'address', 'key', 'normalized', 'remaining', 'deterministic',
                'recorded', 'token', 'trailing', 'seed', 'childModel', 'mismatch']
    if [gate.named(value, x, context) for x in replay] != expected:
        raise ValueError('joint miss rebound the actual replay construction')


def audit_replay(value):
    fields, root, context = gate.domains(value)
    expected = (PARAMETERS - {'rows', 'parent'}) | {'address', 'key', 'normalized', 'remaining', 'deterministic',
        'recorded', 'token', 'trailing', 'seed', 'childModel', 'mismatch'}
    if set(fields) != expected:
        raise ValueError('joint replay changed its construction inputs')
    lets, index, local = {}, value['root'], []
    while value['nodes'][index][0] in ('lambda', 'let'):
        node = value['nodes'][index]
        if node[0] == 'let':
            lets[node[1]] = (node[3], local[:])
        local += [node[1]]
        index = node[4]
    if set(lets) != {'child', 'middle', 'observed', 'events'}:
        raise ValueError('joint replay changed its observed segments')
    child, local = lets['child']
    args = app(value, child, NS + 'ChildTrace.constructors')
    if [gate.named(value, x, local) for x in args[-2:]] != ['children', 'observations']:
        raise ValueError('joint replay replaced its native children')
    middle, local = lets['middle']
    args = app(value, middle, TRACE + 'Native.middle')
    path(value, args[-1], local, (OWNED + 'State.world', TRACE + 'Recorded.native'), 'recorded')
    dispatch = app(value, root, NS + 'dispatchModel')
    if [gate.named(value, x, context) for x in dispatch[-3:]] != ['childModel', 'usizeBits', 'debug']:
        raise ValueError('joint replay replaced its child model or dispatcher inputs')
    replay = app(value, dispatch[-4], OWNED + 'MissStream.replay')
    if [gate.named(value, replay[i], context) for i in (-4, -3, -1)] != ['seed', 'events', 'mismatch']:
        raise ValueError('joint replay changed its bound stream or seed')
    path(value, replay[-2], context, (OWNED + 'MissStream.Segment.candidate',), 'observed')
    observed, local = lets['observed']
    segment = app(value, observed, OWNED + 'MissStream.segment')
    if [gate.named(value, x, local) for x in segment[-2:]] != ['remaining', 'token']:
        raise ValueError('joint suffix replaced its actual owner or take token')
    path(value, segment[-3], local, (OWNED + 'State.world', TRACE + 'Recorded.native'), 'recorded')
    def leaves(index):
        head, args = gate.applied(value, index)
        if head[:2] in (['const', 'HAppend.hAppend'], ['const', 'List.append']):
            return leaves(args[-2]) + leaves(args[-1])
        return [index]
    events, local = lets['events']
    parts = leaves(events)
    if len(parts) != 5:
        raise ValueError('joint resource stream lost an observed segment')
    path(value, parts[0], local, (TRACE + 'Recorded.events',), 'recorded')
    path(value, parts[2], local, (OWNED + 'MissStream.Segment.body',), 'observed')
    path(value, parts[3], local, (OWNED + 'MissStream.Segment.cleanup',), 'observed')
    if [gate.named(value, parts[i], local) for i in (1, 4)] != ['middle', 'trailing']:
        raise ValueError('joint resource stream changed child history or trailing events')


def audit_statements(rows, interfaces):
    statements = {row['theorem']: row['statement'] for row in rows}
    definitions = {row['name']: row for row in interfaces}
    forbidden = {PNS + 'EntryProjected', NS + 'InvocationPost', NS + 'ConstructorPost', OWNED + 'Semantic.Ensures',
                 OWNED + 'Recursive.ConstructorGoal', NS + 'MissWords', OWNED + 'Insertion.Native.CandidateWords'}
    joint = definitions[PNS + 'JointEntry.mk']['type']
    fields, _, _ = gate.domains(joint)
    expected_fields = PARAMETERS | {'model', 'before', 'leading', 'trailing', 'retained', 'localParent', 'taken'}
    if set(fields) != expected_fields:
        raise ValueError('joint entry added a premise or lost an existing field')
    for name, (root, _) in fields.items():
        if forbidden & gate.step.constants_below(joint, root):
            raise ValueError('joint entry assumes a final theorem: ' + name)
    needed = {gate.ITEM + 'prepare', 'Compiler.ZigAir.Memory.allocate', OWNED + 'Caller.initLookup', OWNED + 'take',
              'Compiler.Extraction.Interner.makeKey', OWNED + 'Insertion.Native.CallerInput', PNS + 'takenPrefix', PNS + 'TakenModel'}
    if not needed <= gate.step.constants_below(joint, fields['taken'][0]):
        raise ValueError('joint entry lost an actual prefix observation')
    guard = guarded.source_guard(interfaces)
    audit_binding(definitions[PNS + 'TakenModel']['value'], guard)
    audit_replay(definitions[PNS + 'replayModel']['value'])
    statement = statements[PNS + 'item_joint_verified']
    fields, conclusion, context = gate.domains(statement)
    expected_fields = PARAMETERS | {'model', 'before', 'leading', 'trailing', 'capacity', 'data', 'joint',
        'facts', 'represented', 'privateSource', 'array', 'admitted', 'domain', 'typed', 'capacityQuery',
        'classificationQuery', 'expected', 'valid', 'evaluated', 'pushes'}
    if set(fields) != expected_fields:
        raise ValueError('joint item added a premise or lost actual inputs or initial specification facts')
    for name, (root, _) in fields.items():
        if forbidden & gate.step.constants_below(statement, root):
            raise ValueError('joint item assumes its result: ' + name)
    left, right = app(statement, conclusion, 'And')
    projected = app(statement, left, PNS + 'EntryProjected')
    if gate.named(statement, projected[-1], context) != 'actual':
        raise ValueError('joint item projects a different execution')
    native = app(statement, right, NS + 'InvocationPost')
    pair = app(statement, native[-2], 'Prod.mk')
    path(statement, pair[-2], context, ('Prod.fst',), 'actual')
    path(statement, pair[-1], context, (TRACE + 'Recorded.native', 'Prod.snd'), 'actual')
    return {'guardedInduction': guarded.audit(rows, interfaces),
            'sharedReachedChildModel': True, 'recordedCursorAndSuffixBound': True, 'sameCapturedResultAndNativeState': True,
            'successfulEntryNotAssumed': True, 'nativeFrameLawsRequired': True,
            'recursiveInductionVerified': False, 'composedProductionTheoremVerified': False}


def audit(claims):
    required = {
        PNS + 'takenPrefix_tokens': {TRACE + 'initialized_taken_recorded'},
        PNS + 'JointEntry.native_frames': {PNS + 'takenPrefix_tokens', NS + 'EntryFrames'},
        PNS + 'JointEntry.recorded': {gate.ITEM + 'caller_input', NS + 'CallFrame.caller', OWNED + 'NativeGraph.Facts.frame'},
        PNS + 'item_joint_verified': {PNS + 'item_induction_projected', PNS + 'JointEntry.native_frames', PNS + 'JointEntry.recorded',
                                      NS + 'EntryFrames.native_verified', PNS + 'item_erases'},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('joint item lost shared reasoning: ' + name + ': ' + ', '.join(sorted(missing)))
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('joint item depends on a fixture: ' + name)
    return {'checkedDependencies': sorted(required), 'sharedRecordedAndNativeInductionData': True,
            'recursiveInductionVerified': False, 'composedProductionTheoremVerified': False}


def mutation_cases():
    raw = (gate.harness.ROOT / 'lean/Compiler/Extraction/InternerConstructorJointInduction.lean').read_text()
    source = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
    source += '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)
    changes = (
        ('wrong-take-phase', 'phase := .cleanup', 'phase := .lookup', 2),
        ('wrong-scratch-observation', 'source buffer request)', 'source ⟨0, 0, 0⟩ request)', 2),
        ('rewind-prefix-history', 'constructed memory leading).2 model trailing', 'constructed memory []).2 model trailing', 1),
        ('shift-child-cursor', 'childCursor recorded.events.length recorded.native.world', 'childCursor (recorded.events.length + 1) recorded.native.world', 1),
        ('unbind-entry-model', 'model = replayModel', 'seed = replayModel', 1),
        ('wrong-dispatch-width', 'childModel usizeBits debug', 'childModel (usizeBits + 1) debug', 1),
        ('duplicate-replay-stream', 'MissStream.replay seed events observed.candidate mismatch', 'MissStream.replay seed (events ++ events) observed.candidate mismatch', 1),
        ('lose-trailing-events', 'observed.body ++ observed.cleanup ++ trailing', 'observed.body ++ observed.cleanup', 1),
        ('wrong-child-guard', '((deterministic && (request.item.kind == 1)) = true →', '((!deterministic && (request.item.kind == 1)) = true →', 4),
        ('rewind-native-child-cursor', '⟨MissStream.childCursor events.length taken.world, childModel,', '⟨(fun _ => 0), childModel,', 1),
        ('invent-native-prefix', 'predicate, rows, mismatch, frame.2, frame.1', 'predicate, rows ++ rows, mismatch, frame.2, frame.1', 1),
        ('wrong-final-word', 'before.graph (actual.1, actual.2.native) expected := by', 'before.graph (actual.1, actual.2.native) (expected + 1) := by', 1),
        ('rewind-final-native-state', 'before.graph (actual.1, actual.2.native) expected := by', 'before.graph (actual.1, { actual.2.native with world := before }) expected := by', 1),
        ('wrong-projected-entry-graph', 'EntryProjected model request before.graph leading trailing actual ∧', 'EntryProjected model request { before.graph with table := fun _ => none } leading trailing actual ∧', 1),
    )
    return source, changes


def controls(output, env, lean):
    source, changes = mutation_cases()
    records = checked_controls(output, [mutation_check(output, 'joint-item-unchanged', source, True, env, lean)])
    for name, before, after, count in changes:
        if source.count(before) != count:
            raise ValueError('ambiguous joint item mutation: ' + name)
        records += checked_controls(output, [mutation_check(output, 'joint-item-' + name,
            source.replace(before, after), False, env, lean)])
    return records + guarded.controls(output, env, lean)
