"""Audit resource-aware initialization, fixed entry models and constructor return.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
import guarded_induction_checks as guarded
from native_miss_frame_checks import named, replace_names
from native_resource_admission_checks import telescope, local_call
from native_resource_miss_checks import appended
from native_algebraic_dispatch_checks import source
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check

CALLER = gate.OWNED + 'Caller.ProtocolTrace.'
NATIVE = CALLER + 'Native.'
ENTRY = NATIVE + 'ResourceEntry.'
ITEM = gate.ITEM + 'ProtocolTrace.'
CONSTRUCTOR = ITEM + 'ResourceEntry.'
CHILD = gate.NS + 'ChildTrace.'
MISS = gate.OWNED + 'MissStream.'
RESOURCE = gate.OWNED + 'Recursive.Resource.'
CLAIMS = [NATIVE + 'initialized_miss_projected']
CLAIMS += [ENTRY + name for name in ('source_of_projects', 'MissInduction.of_unrestricted',
                                    'EntryInduction.of_unrestricted', 'entry_continuation')]
ENTRIES = ('borrowed', 'constant', 'materialize', 'operation', 'local')
CLAIMS += [CONSTRUCTOR + name for name in ('item_continuation', 'item_projected')]
CLAIMS += [CONSTRUCTOR + name + '_projected' for name in ENTRIES]
INTERFACES = (ENTRY + 'MissInduction', ENTRY + 'EntryInduction', CONSTRUCTOR + 'ItemInduction', NATIVE + 'EntryInduction')


def audit(claims):
    required = {
        NATIVE + 'initialized_miss_projected': {CALLER + 'initialized_taken_recorded', CALLER + 'findBody_taken', NATIVE + 'MissProjected'},
        NATIVE + 'initialized_miss_continuation': {NATIVE + 'initialized_miss_projected', NATIVE + 'miss_traced_verified'},
        ENTRY + 'source_of_projects': {RESOURCE + 'Projects.of_projects', CHILD + 'record'},
        ENTRY + 'MissInduction.of_unrestricted': {ENTRY + 'source_of_projects'},
        ENTRY + 'EntryInduction.of_unrestricted': {ENTRY + 'MissInduction.of_unrestricted'},
        ENTRY + 'entry_continuation': {NATIVE + 'initialized_miss_projected', NATIVE + 'miss_resource_traced'},
        CONSTRUCTOR + 'item_continuation': {gate.ITEM + 'prepare_success', gate.ITEM + 'good_frame', ENTRY + 'entry_continuation'},
        CONSTRUCTOR + 'item_projected': {CONSTRUCTOR + 'item_continuation', ITEM + 'item_entry_projected'},
        ITEM + 'item_induction_projected': {CONSTRUCTOR + 'item_projected', ENTRY + 'EntryInduction.of_unrestricted'},
        CONSTRUCTOR + 'borrowed_projected': {CONSTRUCTOR + 'item_projected'},
        CONSTRUCTOR + 'constant_projected': {CONSTRUCTOR + 'item_projected'},
        CONSTRUCTOR + 'materialize_projected': {CONSTRUCTOR + 'constant_projected'},
        CONSTRUCTOR + 'operation_projected': {CONSTRUCTOR + 'item_continuation', ITEM + 'literal_entry_projected', gate.ITEM + 'Arguments.prepare_success'},
        CONSTRUCTOR + 'local_projected': {CONSTRUCTOR + 'item_continuation', ITEM + 'local_entry_projected', gate.ITEM + 'ViewInput.local_input_optional'},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('resource entry lost shared composition: ' + name + ': ' + ', '.join(sorted(missing)))
    for name in CLAIMS:
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('resource entry depends on a fixture: ' + name)
    return {'checkedDependencies': sorted(required), 'sameInitializedPrefixAndMissContinuation': True,
            'allFiveRoutesUseExistingPreparationAndReturn': True, 'oldItemConsumesResourceEntry': True,
            'fixedEntryModelStillRequired': True, 'completeConstructorBodyReplayVerified': False,
            'allEntryResourceInductionVerified': False, 'composedProductionTheoremVerified': False}


def audit_statements(rows, interfaces):
    from native_constructor_checks import expression
    statements = {row['theorem']: row['statement'] for row in rows}
    definitions = {row['name']: row for row in interfaces}
    forbidden = {CALLER + 'MissContinuation', ITEM + 'EntryContinuation', ITEM + 'EntryProjected', NATIVE + 'MissProjected'}
    for name in INTERFACES[:3]:
        constants = {node[1] for node in definitions[name]['value']['nodes'] if node[0] == 'const'}
        if constants & forbidden:
            raise ValueError('resource induction assumes a completed simulation: ' + name)
    replacements = {ENTRY + 'EntryInduction': NATIVE + 'EntryInduction', ENTRY + 'MissInduction': NATIVE + 'MissInduction'}
    value, old = statements[ENTRY + 'entry_continuation'], statements[NATIVE + 'entry_continuation']
    fields, _, root, context = telescope(value)
    prior, _, old_root, old_context = telescope(old)
    if set(fields) != set(prior) or expression(value, root, context) != expression(old, old_root, old_context):
        raise ValueError('resource entry changed the complete continuation or native premises')
    for name in fields:
        if replace_names(expression(value, *fields[name]), replacements) != expression(old, *prior[name]):
            raise ValueError('resource entry changed an original input: ' + name)
    value, old = definitions[ENTRY + 'EntryInduction']['value'], definitions[NATIVE + 'EntryInduction']['value']
    if replace_names(expression(value, value['root'], []), replacements) != expression(old, old['root'], []):
        raise ValueError('resource entry changed actual initialization/take or branch guards')

    # Inspect the single reached-miss child law and its binding to the entry
    # model. No returned graph, final result or cleanup success may be assumed.
    value = definitions[ENTRY + 'MissInduction']['value']
    fields, _, root, context = telescope(value)
    prior, _, _, _ = telescope(definitions[NATIVE + 'MissInduction']['value'])
    if set(fields) != set(prior):
        raise ValueError('resource miss induction gained a final-state premise')
    for name in ('childModel', 'seed', 'predicate', 'rows', 'mismatch'):
        body = value['nodes'][joint.app(value, root, 'Exists')[-1]]
        if body[:2] != ['lambda', name]:
            raise ValueError('resource entry changed its local witness: ' + name)
        root, context = body[4], context + [name]
    initial, root = joint.app(value, root, 'And')
    joint.path(value, local_call(value, initial, context, 'predicate')[-1], context,
               (gate.OWNED + 'State.world', CALLER + 'Recorded.native'), 'taken')
    frame, root = joint.app(value, root, 'And')
    native_frame = joint.app(value, frame, gate.NS + 'InputFrame')
    named(value, native_frame[-5:-3], context, ('rows', 'source'))
    named(value, native_frame[-2:-1], context, ('slice',))
    _, lets, root, context = telescope(value, root, context)
    coupled, binding = joint.app(value, root, 'And')
    term, scope = guarded.guarded_body(value, coupled, context, guarded.source_guard(interfaces))
    reached, _, term, scope = telescope(value, term, scope)
    if list(reached) != ['rows']:
        raise ValueError('resource entry lost arbitrary reached rows')
    law = joint.app(value, term, 'Compiler.Extraction.Dispatch.Effects.SourceConstructorsAt')
    effect = joint.app(value, law[-5], RESOURCE + 'projection')
    joint.app(value, effect[-4], CHILD + 'history')
    named(value, effect[-3:-2], scope, ('stream',))
    cursor = joint.app(value, joint.app(value, effect[-2], gate.OWNED + 'Recursive.cursorGraph')[-1], MISS + 'childCursor')
    joint.path(value, cursor[-2], scope, ('List.length', CALLER + 'Recorded.events'), 'taken')
    joint.path(value, cursor[-1], scope, (gate.OWNED + 'State.world', CALLER + 'Recorded.native'), 'taken')
    named(value, law[-3:], scope, ('debug', 'child', 'childModel'))
    named(value, joint.app(value, law[-4], 'Compiler.Extraction.Nested.storageReads')[-1:], scope, ('rows',))
    child = joint.app(value, lets['child'][0], CHILD + 'constructors')
    named(value, child[-2:], lets['child'][1], ('children', 'observations'))
    parts = appended(value, lets['stream'][0])
    if len(parts) != 4:
        raise ValueError('resource entry lost its full captured suffix')
    scope = lets['stream'][1]
    selected = joint.app(value, joint.app(value, joint.app(value, parts[0], CHILD + 'history')[-1], 'Prod.snd')[-1], MISS + 'selected')
    named(value, selected[-5:-1], scope, ('request', 'key', 'slice', 'deterministic'))
    joint.path(value, selected[-1], scope, (gate.OWNED + 'State.world', CALLER + 'Recorded.native'), 'taken')
    native = joint.app(value, selected[-6], NATIVE + 'physical')
    named(value, native[-5:], scope, ('child', 'debug', 'source', 'address', 'input'))
    for term, member in zip(parts[1:3], ('body', 'cleanup')):
        joint.path(value, term, scope, (MISS + 'Segment.' + member,), 'observed')
    named(value, parts[-1:], scope, ('trailing',))
    equation = joint.app(value, binding, 'Eq')
    named(value, equation[-2:-1], context, ('model',))
    dispatch = joint.app(value, equation[-1], gate.NS + 'dispatchModel')
    named(value, dispatch[-3:], context, ('childModel', 'usizeBits', 'debug'))
    replay = joint.app(value, dispatch[-4], MISS + 'replay')
    named(value, replay[-4:-2], context, ('seed', 'events'))
    joint.path(value, replay[-2], context, (MISS + 'Segment.candidate',), 'observed')
    named(value, replay[-1:], context, ('mismatch',))

    value, old = statements[CONSTRUCTOR + 'item_projected'], statements[ITEM + 'item_induction_projected']
    fields, _, root, context = telescope(value)
    prior, _, old_root, old_context = telescope(old)
    if set(fields) != set(prior) or expression(value, root, context) != expression(old, old_root, old_context):
        raise ValueError('resource item changed the complete original result or input premises')
    for name in fields.keys() - {'induction'}:
        if expression(value, *fields[name]) != expression(old, *prior[name]):
            raise ValueError('resource item changed native preparation admission: ' + name)
    value = definitions[CONSTRUCTOR + 'ItemInduction']['value']
    root, context = value['root'], []
    while value['nodes'][root][:2] != ['forall', 'constructed']:
        node = value['nodes'][root]
        if node[0] != 'lambda':
            raise ValueError('resource item induction changed its parameter telescope')
        context.append(node[1]); root = node[4]
    if replace_names(expression(value, root, context), replacements) != expression(old, *prior['induction']):
        raise ValueError('resource item changed the original reached preparation gates')
    for name in ENTRIES:
        value = statements[CONSTRUCTOR + name + '_projected']
        fields, _, root, context = telescope(value)
        if not {'admitted', 'typed', 'capacityQuery', 'classificationQuery', 'induction'} <= fields.keys():
            raise ValueError('resource constructor lost a native/model input: ' + name)
        projected = joint.app(value, root, ITEM + 'EntryProjected')
        named(value, projected[-6:-5], context, ('model',))
        named(value, projected[-3:-1], context, ('leading', 'trailing'))
        field = {'borrowed': 'borrowedOperation', 'local': 'localOperation'}.get(name, name)
        actual = joint.app(value, projected[-1], 'Compiler.Extraction.Associative.Constructors.' + field)
        named(value, actual[-3:], context, ('debug', 'before', 'leading'))
        family = joint.app(value, actual[2], ITEM + 'constructors')
        native = joint.app(value, family[-2], gate.NS + 'context')
        named(value, native[-4:-2], context, ('owner', 'usizeBits'))
        named(value, native[-1:], context, ('debug',))
        named(value, joint.app(value, native[-2], CHILD + 'constructors')[-2:], context, ('children', 'observations'))
        host = joint.app(value, native[-5], gate.NS + 'callerContext')
        named(value, host[-7:], context, ('ops', 'allocate', 'safety', 'owner', 'meaning', 'base', 'growth'))
        ports = joint.app(value, family[-1], NATIVE + 'graphObservations')
        named(value, ports[-11:-3], context, ('ops', 'allocate', 'safety', 'owner', 'meaning', 'base', 'growth', 'usizeBits'))
        named(value, joint.app(value, ports[-3], CHILD + 'constructors')[-2:], context, ('children', 'observations'))
        named(value, joint.app(value, ports[-2], CHILD + 'liftObservations')[-1:], context, ('observations',))
    return {'sameCompleteContinuationAndItemResult': True, 'actualPrefixGuardsRetained': True,
            'actualCapturedAdmissionAndReachedRows': True, 'fixedEntryModelRetained': True,
            'allFiveActualConstructorsSelected': True, 'completeConstructorBodyReplayVerified': False,
            'allEntryResourceInductionVerified': False, 'composedProductionTheoremVerified': False}


def controls(output, env, lean):
    groups = (
        ('prefix', 'InternerCallerProtocolContinuation', (
            ('lose-initialization', 'leading ++ init.2.events.map Event.normalization ++ taken.2.events.map Event.normalization',
             'leading ++ taken.2.events.map Event.normalization', 2),
            ('lose-take', 'leading ++ init.2.events.map Event.normalization ++ taken.2.events.map Event.normalization',
             'leading ++ init.2.events.map Event.normalization', 2),
            ('lose-cleanup-history', 'actual.2.events = missLeading ++ middle ++ observed.body ++ observed.cleanup',
             'actual.2.events = missLeading ++ middle ++ observed.body', 2),
        )),
        ('entry', 'InternerCallerResourceInduction', (
            ('wrong-source-guard', '(deterministic && (request.item.kind == 1)) = true →',
             '(!deterministic && (request.item.kind == 1)) = true →', 1),
            ('rewound-cursor', 'MissStream.childCursor taken.events.length taken.native.world',
             'MissStream.childCursor 0 taken.native.world', 1),
            ('missing-body', 'request key slice deterministic taken.native.world).2 ++ observed.body ++ observed.cleanup ++ trailing',
             'request key slice deterministic taken.native.world).2 ++ observed.cleanup ++ trailing', 1),
            ('missing-cleanup', 'request key slice deterministic taken.native.world).2 ++ observed.body ++ observed.cleanup ++ trailing',
             'request key slice deterministic taken.native.world).2 ++ observed.body ++ trailing', 1),
            ('wrong-entry-model', 'model = dispatchModel (MissStream.replay seed events observed.candidate mismatch)',
             'model = dispatchModel (MissStream.replay seed events none mismatch)', 1),
            ('wrong-frame-owner', 'InputFrame safety base.allocator owner rows source request.arguments slice taken.native.world ∧',
             'InputFrame safety base.allocator (owner + 1) rows source request.arguments slice taken.native.world ∧', 1),
        )),
        ('constructors', 'InternerConstructorResourceEntries', (
            ('borrowed-wrong-address', '.borrowedOperation source.address opcode source.items debug before leading',
             '.borrowedOperation (source.address + 1) opcode source.items debug before leading', 1),
            ('constant-wrong-value', '.constant value debug before leading', '.constant (value + 1) debug before leading', 1),
            ('materialize-wrong-value', '.materialize id value debug before leading', '.materialize id (value + 1) debug before leading', 1),
            ('local-wrong-index', '.localOperation opcode ⟨address, [left, right]⟩ selected repeated first debug before leading',
             '.localOperation opcode ⟨address, [left, right]⟩ (selected + 1) repeated first debug before leading', 1),
        )),
    )
    records = []
    for group, module, changes in groups:
        code = source('Compiler.Extraction.' + module)
        # Prevent failed equality checks from unfolding the whole executor.
        # The unchanged source uses the same opacity and must still compile.
        opaque = {'entry': (gate.NS + 'dispatchModel', MISS + 'replay'),
                  'constructors': tuple(ITEM + n for n in ('item', 'literal', 'namedLocal'))}.get(group, ())
        if opaque:
            code = code.replace('\nnamespace ', '\nattribute [local irreducible] ' + ' '.join(opaque) + '\n\nnamespace ', 1)
        records += checked_controls(output, [mutation_check(output, 'resource-entry-' + group + '-unchanged', code, True, env, lean)])
        for name, old, new, count in changes:
            if code.count(old) != count:
                raise ValueError('ambiguous resource entry mutation: ' + name)
            records += checked_controls(output, [mutation_check(output, 'resource-entry-' + group + '-' + name,
                code.replace(old, new), False, env, lean)])
    return records
