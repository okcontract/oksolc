"""Audit proper-child bodies through initialization and every constructor entry.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
import guarded_induction_checks as guarded
from native_miss_frame_checks import named
from native_resource_admission_checks import telescope
from native_resource_miss_checks import appended
from native_checkpoint_constructor_checks import cursor, numeral
from native_algebraic_dispatch_checks import source
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check

CALLER = gate.OWNED + 'Caller.ProtocolTrace.'
ENTRY = CALLER + 'Native.CheckpointEntry.'
ITEM = gate.ITEM + 'ProtocolTrace.'
PREVIOUS = ITEM + 'CheckpointEntry.'
CONSTRUCTOR = ITEM + 'CheckpointBodies.'
TRACE = gate.NS + 'AllocationTrace.'
CHILD = gate.NS + 'ChildTrace.'
ROUTES = ('borrowed', 'constant', 'materialize', 'operation', 'local')
CLAIMS = [ENTRY + n for n in ('AtMiss.mono', 'miss_from_bodies', 'induction_from_bodies', 'entry_continuation_from_bodies')]
CLAIMS += [CONSTRUCTOR + 'item_induction_from_bodies'] + [CONSTRUCTOR + r + '_projected' for r in ROUTES]
CLAIMS += [TRACE + 'replay_appended']
INTERFACES = (ENTRY + 'BodyMiss', ENTRY + 'BodyInduction', CONSTRUCTOR + 'ItemBodies', TRACE + 'streamReplay')
NATIVE = {'σ', 'depth', 'ops', 'allocate', 'safety', 'owner', 'usizeBits', 'meaning', 'base', 'growth',
          'outerOps', 'outerAllocate', 'outerBase', 'outerGrowth', 'debug', 'models', 'stream'}


def audit(claims):
    required = {
        ENTRY + 'AtMiss.mono': {ENTRY + 'AtMiss'},
        ENTRY + 'miss_from_bodies': {TRACE + 'selected_from_bodies', TRACE + 'replay_appended', gate.NS + 'CallFrame.mapAllocator_iff'},
        ENTRY + 'induction_from_bodies': {ENTRY + 'AtMiss.mono', ENTRY + 'miss_from_bodies'},
        ENTRY + 'entry_continuation_from_bodies': {ENTRY + 'induction_from_bodies', ENTRY + 'entry_continuation'},
        CONSTRUCTOR + 'item_induction_from_bodies': {ENTRY + 'induction_from_bodies'},
        TRACE + 'replay_appended': {TRACE + 'replay', TRACE + 'streamReplay', TRACE + 'rebase', 'List.drop_left'},
    }
    for route in ROUTES:
        required[CONSTRUCTOR + route + '_projected'] = {CONSTRUCTOR + 'item_induction_from_bodies', PREVIOUS + route + '_projected'}
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('body entry lost shared composition: ' + name + ': ' + ', '.join(sorted(missing)))
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('body entry depends on fixtures: ' + name)
    return {'checkedDependencies': sorted(required), 'actualPrefixSharedByBothInductionForms': True,
            'allFiveEntriesConsumeProperBodies': True, 'initializationAndReturnProofsReused': True,
            'completeRecursiveBodiesVerified': False, 'fixedStreamChildFamilyDerived': True,
            'nativeAdmissionDerived': False, 'composedProductionTheoremVerified': False}


def child_depth(value, term, context):
    child = joint.app(value, term, TRACE + 'children')
    named(value, child[1:-1], context, ('ops', 'allocate', 'safety', 'owner', 'meaning', 'base', 'growth', 'usizeBits'))
    depth = joint.app(value, child[-1], 'HAdd.hAdd')
    named(value, depth[-2:-1], context, ('depth',))
    numeral(value, depth[-1], 1)


def fixed_model(value, term, context, route):
    call = joint.app(value, term, PREVIOUS + 'model')
    named(value, call[:3] + call[4:7], context, ('meaning', 'usizeBits', 'debug', 'seed', 'stream', 'mismatch'))
    named(value, joint.app(value, call[3], TRACE + 'streamReplay'), context, ('stream', 'models'))
    cursor(value, call[-2], context, route)
    return call[-1]


def audit_statements(rows, interfaces):
    from native_constructor_checks import expression
    statements = {r['theorem']: r['statement'] for r in rows}
    definitions = {r['name']: r for r in interfaces}
    value = definitions[TRACE + 'streamReplay']['value']
    fields, _, root, context = telescope(value)
    if list(fields) != ['stream', 'models']:
        raise ValueError('fixed child family gained a reached-state input')
    mapped = joint.app(value, root, ITEM + 'mapConstructors')
    named(value, mapped[-1:], context, ('models',))
    fields, _, root, context = telescope(value, mapped[-2], context)
    if list(fields) != ['model']:
        raise ValueError('fixed child family changed its body mapping')
    bind = joint.app(value, root, 'Bind.bind')
    named(value, joint.app(value, bind[-2], TRACE + 'enter') + bind[-1:], context, ('stream', 'model'))
    value = statements[TRACE + 'replay_appended']
    fields, _, root, context = telescope(value)
    if set(fields) != {'σ', 'leading', 'middle', 'trailing', 'root', 'models'}:
        raise ValueError('history rebasing gained a premise')
    eq = joint.app(value, root, 'Eq')
    replay = joint.app(value, eq[-2], TRACE + 'replay')
    named(value, replay[1:2] + replay[-2:], context, ('leading', 'root', 'models'))
    raw = appended(value, replay[2])
    joint.path(value, raw[0], context, (CHILD + 'history',), 'root')
    named(value, raw[1:], context, ('middle', 'trailing'))
    fixed = joint.app(value, eq[-1], TRACE + 'streamReplay')
    named(value, appended(value, fixed[0]) + fixed[1:], context, ('leading', 'middle', 'trailing', 'models'))
    value = definitions[ENTRY + 'BodyMiss']['value']
    fields, _, root, context = telescope(value)
    anonymous = [n for n in fields if n.startswith('a.')]
    if set(fields) != NATIVE | {'source', 'address', 'input', 'request', 'key', 'deterministic',
                               'taken', 'trailing', 'slice', 'handle', 'lookup'} | set(anonymous) or len(anonymous) != 3:
        raise ValueError('proper-body miss gained a completed result or changed its source guards')
    for field in ('rows', 'parent'):
        node = value['nodes'][joint.app(value, root, 'Exists')[-1]]
        if node[:2] != ['lambda', field]:
            raise ValueError('proper-body miss gained a local model/result witness')
        root, context = node[4], context + [field]
    _, lets, root, context = telescope(value, root, context)
    frame, root = joint.app(value, root, 'And')
    history, proper = joint.app(value, root, 'And')
    frame = joint.app(value, frame, gate.NS + 'CallFrame')
    named(value, frame[-8:-6] + frame[-5:-1], context, ('rows', 'source', 'slice', 'address', 'input', 'parent'))
    joint.path(value, frame[-1], context, (CHILD + 'erase', gate.OWNED + 'State.world', CALLER + 'Recorded.native'), 'taken')
    eq = joint.app(value, history, 'Eq')
    named(value, appended(value, eq[-2]), context, ('history', 'trailing'))
    named(value, eq[-1:], context, ('stream',))
    proper, scope = guarded.guarded_body(value, proper, context, guarded.source_guard(interfaces))
    reached, _, term, scope = telescope(value, proper, scope)
    if list(reached) != ['reachedRows']:
        raise ValueError('proper-body miss lost reached row quantification')
    bodies = joint.app(value, term, TRACE + 'BodiesAt')
    named(value, bodies[-3:-2] + bodies[-1:], scope, ('debug', 'models'))
    joint.path(value, bodies[1], scope, (CALLER + 'Recorded.events',), 'taken')
    named(value, bodies[2:3], scope, ('rawStream',))
    joint.path(value, bodies[3], scope, (gate.OWNED + 'State.world', CALLER + 'Recorded.native'), 'taken')
    native = joint.app(value, bodies[-2], TRACE + 'body')
    named(value, native[1:], scope, ('ops', 'allocate', 'safety', 'owner', 'meaning', 'base', 'growth', 'usizeBits', 'depth'))
    raw = appended(value, lets['rawStream'][0])
    if len(raw) != 4:
        raise ValueError('proper-body miss lost the complete raw stream suffix')
    scope = lets['rawStream'][1]
    joint.path(value, raw[0], scope, (CHILD + 'history', 'Prod.snd'), 'decision')
    named(value, raw[1:2] + raw[-1:], scope, ('bodyEvents', 'trailing'))
    joint.path(value, raw[2], scope, (gate.OWNED + 'MissStream.Segment.cleanup',), 'observed')
    value = definitions[ENTRY + 'BodyInduction']['value']
    fields, _, root, context = telescope(value)
    if set(fields) != NATIVE | {'source', 'address', 'input', 'request', 'buffer', 'before', 'trailing'}:
        raise ValueError('proper-body induction gained nonlocal inputs')
    prefix = joint.app(value, root, ENTRY + 'AtMiss')
    named(value, prefix[1:5] + prefix[-2:], context, ('outerOps', 'outerBase', 'source', 'request', 'buffer', 'before'))
    local, _, root, context = telescope(value, prefix[-3], context)
    if list(local) != ['key', 'deterministic', 'taken']:
        raise ValueError('proper-body induction changed the shared prefix continuation')
    miss = joint.app(value, root, ENTRY + 'BodyMiss')
    named(value, miss[-4:], context, ('key', 'deterministic', 'taken', 'trailing'))
    value = definitions[CONSTRUCTOR + 'ItemBodies']['value']
    fields, _, root, context = telescope(value)
    anonymous = [n for n in fields if n.startswith('a.')]
    if set(fields) != NATIVE | {'source', 'request', 'before', 'leading', 'trailing',
                               'constructed', 'address', 'memory'} | set(anonymous) or len(anonymous) != 3:
        raise ValueError('item body admission changed its actual preparation guards')
    joint.app(value, root, ENTRY + 'BodyInduction')
    for route in ROUTES:
        value = statements[CONSTRUCTOR + route + '_projected']
        fields, _, root, context = telescope(value)
        extras = {'borrowed': {'source', 'opcode', 'good'}, 'constant': {'value', 'valid'},
                  'materialize': {'id', 'value', 'valid'}, 'operation': {'opcode', 'values', 'valid'},
                  'local': {'address', 'opcode', 'left', 'right', 'repeated', 'selected', 'first', 'good', 'inside'}}[route]
        common = {'seed', 'mismatch', 'before', 'leading', 'trailing', 'other', 'read', 'sequence',
                  'admitted', 'typed', 'capacityQuery', 'closedQuery', 'classificationQuery', 'bodies'}
        if set(fields) != NATIVE | common | extras:
            raise ValueError('constructor body gained a prepared identity or result premise: ' + route)
        post = joint.app(value, root, ITEM + 'EntryProjected')
        item = fixed_model(value, post[-6], context, route)
        request = joint.app(value, item, 'Compiler.Extraction.Interner.Request.item')[-1]
        if expression(value, request, context) != expression(value, post[-5], context):
            raise ValueError('constructor body model changed the source request')
        joint.path(value, post[-4], context, (gate.OWNED + 'World.graph',), 'before')
        named(value, post[-3:-1], context, ('leading', 'trailing'))
        member = {'borrowed': 'borrowedOperation', 'local': 'localOperation'}.get(route, route)
        capture = joint.app(value, post[-1], 'Compiler.Extraction.Associative.Constructors.' + member)
        named(value, capture[-3:], context, ('debug', 'before', 'leading'))
        family = joint.app(value, capture[2], TRACE + 'step')
        named(value, family[1:-2], context, ('outerOps', 'outerAllocate', 'safety', 'owner', 'meaning', 'outerBase', 'outerGrowth', 'usizeBits'))
        child_depth(value, family[-2], context)
        _, _, term, scope = telescope(value, *fields['bodies'])
        local = joint.app(value, term, CONSTRUCTOR + 'ItemBodies')
        if expression(value, local[-4], scope) != expression(value, post[-5], context):
            raise ValueError('constructor body changed the prepared request')
        named(value, local[-3:], scope, ('prepared' if route in ('operation', 'local') else 'before', 'leading', 'trailing'))
    return {'initialFramesAndProperBodiesOnly': True, 'sharedActualInitializationPrefix': True,
            'fullStreamBindingExplicit': True, 'allFiveActualConstructorEntries': True,
            'completeRecursiveBodiesVerified': False, 'fixedStreamChildFamilyDerived': True,
            'composedProductionTheoremVerified': False}


def controls(output, env, lean):
    groups = (
        ('stream', 'InternerAllocationSourceReplay', (
            ('wrong-fixed-stream', 'enter stream >>= model', 'enter stream.reverse >>= model', 1),
            ('lost-raw-prefix', 'ChildTrace.history root ++ middle ++ trailing', 'middle ++ trailing', 1),
        )),
        ('guard', 'InternerCheckpointEntryReplay', (
            ('wrong-outcome', 'ordinary decision.1 = true → decision.1 =', 'ordinary decision.1 = false → decision.1 =', 1),
            ('wrong-alignment', 'key.arguments = slice.items →', 'request.arguments = slice.items →', 1),
            ('skip-take', 'next key deterministic taken.2', 'next key deterministic normalized.2', 1),
        )),
        ('entry', 'InternerCheckpointEntryBodies', (
            ('wrong-guard', '(deterministic && (request.item.kind == 1)) = true →', '(!deterministic && (request.item.kind == 1)) = true →', 1),
            ('wrong-body-depth', 'base growth usizeBits depth) models)', 'base growth usizeBits (depth + 1)) models)', 1),
            ('assumed-later-frame', 'parent (ChildTrace.erase taken.native.world)', 'parent (ChildTrace.erase decision.2)', 1),
            ('wrong-stream', 'history ++ trailing = stream', 'history ++ trailing = stream.reverse', 1),
            ('wrong-fixed-stream', 'AllocationTrace.streamReplay stream models', 'AllocationTrace.streamReplay stream.reverse models', 1),
        )),
        ('constructors', 'InternerCheckpointConstructorBodies', (
            ('wrong-child-depth', '(depth + 1)', '(depth + 2)', 2),
            ('borrowed-wrong-address', '.borrowedOperation source.address opcode source.items', '.borrowedOperation (source.address + 1) opcode source.items', 1),
            ('empty-literal-allocated', 'if values.isEmpty then 0 else 1', 'if values.isEmpty then 1 else 1', 2),
            ('local-wrong-index', '.localOperation opcode ⟨address, [left, right]⟩ selected repeated first',
             '.localOperation opcode ⟨address, [left, right]⟩ (selected + 1) repeated first', 1),
        )),
    )
    records = []
    for label, module, changes in groups:
        code = source('Compiler.Extraction.' + module)
        code = code.replace('namespace Compiler.Extraction.', 'set_option pp.all true\n\nnamespace Compiler.Extraction.', 1)
        records += checked_controls(output, [mutation_check(output, 'checkpoint-body-entry-' + label + '-unchanged', code, True, env, lean)])
        for name, old, new, count in changes:
            if code.count(old) != count:
                raise ValueError('ambiguous body entry control: ' + name + ': ' + str(code.count(old)))
            records += checked_controls(output, [mutation_check(output, 'checkpoint-body-entry-' + label + '-' + name,
                code.replace(old, new), False, env, lean)])
    return records
