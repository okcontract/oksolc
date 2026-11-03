"""Audit entry-fixed replay through actual constructor preparation and return.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
from native_miss_frame_checks import named
from native_resource_admission_checks import telescope
from native_algebraic_dispatch_checks import source
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check

ITEM = gate.ITEM + 'ProtocolTrace.'
ENTRY = ITEM + 'CheckpointEntry.'
CALLER = gate.OWNED + 'Caller.ProtocolTrace.Native.CheckpointEntry.'
TRACE = gate.NS + 'AllocationTrace.'
MEMORY = 'Compiler.ZigAir.Memory.'
NORMALIZATION = 'Compiler.Extraction.Memory.Arguments.Normalization.'
ENTRIES = ('borrowed', 'constant', 'materialize', 'operation', 'local')
CLAIMS = [ENTRY + n for n in ('item_continuation', 'item_projected', 'prepared_continuation')]
CLAIMS += [ENTRY + n + '_projected' for n in ENTRIES]
INTERFACES = (ENTRY + 'model', ENTRY + 'ItemInduction')
NATIVE = ('σ', 'ops', 'allocate', 'safety', 'owner', 'meaning', 'base', 'growth', 'usizeBits',
          'children', 'observations', 'debug', 'childModel', 'seed', 'stream', 'mismatch')
COMMON = ('before', 'leading', 'trailing', 'other', 'read', 'sequence', 'admitted', 'typed',
          'closedQuery', 'capacityQuery', 'classificationQuery', 'induction')


def audit(claims):
    required = {
        'item_continuation': {gate.ITEM + 'prepare_success', gate.ITEM + 'Prepared.nextId',
            gate.ITEM + 'good_frame', CALLER + 'entry_continuation'},
        'item_projected': {ENTRY + 'item_continuation', ITEM + 'item_entry_projected'},
        'prepared_continuation': {ENTRY + 'item_continuation', gate.ITEM + 'Arguments.Prepared.counter'},
        'borrowed_projected': {ENTRY + 'item_projected'},
        'constant_projected': {ENTRY + 'item_projected'},
        'materialize_projected': {ENTRY + 'constant_projected'},
        'operation_projected': {ENTRY + 'prepared_continuation', ITEM + 'literal_entry_projected', gate.ITEM + 'Arguments.prepare_success'},
        'local_projected': {ENTRY + 'prepared_continuation', ITEM + 'local_entry_projected', gate.ITEM + 'ViewInput.local_input_optional'},
    }
    for name, needed in required.items():
        if missing := needed - claims[ENTRY + name]:
            raise ValueError('checkpoint constructor lost shared composition: ' + name + ': ' + ', '.join(sorted(missing)))
    for name in CLAIMS:
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('checkpoint constructor depends on fixtures: ' + name)
    return {'checkedDependencies': sorted(ENTRY + n for n in required), 'actualPreparationCountersConsumed': True,
            'allFiveConstructorsUseFixedInputModel': True, 'sharedPreparationAndReturn': True,
            'properChildDispatcherFrameAndStreamDerived': False, 'completeConstructorBodyReplayVerified': False,
            'composedProductionTheoremVerified': False}


def numeral(value, term, number):
    call = joint.app(value, term, 'OfNat.ofNat')
    if value['nodes'][call[-2]] != ['natural', str(number)]:
        raise ValueError('constructor allocation offset changed')


def before_id(value, term, context):
    joint.path(value, term, context, (MEMORY + 'State.nextId', NORMALIZATION + 'Session.memory', gate.OWNED + 'World.memory'), 'before')


def cursor(value, term, context, route):
    if route in ('borrowed', 'constant', 'materialize', 'item_projected', 'item_continuation'):
        before_id(value, term, context)
        return
    added = joint.app(value, term, 'HAdd.hAdd')
    before_id(value, added[-2], context)
    if route == 'local':
        numeral(value, added[-1], 1)
    else:
        branch = joint.app(value, added[-1], 'ite')
        numeral(value, branch[-2], 0)
        numeral(value, branch[-1], 1)
        condition = joint.app(value, branch[-4], 'Eq')
        named(value, condition[-1:], context, ('Bool.true',))
        empty = joint.app(value, condition[-2], 'List.isEmpty')
        if route == 'operation':
            named(value, empty[-1:], context, ('values',))
        else:
            joint.path(value, empty[-1], context, ('Compiler.Extraction.Interner.Request.arguments',), 'request')


def fixed_model(value, term, context, route):
    call = joint.app(value, term, ENTRY + 'model')
    named(value, call[:7], context, ('meaning', 'usizeBits', 'debug', 'childModel', 'seed', 'stream', 'mismatch'))
    cursor(value, call[-2], context, route)
    return call[-1]


def audit_statements(rows, interfaces):
    from native_constructor_checks import expression
    statements = {r['theorem']: r['statement'] for r in rows}
    definitions = {r['name']: r for r in interfaces}
    value = definitions[ENTRY + 'model']['value']
    fields, _, root, context = telescope(value)
    if set(fields) != {'meaning', 'usizeBits', 'debug', 'childModel', 'seed', 'stream', 'mismatch', 'initialId', 'item'}:
        raise ValueError('constructor model gained a prepared or completed input')
    dispatch = joint.app(value, root, gate.NS + 'dispatchModel')
    named(value, dispatch[-3:], context, ('childModel', 'usizeBits', 'debug'))
    replay = joint.app(value, dispatch[-4], TRACE + 'inputGraphReplay')
    named(value, replay[:1] + replay[-3:], context, ('seed', 'meaning', 'stream', 'mismatch'))
    named(value, joint.app(value, replay[1], gate.ITEM + 'input'), context, ('item', 'debug'))
    added = joint.app(value, replay[2], 'HAdd.hAdd')
    named(value, added[-2:-1], context, ('initialId',))
    numeral(value, added[-1], 2)
    value = definitions[ENTRY + 'ItemInduction']['value']
    fields, _, root, context = telescope(value)
    anonymous = {n for n in fields if n.startswith('a.')}
    if len(anonymous) != 3 or set(fields) != set(NATIVE) | anonymous | {
            'initialId', 'source', 'request', 'before', 'leading', 'trailing', 'constructed', 'address', 'memory'}:
        raise ValueError('constructor induction changed actual preparation guards')
    forbidden = {ITEM + 'EntryProjected', ITEM + 'EntryContinuation', gate.OWNED + 'Caller.ProtocolTrace.MissContinuation'}
    if {n[1] for n in value['nodes'] if n[0] == 'const'} & forbidden:
        raise ValueError('constructor induction assumes a complete replay')
    called = joint.app(value, root, CALLER + 'Induction')
    named(value, called[-8:-6] + called[-5:-3], context, ('childModel', 'seed', 'stream', 'mismatch'))
    added = joint.app(value, called[-6], 'HAdd.hAdd')
    named(value, added[-2:-1], context, ('initialId',))
    numeral(value, added[-1], 2)
    for route in ('item_continuation', 'item_projected', 'prepared_continuation') + ENTRIES:
        name = route if route.endswith('continuation') or route == 'item_projected' else route + '_projected'
        value = statements[ENTRY + name]
        fields, _, root, context = telescope(value)
        extras = {
            'item_continuation': {'source', 'request', 'good', 'domain'},
            'item_projected': {'source', 'request', 'good', 'domain'},
            'prepared_continuation': {'source', 'request', 'prepared', 'ready', 'domain'},
            'borrowed': {'source', 'opcode', 'good'}, 'constant': {'value', 'valid'},
            'materialize': {'id', 'value', 'valid'}, 'operation': {'opcode', 'values', 'valid'},
            'local': {'address', 'opcode', 'left', 'right', 'repeated', 'selected', 'first', 'good', 'inside'},
        }[route]
        expected = set(NATIVE) | set(COMMON) | extras
        if route.endswith('continuation'):
            expected -= {'capacityQuery', 'classificationQuery'}
        if set(fields) != expected:
            raise ValueError('constructor gained a prepared identity or complete simulation premise: ' + route)
        if route.endswith('continuation'):
            result = joint.app(value, root, ITEM + 'EntryContinuation')
            fixed_model(value, result[-7], context, route)
        else:
            result = joint.app(value, root, ITEM + 'EntryProjected')
            item = fixed_model(value, result[-6], context, route)
            request_item = joint.app(value, item, 'Compiler.Extraction.Interner.Request.item')[-1]
            if expression(value, request_item, context) != expression(value, result[-5], context):
                raise ValueError('constructor model changed the source request: ' + route)
            joint.path(value, result[-4], context, (gate.OWNED + 'World.graph',), 'before')
            named(value, result[-3:-1], context, ('leading', 'trailing'))
            if route in ENTRIES:
                field = {'borrowed': 'borrowedOperation', 'local': 'localOperation'}.get(route, route)
                actual = joint.app(value, result[-1], 'Compiler.Extraction.Associative.Constructors.' + field)
                named(value, actual[-3:], context, ('debug', 'before', 'leading'))
                arguments = actual[3:-3]
                if route == 'borrowed':
                    joint.path(value, arguments[0], context, ('Compiler.Extraction.Storage.ArgumentSlice.address',), 'source')
                    named(value, arguments[1:2], context, ('opcode',))
                    joint.path(value, arguments[2], context, ('Compiler.Extraction.Storage.ArgumentSlice.items',), 'source')
                elif route in ('constant', 'materialize', 'operation'):
                    named(value, arguments, context, {'constant': ('value',), 'materialize': ('id', 'value'),
                                                     'operation': ('opcode', 'values')}[route])
                else:
                    named(value, arguments[:1] + arguments[2:], context, ('opcode', 'selected', 'repeated', 'first'))
                    descriptor = joint.app(value, arguments[1], 'Compiler.Extraction.Storage.ArgumentSlice.mk')
                    named(value, descriptor[:1], context, ('address',))
                    left = joint.app(value, descriptor[-1], 'List.cons')
                    right = joint.app(value, left[-1], 'List.cons')
                    named(value, (left[-2], right[-2]), context, ('left', 'right'))
                    joint.app(value, right[-1], 'List.nil')
                family = joint.app(value, actual[2], TRACE + 'step')
                named(value, family[-10:], context, ('ops', 'allocate', 'safety', 'owner', 'meaning', 'base', 'growth',
                    'usizeBits', 'children', 'observations'))
        term, scope = fields['induction']
        _, _, body, scope = telescope(value, term, scope)
        local = joint.app(value, body, ENTRY + 'ItemInduction')
        named(value, local[:len(NATIVE)], scope, NATIVE)
        cursor(value, local[-6], scope, route)
        if expression(value, local[-4], scope) != expression(value, result[-5], context):
            raise ValueError('local induction changed the source request: ' + route)
        named(value, local[-3:-2], scope,
              ('prepared' if route in ('operation', 'local', 'prepared_continuation') else 'before',))
        named(value, local[-2:], scope, ('leading', 'trailing'))
    return {'fixedModelBeforeItemAndArgumentPreparation': True, 'emptyAndNonemptyAllocationOffsetsExact': True,
            'actualCheckpointCapturesForAllFiveRoutes': True, 'existingCompleteReturnProofsConsumed': True,
            'completeConstructorBodyReplayVerified': False, 'composedProductionTheoremVerified': False}


def controls(output, env, lean):
    code = source('Compiler.Extraction.InternerCheckpointConstructorReplay')
    # Default delaboration recurses while displaying a mismatched Word argument.
    # Explicit diagnostics affect printing only; both partners retain all proof
    # limits and the same strict rejection checks.
    code = code.replace('namespace Compiler.Extraction.',
                        'set_option pp.all true\n\nnamespace Compiler.Extraction.', 1)
    records = checked_controls(output, [mutation_check(output, 'checkpoint-constructors-unchanged', code, True, env, lean)])
    for name, old, new, count in (
        ('missing-scratch', '(initialId + 2)', '(initialId + 1)', 2),
        ('extra-preparation', '(initialId + 2)', '(initialId + 3)', 2),
        ('wrong-item', '(input item debug)', '(input { item with data := 0 } debug)', 1),
        ('wrong-stream', '(initialId + 2) meaning stream mismatch)', '(initialId + 2) meaning stream.reverse mismatch)', 1),
        ('borrowed-wrong-address', '.borrowedOperation source.address opcode source.items debug before leading',
         '.borrowedOperation (source.address + 1) opcode source.items debug before leading', 1),
        ('constant-wrong-value', '.constant value debug before leading', '.constant (value + 1) debug before leading', 1),
        ('materialize-wrong-value', '.materialize id value debug before leading', '.materialize id (value + 1) debug before leading', 1),
        ('empty-literal-allocated', 'if values.isEmpty then 0 else 1', 'if values.isEmpty then 1 else 1', 4),
        ('nonempty-literal-unallocated', 'if values.isEmpty then 0 else 1', 'if values.isEmpty then 0 else 0', 4),
        ('local-unallocated', '(before.memory.memory.nextId + 1)', '(before.memory.memory.nextId + 0)', 4),
        ('local-wrong-guard', '(inside : first = true → selected < 2)', '(inside : first = false → selected < 2)', 1),
        ('local-wrong-index', '.localOperation opcode ⟨address, [left, right]⟩ selected repeated first debug before leading',
         '.localOperation opcode ⟨address, [left, right]⟩ (selected + 1) repeated first debug before leading', 1),
    ):
        if code.count(old) != count:
            raise ValueError('ambiguous checkpoint constructor control: ' + name + ': ' + str(code.count(old)))
        records += checked_controls(output, [mutation_check(output, 'checkpoint-constructors-' + name,
            code.replace(old, new), False, env, lean)])
    return records
