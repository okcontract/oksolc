"""Audit the fixed caller input model and its actual initialization consumer.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
import constructor_replay_choice_checks as choice
from native_miss_frame_checks import named
from native_resource_admission_checks import telescope, local_call
from native_algebraic_dispatch_checks import source
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check
from check_zig_air_memory_proofs import without_imports

CALLER = gate.OWNED + 'Caller.'
PROTOCOL = CALLER + 'ProtocolTrace.'
ENTRY = PROTOCOL + 'Native.CheckpointEntry.'
TRACE = gate.NS + 'AllocationTrace.'
INSERTION = gate.OWNED + 'Insertion.Native.'
QUERIES = 'Compiler.Extraction.Interner.Queries.'
MISS = gate.OWNED + 'MissStream.'
SLICE = 'Compiler.Extraction.Storage.ArgumentSlice.'
KEY = 'Compiler.Extraction.Cache.Key.'
MEMORY = 'Compiler.ZigAir.Memory.'
NORMALIZATION = 'Compiler.Extraction.Memory.Arguments.Normalization.'
CLAIMS = [QUERIES + 'nondeterministic_noncommutative', CALLER + 'nondeterministic_taken',
          CALLER + 'taken_replay_inputs', INSERTION + 'allocationCandidate_inputs',
          TRACE + 'insertionReplay_inputs', MISS + 'scoped_ports',
          ENTRY + 'entry_continuation', ENTRY + 'find_projected']
INTERFACES = (TRACE + 'inputGraphReplay', ENTRY + 'Miss', ENTRY + 'Induction', ENTRY + 'AtMiss')
NATIVE_INPUTS = ('σ', 'ops', 'allocate', 'safety', 'owner', 'meaning', 'base', 'growth', 'usizeBits',
                'children', 'observations', 'debug', 'source', 'address', 'input', 'request', 'model', 'seed')


def next_input(value, term, context):
    added = joint.app(value, term, 'HAdd.hAdd')
    joint.path(value, added[-2], context, (MEMORY + 'State.nextId', NORMALIZATION + 'Session.memory', gate.OWNED + 'World.memory'), 'before')
    one = joint.app(value, added[-1], 'OfNat.ofNat')
    if value['nodes'][one[-2]] != ['natural', '1']:
        raise ValueError('checkpoint input lost the actual scratch allocation')


def fixed_model(value, term, context):
    model = joint.app(value, term, gate.NS + 'dispatchModel')
    named(value, model[-3:], context, ('model', 'usizeBits', 'debug'))
    ports = joint.app(value, model[-4], TRACE + 'inputGraphReplay')
    named(value, ports[:2] + ports[3:], context, ('seed', 'input', 'meaning', 'stream', 'mismatch'))
    next_input(value, ports[2], context)


def false_guard(value, term, context):
    fields, _, root, scope = telescope(value, term, context)
    if len(fields) != 1:
        raise ValueError('input address law changed its nondeterministic guard')
    guard, local = next(iter(fields.values()))
    named(value, joint.app(value, guard, 'Eq')[-2:], local, ('deterministic', 'Bool.false'))
    return root, scope


def audit(claims):
    required = {
        QUERIES + 'nondeterministic_noncommutative': {QUERIES + 'deterministic_exact'},
        CALLER + 'nondeterministic_taken': {QUERIES + 'nondeterministic_noncommutative',
            'Compiler.Extraction.Memory.Arguments.Normalization.init_refines',
            'Compiler.Extraction.Memory.Arguments.Normalization.take_refines'},
        CALLER + 'taken_replay_inputs': {CALLER + 'nondeterministic_taken', CALLER + 'take_origin',
            gate.OWNED + 'key_arguments', 'Compiler.ZigAir.Memory.allocate_pointer'},
        TRACE + 'insertionReplay_inputs': {INSERTION + 'allocationCandidate_inputs'},
        MISS + 'scoped_ports': {MISS + 'scoped_routed'},
        ENTRY + 'entry_continuation': {CALLER + 'taken_replay_inputs', PROTOCOL + 'initialized_taken_recorded',
            TRACE + 'insertionReplay_inputs', MISS + 'scoped_ports', PROTOCOL + 'Native.checkpoint_miss',
            PROTOCOL + 'missBody_selected_ordinary'},
        ENTRY + 'find_projected': {ENTRY + 'entry_continuation', PROTOCOL + 'find_projected'},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('checkpoint entry lost composition: ' + name + ': ' + ', '.join(sorted(missing)))
    for name in CLAIMS:
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('checkpoint entry depends on fixtures: ' + name)
    return {'checkedDependencies': sorted(required), 'normalizedReplayInputsDerived': True,
            'fixedModelReachesCompleteCaller': True, 'newResourceObservationsRequired': False,
            'properChildDispatcherAndFrameDerived': False, 'completeConstructorBodyReplayVerified': False,
            'composedProductionTheoremVerified': False}


def audit_statements(rows, interfaces):
    statements = {r['theorem']: r['statement'] for r in rows}
    definitions = {r['name']: r for r in interfaces}
    value = definitions[TRACE + 'inputGraphReplay']['value']
    fields, _, _, _ = telescope(value)
    if set(fields) != {'seed', 'input', 'incoming', 'meaning', 'stream', 'mismatch'}:
        raise ValueError('input model depends on a selected slice or completed candidate')
    replay, context = choice.one_call(value, value['root'], [], TRACE + 'insertionReplay')
    named(value, replay[:1] + replay[2:], context, ('input', 'meaning', 'key', 'deterministic', 'stream', 'mismatch'))
    descriptor = joint.app(value, replay[1], 'Compiler.Extraction.Storage.ArgumentSlice.mk')
    named(value, descriptor[:1], context, ('incoming',))
    joint.path(value, descriptor[-1], context, ('Compiler.Extraction.Cache.Key.arguments',), 'key')
    published, context = choice.one_call(value, value['root'], [], 'Compiler.Extraction.Interner.InvocationTrace.publish')
    named(value, published[-1:], context, ('stream',))
    for name in ('Miss', 'Induction', 'AtMiss'):
        value = definitions[ENTRY + name]['value']
        constants = {n[1] for n in value['nodes'] if n[0] == 'const'}
        forbidden = {PROTOCOL + 'MissContinuation', PROTOCOL + 'Native.MissProjected',
                     TRACE + 'graphReplay', MISS + 'replay', INSERTION + 'observedCandidate'}
        if constants & forbidden:
            raise ValueError('entry obligation assumes a completed replay or candidate: ' + name)
    value = statements[CALLER + 'taken_replay_inputs']
    fields, _, root, context = telescope(value)
    if set(fields) != {'σ', 'external', 'budget', 'allocator', 'source', 'request', 'before', 'memory', 'pointer',
                       'values', 'prepared', 'called', 'key', 'slice', 'deterministic', 'good', 'admitted',
                       'allocated', 'initialized', 'transferred', 'classified', 'made', 'present'}:
        raise ValueError('replay input identity gained an assumed descriptor')
    items, address = joint.app(value, root, 'And')
    equation = joint.app(value, items, 'Eq')
    joint.path(value, equation[-2], context, (SLICE + 'items',), 'slice')
    joint.path(value, equation[-1], context, (KEY + 'arguments',), 'key')
    address, scope = false_guard(value, address, context)
    equation = joint.app(value, address, 'Eq')
    joint.path(value, equation[-2], scope, (SLICE + 'address',), 'slice')
    next_input(value, equation[-1], scope)
    for name in (INSERTION + 'allocationCandidate_inputs', TRACE + 'insertionReplay_inputs'):
        value = statements[name]
        fields, _, _, _ = telescope(value)
        root, scope = false_guard(value, *fields['transferred'])
        equation = joint.app(value, root, 'Eq')
        joint.path(value, equation[-2], scope, (SLICE + 'address',), 'normalized')
        named(value, equation[-1:], scope, ('incoming',))
    for name in ('entry_continuation', 'find_projected'):
        value = statements[ENTRY + name]
        fields, lets, root, context = telescope(value)
        base = set(NATIVE_INPUTS) | {'stream', 'mismatch', 'before', 'memory', 'pointer', 'leading', 'trailing',
                                    'other', 'read', 'sequence', 'good', 'admitted', 'allocated', 'closedQuery', 'induction'}
        anonymous = [n for n in fields if n.startswith('a.')]
        expected = base if name == 'entry_continuation' else base | {'capacityQuery', 'classificationQuery'} | set(anonymous)
        if set(fields) != expected or len(anonymous) != (name == 'find_projected'):
            raise ValueError('checkpoint entry gained a selected slice, candidate or complete simulation premise')
        term, scope = fields['induction']
        induction = joint.app(value, term, ENTRY + 'Induction')
        named(value, induction[-7:-6] + induction[-5:-3], scope, ('seed', 'stream', 'mismatch'))
        next_input(value, induction[-6], scope)
        if name == 'entry_continuation':
            continuation = joint.app(value, root, PROTOCOL + 'MissContinuation')
            fixed_model(value, continuation[-6], context)
        else:
            fixed_model(value, *lets['logicalModel'])
            term, scope = fields[anonymous[0]]
            condition = joint.app(value, term, 'Eq')
            joint.path(value, joint.app(value, condition[-2], gate.OWNED + 'ordinary')[-1], scope, ('Prod.fst',), 'body')
            named(value, condition[-1:], scope, ('Bool.true',))
            logical, scope = lets['logical']
            logical = joint.app(value, logical, 'Compiler.Extraction.Interner.Scoped.findDetailed')
            named(value, logical[-3:-1], scope, ('logicalModel', 'request'))
            resources = joint.app(value, logical[-4], 'Compiler.Extraction.Interner.InvocationTrace.resources')
            from native_resource_miss_checks import appended
            history = appended(value, resources[-2])
            joint.path(value, history[0], scope, (PROTOCOL + 'Recorded.events', 'Prod.snd'), 'actual')
            named(value, history[1:], scope, ('trailing',))
            for binding, function in (('body', 'findBody'), ('actual', 'find')):
                term, scope = lets[binding]
                called = joint.app(value, term, PROTOCOL + function)
                named(value, called[-4:-3] + called[-2:], scope, ('source', 'request', 'entry'))
                native = joint.app(value, called[-7], PROTOCOL + 'Native.physical')
                named(value, native[-13:], scope, ('ops', 'allocate', 'safety', 'owner', 'meaning', 'base', 'growth',
                    'usizeBits', 'children', 'debug', 'source', 'address', 'input'))
                observed = joint.app(value, called[-5], TRACE + 'graphObservations')
                named(value, observed[-14:], scope, ('ops', 'allocate', 'safety', 'owner', 'meaning', 'base', 'growth',
                    'usizeBits', 'children', 'observations', 'debug', 'source', 'address', 'input'))
            relation, tokens = joint.app(value, root, 'And')
            equation = joint.app(value, relation, 'Eq')
            actual, logical = (joint.app(value, side, 'Prod.mk') for side in equation[-2:])
            joint.path(value, actual[-2], context, ('Prod.fst',), 'actual')
            joint.path(value, actual[-1], context, (PROTOCOL + 'scopeView', 'Prod.snd'), 'actual')
            returned = joint.app(value, logical[-2], 'Except.mapError')
            named(value, returned[-2:-1], context, (gate.OWNED + 'Fault.language',))
            joint.path(value, returned[-1], context, ('Prod.fst',), 'logical')
            joint.path(value, logical[-1], context, ('Prod.snd',), 'logical')
            equation = joint.app(value, tokens, 'Eq')
            joint.path(value, equation[-2], context, (PROTOCOL + 'Tokens.incomplete', PROTOCOL + 'Recorded.tokens', 'Prod.snd'), 'actual')
            named(value, equation[-1:], context, ('Bool.false',))
    value = definitions[ENTRY + 'Miss']['value']
    fields, _, root, context = telescope(value)
    anonymous = [n for n in fields if n.startswith('a.')]
    if set(fields) != set(NATIVE_INPUTS) | {'incoming', 'stream', 'mismatch', 'key', 'deterministic', 'taken', 'trailing',
                                        'slice', 'handle', 'lookup'} | set(anonymous) or len(anonymous) != 3:
        raise ValueError('local checkpoint entry changed its actual inputs or scope guards')
    alignment, scope = fields[anonymous[-1]]
    alignment = joint.app(value, alignment, 'Eq')
    joint.path(value, alignment[-2], scope, (KEY + 'arguments',), 'key')
    joint.path(value, alignment[-1], scope, (SLICE + 'items',), 'slice')
    for name in ('rows', 'parent'):
        body = value['nodes'][joint.app(value, root, 'Exists')[-1]]
        if body[:2] != ['lambda', name]:
            raise ValueError('checkpoint entry gained a model or final-state witness')
        root, context = body[4], context + [name]
    _, lets, root, context = telescope(value, root, context)
    frame, root = joint.app(value, root, 'And')
    history, projection = joint.app(value, root, 'And')
    from native_resource_miss_checks import appended
    equation = joint.app(value, history, 'Eq')
    named(value, appended(value, equation[-2]), context, ('history', 'trailing'))
    named(value, equation[-1:], context, ('stream',))
    guard, _, term, scope = telescope(value, frame, context)
    if len(guard) != 1:
        raise ValueError('reached frame changed its ordinary-decision guard')
    term_guard, local = next(iter(guard.values()))
    condition = joint.app(value, term_guard, 'Eq')
    joint.path(value, joint.app(value, condition[-2], gate.OWNED + 'ordinary')[-1], local, ('Prod.fst',), 'decision')
    named(value, condition[-1:], local, ('Bool.true',))
    call = joint.app(value, term, gate.NS + 'CallFrame')
    named(value, call[-8:-6] + call[-5:-1], scope, ('rows', 'source', 'slice', 'address', 'input', 'parent'))
    joint.path(value, call[-1], scope, ('Prod.snd',), 'decision')
    guards, _, root, context = telescope(value, projection, context)
    if len(guards) != 1:
        raise ValueError('dispatcher projection lost its ordinary-decision guard')
    condition, local = next(iter(guards.values()))
    condition = joint.app(value, condition, 'Eq')
    named(value, condition[-1:], local, ('Bool.true',))
    joint.path(value, joint.app(value, condition[-2], gate.OWNED + 'ordinary')[-1], local, ('Prod.fst',), 'decision')
    selected, reached = joint.app(value, root, 'And')
    equation = joint.app(value, selected, 'Eq')
    joint.path(value, equation[-2], context, ('Prod.fst',), 'decision')
    mapped = joint.app(value, equation[-1], 'Except.mapError')
    named(value, mapped[-2:-1], context, (gate.OWNED + 'Fault.language',))
    joint.path(value, mapped[-1], context, ('Prod.fst',), 'logicalDecision')
    equation = joint.app(value, reached, 'Eq')
    joint.path(value, equation[-1], context, ('Prod.snd',), 'logicalDecision')
    _, updates, term, scope = telescope(value, equation[-2], context)
    if len(updates) != 1:
        raise ValueError('checkpoint entry changed the reached graph update')
    graph_name, (graph, local) = next(iter(updates.items()))
    joint.path(value, graph, local, (gate.OWNED + 'World.graph', 'Prod.snd'), 'decision')
    heap = joint.app(value, term, 'Compiler.Extraction.Interner.Heap.mk')
    for field, member in zip(heap[-4:-1], ('read', 'table', 'representatives')):
        joint.path(value, field, scope, ('Compiler.Extraction.Interner.Heap.' + member,), graph_name)
    position = joint.app(value, heap[-1], 'List.length')[-1]
    prefix = appended(value, position)
    joint.path(value, prefix[0], scope, (PROTOCOL + 'Recorded.events',), 'taken')
    named(value, prefix[1:], scope, ('middle',))
    value = definitions[ENTRY + 'Induction']['value']
    fields, lets, root, context = telescope(value)
    if set(fields) != set(NATIVE_INPUTS) | {'incoming', 'stream', 'mismatch', 'buffer', 'before', 'trailing'}:
        raise ValueError('checkpoint induction changed its fixed entry inputs')
    at_miss = joint.app(value, root, ENTRY + 'AtMiss')
    named(value, at_miss[1:5] + at_miss[-2:], context, ('ops', 'base', 'source', 'request', 'buffer', 'before'))
    local_fields, _, root, context = telescope(value, at_miss[-3], context)
    if list(local_fields) != ['key', 'deterministic', 'taken']:
        raise ValueError('checkpoint induction changed local miss inputs')
    miss = joint.app(value, root, ENTRY + 'Miss')
    named(value, miss[-7:], context, ('incoming', 'stream', 'mismatch', 'key', 'deterministic', 'taken', 'trailing'))
    value = definitions[ENTRY + 'AtMiss']['value']
    fields, lets, root, context = telescope(value)
    anonymous = [n for n in fields if n.startswith('a.')]
    if set(fields) != {'σ', 'ops', 'base', 'source', 'request', 'next', 'buffer', 'before',
                      'values', 'key', 'deterministic'} | set(anonymous) or len(anonymous) != 6:
        raise ValueError('checkpoint induction changed its source guards')
    next_miss = local_call(value, root, context, 'next')
    named(value, next_miss[:2], context, ('key', 'deterministic'))
    joint.path(value, next_miss[-1], context, ('Prod.snd',), 'taken')
    for binding, action, observer, start in (
        ('normalized', CALLER + 'initLookup', PROTOCOL + 'initialization', 'before'),
        ('taken', gate.OWNED + 'take', PROTOCOL + 'taking', 'normalized'),
    ):
        term, scope = lets[binding]
        call = joint.app(value, term, PROTOCOL + 'record')
        first = joint.app(value, call[-3], action)
        second = joint.app(value, call[-2], observer)
        if binding == 'normalized':
            named(value, first[-3:], scope, ('source', 'buffer', 'request'))
            named(value, second[-3:], scope, ('source', 'buffer', 'request'))
            named(value, call[-1:], scope, (start,))
        else:
            joint.path(value, call[-1], scope, ('Prod.snd',), start)
    return {'fixedModelBeforeKeyAndSliceSelection': True, 'keySuppliesNormalizedValues': True,
            'actualInitializationAndTakeConsumed': True, 'completeCallerUsesSharedProof': True,
            'completeConstructorBodyReplayVerified': False, 'composedProductionTheoremVerified': False}


def controls(output, env, lean):
    records = []
    groups = (
        ('classification', 'InternerQueries', (
            ('wrong-guard', 'queries.deterministic item = .ok false', 'queries.deterministic item = .ok true'),
            ('wrong-result', 'Interner.Scoped.commutative item = .ok false', 'Interner.Scoped.commutative item = .ok true'),
        )),
        ('inputs', 'InternerCallerInputIdentity', (
            ('wrong-take-address', 'some ⟨before.memory.memory.nextId, request.arguments⟩', 'some ⟨before.memory.memory.nextId + 1, request.arguments⟩'),
            ('wrong-scratch-address', 'slice.address = before.memory.memory.nextId + 1', 'slice.address = before.memory.memory.nextId'),
            ('sorted-address-assumed', '(deterministic = false → slice.address = before.memory.memory.nextId + 1)',
             '(deterministic = true → slice.address = before.memory.memory.nextId + 1)'),
            ('wrong-key-values', 'slice.items = key.arguments ∧', 'slice.items = request.arguments ∧'),
        )),
        ('candidate', 'InternerInsertionCandidateIdentity', (
            ('wrong-address-guard', '(transferred : deterministic = false → normalized.address = incoming)',
             '(transferred : deterministic = true → normalized.address = incoming)'),
        )),
        ('model', 'InternerCheckpointInputModel', (
            ('lost-key-values', '(aligned : normalized.items = key.arguments)', '(aligned : normalized.items = normalized.items)'),
            ('wrong-transfer-guard', '(transferred : deterministic = false → normalized.address = incoming)',
             '(transferred : deterministic = true → normalized.address = incoming)'),
        )),
        ('entry', 'InternerCheckpointEntryReplay', (
            ('rewound-model-address', '(before.memory.memory.nextId + 1)', 'before.memory.memory.nextId'),
            ('wrong-input-item', 'let logicalModel := dispatchModel (AllocationTrace.inputGraphReplay seed input',
             'let logicalModel := dispatchModel (AllocationTrace.inputGraphReplay seed { input with item := { input.item with data := 0 } }'),
            ('wrong-stream', 'history ++ trailing = stream', 'history ++ trailing = stream.reverse'),
            ('unclosed-caller', 'logical.2) ∧ actual.2.tokens.incomplete = false', 'scopeView body.2) ∧ actual.2.tokens.incomplete = false'),
            ('unfinished-caller', 'logical.2) ∧ actual.2.tokens.incomplete = false', 'logical.2) ∧ actual.2.tokens.incomplete = true'),
        )),
    )
    for label, module, mutations in groups:
        code = source('Compiler.Extraction.' + module)
        records += checked_controls(output, [mutation_check(output, 'checkpoint-entry-' + label + '-unchanged', code, True, env, lean)])
        for name, old, new in mutations:
            count = code.count(old)
            expected = 7 if name == 'rewound-model-address' else 1
            if count != expected:
                raise ValueError('ambiguous checkpoint entry control: ' + name + ': ' + str(count))
            records += checked_controls(output, [mutation_check(output, 'checkpoint-entry-' + label + '-' + name,
                code.replace(old, new), False, env, lean)])
    model = source('Compiler.Extraction.InternerCheckpointInputModel')
    entry = source('Compiler.Extraction.InternerCheckpointEntryReplay')
    imports = '\n'.join(dict.fromkeys(line for line in (model + '\n' + entry).splitlines()
        if line.startswith('import ') and line != 'import Compiler.Extraction.InternerCheckpointInputModel'))
    combined = imports + '\n' + without_imports(model) + '\n' + without_imports(entry)
    records += checked_controls(output, [mutation_check(output, 'checkpoint-entry-model-consumer-unchanged', combined, True, env, lean)])
    for name, old, new in (
        ('wrong-incoming', 'insert := fun key deterministic => insertionReplay input ⟨incoming, key.arguments⟩',
         'insert := fun key deterministic => insertionReplay input ⟨incoming + 1, key.arguments⟩'),
        ('wrong-key', 'insert := fun key deterministic => insertionReplay input ⟨incoming, key.arguments⟩',
         'insert := fun key deterministic => insertionReplay input ⟨incoming, []⟩'),
        ('wrong-publication', 'publish := Interner.InvocationTrace.publish stream',
         'publish := Interner.InvocationTrace.publish stream.reverse'),
    ):
        if combined.count(old) != 1:
            raise ValueError('ambiguous input model control: ' + name)
        records += checked_controls(output, [mutation_check(output, 'checkpoint-entry-model-consumer-' + name,
            combined.replace(old, new), False, env, lean)])
    return records
