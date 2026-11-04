"""Audit reached transferred first, spare and relocated insertion through the shared recursive consumer.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
import constructor_replay_choice_checks as choice
from assembly_item_creation_checks import checked_controls
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NS, OWNED = gate.NS, gate.OWNED
NATIVE, GRAPH = OWNED + 'Insertion.Native.', OWNED + 'NativeGraph.'
CLAIMS = [NATIVE + name for name in ('prepare_transferred_reached', 'transferred_growing_success_reached', 'insert_success_at')]
CLAIMS += [GRAPH + 'Facts.insert_success_at']
CLAIMS += [NS + name for name in ('CallFrame.storage_frame_rows', 'TransferredFrame.parent',
    'CallFrame.transferred_growing', 'Enclosing.transferred', 'Enclosing.insertion_transferred')]
CLAIMS += [NATIVE + 'unrelocated_append_owned_at', NATIVE + 'unrelocated_append_owned',
           NS + 'CallFrame.transferred_unrelocated', NS + 'CallFrame.transferred']
INTERFACES = tuple(NATIVE + name for name in ('successOwnership', 'successKeys', 'insert_published',
    'CallerInput.prepare_transferred', 'RelocatedTransferred', 'UnrelocatedTransferred', 'TransferredObservation'))
INTERFACES += (GRAPH + 'Facts.insert_published', NS + 'TransferredFrame.mk', NS + 'TransferredReturn')


def audit_statements(statements, definitions):
    from native_constructor_checks import expression
    # Existing publication clients must specialize the shared native adapter,
    # preserving every input outside the explicitly selected ownership mode.
    for name in (NATIVE + 'insert_success_at', GRAPH + 'Facts.insert_success_at'):
        old = definitions[name.replace('insert_success_at', 'insert_published')]['type']
        previous, _, _ = gate.domains(old)
        value = statements[name]
        fields, root, context = gate.domains(value)
        if set(fields) != set(previous) | {'deterministic'}:
            raise ValueError('success mode changed native premises: ' + name)
        for field, (index, local) in fields.items():
            if field in {'deterministic', 'ran', 'executed', 'candidate', 'keys'}:
                continue
            prior, prior_local = previous[field]
            if expression(value, index, local) != expression(old, prior, prior_local):
                raise ValueError('success mode changed an existing input: ' + name + '.' + field)
        execution_field = 'executed' if name.startswith(GRAPH) else 'ran'
        index, local = fields[execution_field]
        call, scope = choice.one_call(value, index, local, NATIVE + 'execution')
        if gate.named(value, call[12], scope) != 'deterministic':
            raise ValueError('success premise changed the native execution mode')
        for field in (execution_field, 'candidate'):
            index, local = fields[field]
            state, scope = choice.one_call(value, index, local, NATIVE + 'successOwnership')
            if gate.named(value, state[-1], scope) != 'deterministic':
                raise ValueError('success ownership differs from the executed branch')
        if name.startswith(GRAPH):
            index, local = fields['keys']
            keys, scope = choice.one_call(value, index, local, NATIVE + 'successKeys')
            if [gate.named(value, keys[i], scope) for i in (0, 2, 3, 4)] != ['deterministic', 'key', 'normalized', 'rows']:
                raise ValueError('success premise changed the key update binding')
        call, local = choice.one_call(value, value['root'], [], NATIVE + 'insert')
        if gate.named(value, call[-3], local) != 'deterministic':
            raise ValueError('success completion selects a different source branch')
        if gate.named(value, call[-1], local) != ('world' if name.startswith(GRAPH) else 'before'):
            raise ValueError('success completion rebases native execution')
    # Reached proofs remove caller provenance, while retaining validity,
    # represented input and the exact native allocation observations.
    for short in ('prepare_transferred', 'transferred_growing_success'):
        name = NATIVE + (short + '_reached')
        value = statements[name]
        fields, root, context = gate.domains(value)
        if short == 'prepare_transferred':
            old = definitions[NATIVE + 'CallerInput.' + short]['type']
            prior, _, _ = gate.domains(old)
            wanted = (set(prior) - {'request', 'values', 'lookup', 'before', 'taken', 'entry'}) | {
                'world', 'initial', 'represented', 'live', 'unique', 'normalizedLive'}
        else:
            wanted = set(('σ ops allocate freeBacking runtimeSafety allocator container oldLifetime oldCapacity capacity '
                'object base context returnAddress ownerCell source itemSource meaning input copied key normalized world cells '
                'allocated middle initial represented custody live unique ownerFound ownerTyped ownerWritable backingOwned '
                'header capacityRead registered rows resident keyApart oldItems domain oldNonempty full selected size room '
                'createCall cloneCall allocationEffects backing unlocked').split())
        if set(fields) != wanted:
            raise ValueError('reached transfer added caller/final premises: ' + name)
        for field, (index, _) in fields.items():
            if gate.step.constants_below(value, index) & {OWNED + 'Caller.Origin', NATIVE + 'CallerInput',
                    NS + 'CallFrame', NS + 'FramePost', NS + 'TransferredReturn'}:
                raise ValueError('reached transfer assumes its final result: ' + field)
        call, local = choice.one_call(value, fields['createCall'][0], fields['createCall'][1],
                                     'Compiler.Extraction.AssemblyItem.Creation.create')
        joint.path(value, call[-1], local, (OWNED + 'World.memory',), 'world')
        if short.startswith('transferred_'):
            call, local = choice.one_call(value, root, context, NATIVE + 'execution')
            if gate.named(value, call[12], local) != 'Bool.false' or gate.named(value, call[-2], local) != 'world':
                raise ValueError('reached transfer changes actual execution mode or world')
    for suffix, observation_name in (('growing', 'RelocatedTransferred'), ('unrelocated', 'UnrelocatedTransferred'), ('', 'TransferredObservation')):
        value = statements[NS + 'CallFrame.transferred' + ('_' + suffix if suffix else '')]
        fields, root, context = gate.domains(value)
        if set(fields) != {'σ', 'safety', 'allocator', 'owner', 'rows', 'source', 'values', 'normalized', 'address',
                'native', 'parent', 'world', 'frame', 'ops', 'allocate', 'growth', 'meaning', 'key', 'room', 'success'}:
            raise ValueError('transferred completion assumes a final native frame or duplicate/probe admission')
        index, local = fields['success']
        observation = joint.app(value, index, NATIVE + observation_name)
        if [gate.named(value, x, local) for x in observation] != ['σ', 'ops', 'allocate', 'allocator', 'owner', 'native'] + ([] if suffix == 'unrelocated' else ['growth']) + ['world']:
            raise ValueError('transfer observation differs from reached inputs')
        result = joint.app(value, root, NS + 'TransferredReturn')
        if [gate.named(value, x, context) for x in result[:-1]] != ['σ', 'safety', 'allocator', 'owner', 'rows', 'normalized', 'world']:
            raise ValueError('transferred completion changes the private owner or initial rows')
        if gate.named(value, result[-1], context) != 'actual':
            raise ValueError('transfer completion loses its actual run binding')
        call, local = choice.one_call(value, value['root'], [], NATIVE + 'insert')
        if [gate.named(value, x, local) for x in call] != ['σ', 'ops', 'allocate', 'safety', 'allocator', 'owner',
                'source', 'address', 'meaning', 'native', 'key', 'normalized', 'Bool.false', 'growth', 'world']:
            raise ValueError('transfer completion describes another native insertion')
    audit_interfaces(definitions)
    audit_parent(statements)
    audit_append(statements)


def audit_interfaces(definitions):
    for name in ('RelocatedTransferred', 'UnrelocatedTransferred'):
        value = definitions[NATIVE + name]['value']
        fields, root, context = gate.domains(value)
        if list(fields) != ['σ', 'ops', 'allocate', 'allocator', 'owner', 'input'] + (['growth'] if name == 'RelocatedTransferred' else []) + ['world']:
            raise ValueError('transfer observations added non-source parameters')
        forbidden = {NS + 'TransferredReturn', NS + 'TransferredFrame', NS + 'CallFrame', OWNED + 'NativeGraph.Facts',
            NATIVE + 'execution', NATIVE + 'insert', OWNED + 'Publication.publish', 'Compiler.Extraction.OwnedKeys.Live'}
        if gate.step.constants_below(value, root) & forbidden:
            raise ValueError('transfer observation assumes final ownership or execution')
        for constant in ('Compiler.Extraction.AssemblyItem.Creation.create', 'Compiler.Extraction.AssemblyClone.Physical.run',
                'Compiler.ZigAir.Memory.RegionAllocation.Fits', 'Compiler.Extraction.RepresentativeArray.Owner.NativeLock.checkHeader'):
            choice.one_call(value, root, context, constant)
    value = definitions[NATIVE + 'TransferredObservation']['value']
    _, root, context = gate.domains(value)
    branches = joint.app(value, root, 'Or')
    for term, name in zip(branches, ('UnrelocatedTransferred', 'RelocatedTransferred')):
        args = joint.app(value, term, NATIVE + name)
        if [gate.named(value, x, context) for x in args] != ['σ', 'ops', 'allocate', 'allocator', 'owner', 'input'] + (['growth'] if name == 'RelocatedTransferred' else []) + ['world']:
            raise ValueError('transferred branches changed reached source inputs')
    value = definitions[NS + 'TransferredFrame.mk']['type']
    fields, root, context = gate.domains(value)
    parameters = ['σ', 'safety', 'allocator', 'owner', 'oldData', 'oldCapacity', 'rows', 'owned', 'row', 'before', 'after']
    if list(fields) != parameters + ['native', 'keys', 'arguments', 'memory', 'registry']:
        raise ValueError('transfer frame changed its native retention contract')
    index, local = fields['keys']
    equality = joint.app(value, index, 'Eq')
    for term, name in zip(equality[-2:], ('after', 'before')):
        joint.path(value, term, local, (OWNED + 'Publication.Effects.keys', 'Compiler.Extraction.Memory.Arguments.Normalization.Session.effects', OWNED + 'World.memory'), name)
    index, local = fields['arguments']
    equality = joint.app(value, index, 'Eq')
    joint.path(value, equality[-2], local, ('Compiler.Extraction.Storage.Cell.argumentsAddress',), 'row')
    joint.path(value, equality[-1], local, ('Compiler.Extraction.Storage.ArgumentSlice.address',), 'owned')
    value = definitions[NATIVE + 'successOwnership']['value']
    _, root, context = gate.domains(value)
    branch = joint.app(value, root, 'ite')
    equal = joint.app(value, branch[-4], 'Eq')
    if [gate.named(value, x, context) for x in equal[-2:]] != ['deterministic', 'Bool.true']:
        raise ValueError('success ownership reverses its source selector')
    if [gate.named(value, x, context) for x in branch[-2:]] != ['Compiler.Extraction.Storage.publishedOwnership', 'Compiler.Extraction.Storage.transferredOwnership']:
        raise ValueError('transfer success uses a publication or cleanup owner')

    value = definitions[NATIVE + 'successKeys']['value']
    _, root, context = gate.domains(value)
    branch = joint.app(value, root, 'ite')
    equal = joint.app(value, branch[-4], 'Eq')
    if [gate.named(value, x, context) for x in equal[-2:]] != ['deterministic', 'Bool.true']:
        raise ValueError('success keys invert source determinism')
    if gate.named(value, branch[-1], context) != 'keys':
        raise ValueError('transferred success changes the key table')
    stored = joint.app(value, branch[-2], 'Compiler.Extraction.OwnedKeys.store')
    if [gate.named(value, x, context) for x in stored[:2]] != ['keys', 'key']:
        raise ValueError('published success updates a different key table')


def audit_parent(statements):
    common = {'σ', 'safety', 'allocator', 'owner', 'oldCapacity', 'oldData', 'rows', 'parentRows', 'source', 'values',
        'normalized', 'address', 'native', 'outer', 'original', 'before', 'after', 'childSource', 'request', 'childValues',
        'taken', 'owned', 'lookup', 'origin', 'initial', 'reached', 'facts', 'outerKept'}
    expected = {
        NS + 'CallFrame.storage_frame_rows': common | {'suffix', 'transferred', 'afterNative', 'keys', 'retained', 'registered'},
        NS + 'TransferredFrame.parent': common | {'row', 'post'},
        NS + 'Enclosing.transferred': {'σ', 'safety', 'allocator', 'owner', 'parent', 'stack', 'original', 'before', 'after',
            'initial', 'reached', 'source', 'request', 'values', 'taken', 'owned', 'lookup', 'origin', 'rows', 'data', 'capacity', 'row', 'facts', 'post'},
        NS + 'Enclosing.insertion_transferred': {'σ', 'safety', 'allocator', 'owner', 'parent', 'stack', 'before', 'world', 'initial',
            'source', 'request', 'values', 'taken', 'owned', 'lookup', 'origin', 'rows', 'address', 'native', 'frame',
            'ops', 'allocate', 'growth', 'meaning', 'key', 'room', 'success'},
    }
    for name, wanted in expected.items():
        value = statements[name]
        fields, root, context = gate.domains(value)
        if set(fields) != wanted:
            raise ValueError('transfer parent proof added an unproved law: ' + name)
        if name.endswith('insertion_transferred'):
            result = joint.app(value, root, NS + 'FramePost')
            choice.one_call(value, result[-1], context, OWNED + 'finish')
        elif not name.endswith('Enclosing.transferred'):
            result = joint.app(value, root, NS + 'CallFrame')
            if [gate.named(value, x, context) for x in result] != ['σ', 'safety', 'allocator', 'owner', 'parentRows',
                    'source', 'values', 'normalized', 'address', 'native', 'outer', 'after']:
                raise ValueError('transfer changes live parent geometry')


def audit_append(statements):
    value = statements[NATIVE + 'unrelocated_append_owned_at']
    fields, root, context = gate.domains(value)
    expected = set(('σ allocate safety allocator container oldCapacity object oldData ownerCell input stored key normalized operands '
        'cells value ownership middle ready growth installedPost objectPresent clonePresent argumentsPresent ownerFound ownerTyped '
        'ownerWritable header bounded storage selected first room operandsBound').split())
    if set(fields) != expected:
        raise ValueError('generic append added a final-frame or fixture premise')
    index, local = fields['argumentsPresent']
    args, scope = choice.one_call(value, index, local, OWNED + 'Insertion.arguments')
    if [gate.named(value, x, scope) for x in args[-3:]] != ['normalized', 'ownership', 'ready']:
        raise ValueError('generic append disconnects its actual argument owner')
    forbidden = {NS + 'CallFrame', NS + 'TransferredReturn', GRAPH + 'Facts', NATIVE + 'append', NATIVE + 'execution'}
    for field, (index, _) in fields.items():
        if gate.step.constants_below(value, index) & forbidden:
            raise ValueError('generic append assumes its result: ' + field)
    calls = list(choice.applications(value, root, context, NATIVE + 'append'))
    if len(calls) != 2:
        raise ValueError('generic append lost optional-growth equivalence')
    for call, scope in calls:
        if [gate.named(value, x, scope) for x in call[:-1]] != ['σ', 'safety', 'allocate', 'allocator', 'container',
                'cells', 'input', 'key', 'normalized', 'value', 'ownership', 'ready']:
            raise ValueError('generic append changes the reached inputs or ownership')


def dependencies():
    return {
        CLAIMS[0]: {NATIVE + 'prepare_item', NATIVE + 'arguments_retained'},
        CLAIMS[1]: {CLAIMS[0], NATIVE + 'growing_append_owned', NATIVE + 'append_cell', 'Compiler.Extraction.Storage.insert_transferred_success'},
        CLAIMS[2]: {NATIVE + 'checkedExecution_read', NATIVE + 'body'},
        CLAIMS[3]: {CLAIMS[2], GRAPH + 'data_frame', 'Compiler.Extraction.OwnedKeys.view_store'},
        CLAIMS[4]: {OWNED + 'Caller.Origin.fresh', OWNED + 'ArraySource.storage'},
        CLAIMS[5]: {CLAIMS[4]},
        CLAIMS[6]: {CLAIMS[1], CLAIMS[3]},
        CLAIMS[7]: {CLAIMS[5], NS + 'Enclosing.rec'},
        CLAIMS[8]: {NS + 'CallFrame.transferred', CLAIMS[7], OWNED + 'finish_handoff'},
        NATIVE + 'unrelocated_append_owned_at': {NATIVE + 'first_append_owned', NATIVE + 'spare_append_owned',
            'Compiler.Extraction.RepresentativeArray.Append.Registered.first_same',
            'Compiler.Extraction.RepresentativeArray.Append.Registered.spare_same'},
        NATIVE + 'unrelocated_append_owned': {NATIVE + 'unrelocated_append_owned_at'},
        NS + 'CallFrame.transferred_unrelocated': {CLAIMS[0], NATIVE + 'unrelocated_append_owned_at',
            GRAPH + 'Facts.frame', CLAIMS[3], NATIVE + 'append_cell', 'Compiler.Extraction.Storage.insert_transferred_success'},
        NS + 'CallFrame.transferred': {CLAIMS[6], NS + 'CallFrame.transferred_unrelocated'},
    }


def mutation_cases():
    def source(name):
        raw = (gate.harness.ROOT / 'lean/Compiler/Extraction' / (name + '.lean')).read_text()
        return '\n'.join(line for line in raw.splitlines() if line.startswith('import ')) + '\n' + (
            'set_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw))
    return (
        ('graph', source('InternerNativeGraphInsertion'), (
            ('wrong-mode', 'if deterministic then Storage.publishedOwnership else Storage.transferredOwnership',
             'if deterministic then Storage.transferredOwnership else Storage.publishedOwnership', 1),
            ('publish-transferred-key', 'else keys\n', 'else OwnedKeys.store keys key ⟨normalized.address, Storage.idFor rows⟩\n', 1),
        )),
        ('storage', source('InternerNativeParentRelease'), (
            ('wrong-row-owner', 'row.argumentsAddress = owned.address', 'row.argumentsAddress = normalized.address', 1),
            ('rewind-suffix', 'after (rows ++ suffix)', 'after rows', 1),
        )),
        ('frame', source('InternerNativeTransferredFrame'), (
            ('wrong-transfer-address', 'row.argumentsAddress = owned.address', 'row.argumentsAddress = owned.address + 1', 1),
            ('exclude-empty-storage', '(oldCapacity ≠ 0 → id ≠ oldData.allocation)', '(id ≠ oldData.allocation)', 2),
            ('rewind-outer', '(outerKept : outer after)', '(outerKept : outer before)', 1),
        )),
        ('unrelocated', source('InternerNativeUnrelocatedTransferred'), (
            ('rewind-create', 'input.item world.memory = (.ok object, allocated)', 'input.item allocated = (.ok object, allocated)', 1),
            ('wrong-first-request', 'allocate allocator 160 8 installed.effects.allocator', 'allocate allocator 80 8 installed.effects.allocator', 2),
            ('full-as-spare', '[]).length < oldCapacity', '[]).length ≤ oldCapacity', 1),
            ('wrong-success-mode', 'native key normalized false growth world', 'native key normalized true growth world', 2),
        )),
        ('append', source('InternerInsertionUnrelocatedAppend'), (
            ('wrong-local-owner', 'arguments normalized ownership ready = some operands', 'arguments normalized preparationOwnership ready = some operands', 1),
            ('exclude-first-sentinel', '(oldCapacity ≠ 0 → id ≠ oldData.allocation)', '(id ≠ oldData.allocation)', 3),
        )),
        ('completion', source('InternerNativeTransferredCompletion'), (
            ('rewind-create', 'input.item world.memory = (.ok object, allocated)', 'input.item allocated = (.ok object, allocated)', 1),
            ('wrong-request-size', '(capacity * 32) 8 installed.effects.allocator', '(capacity * 16) 8 installed.effects.allocator', 1),
            ('wrong-full-bound', 'oldCapacity < Append.nextLength', 'oldCapacity ≤ Append.nextLength', 1),
            ('wrong-success-mode', 'native key normalized false growth world', 'native key normalized true growth world', 1),
        )),
    )


def controls(output, env, lean):
    records = []
    for group, source, changes in mutation_cases():
        records += checked_controls(output, [mutation_check(output, 'transferred-success-' + group + '-unchanged', source, True, env, lean)])
        for name, before, after, count in changes:
            if source.count(before) != count:
                raise ValueError('ambiguous transferred success mutation: ' + name)
            records += checked_controls(output, [mutation_check(output, 'transferred-success-' + group + '-' + name,
                source.replace(before, after), False, env, lean)])
    return records
