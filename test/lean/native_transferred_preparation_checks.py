"""Audit reached transferred preparation and the shared branch-selected frame.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
import constructor_replay_choice_checks as choice
from assembly_item_creation_checks import checked_controls
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

OWNED, NS = gate.OWNED, gate.NS
NATIVE = OWNED + 'Insertion.Native.'
MEMORY = 'Compiler.Extraction.Memory.Arguments.Normalization.'
CLAIMS = [NATIVE + name for name in ('transferred_argument_cleanup', 'transferred_create_oom_execution',
          'transferred_clone_oom_execution', 'preparation_oom_execution_at')]
INTERFACES = tuple(NATIVE + name for name in ('TransferredFailure.mk', 'TransferredPreparationOOM',
    'TransferredPreparationOOM.create', 'TransferredPreparationOOM.clone', 'PreparationOOMAt', 'preparation_oom_execution'))


def audit_statements(statements, definitions):
    from native_constructor_checks import expression
    base = {'σ', 'ops', 'allocate', 'runtimeSafety', 'allocator', 'container', 'source', 'itemSource',
            'meaning', 'input', 'key', 'normalized', 'before', 'cells', 'growth', 'valid', 'live', 'failed', 'room', 'created'}
    expected = {
        CLAIMS[0]: {'σ', 'ops', 'allocate', 'safety', 'allocator', 'container', 'source', 'address', 'input', 'key',
            'normalized', 'before', 'cells', 'value', 'graph', 'growth', 'owner', 'reached', 'valid', 'live',
            'present', 'retained', 'keys', 'cleared'},
        CLAIMS[1]: base,
        CLAIMS[2]: base | {'represented', 'object', 'allocated', 'cloned'},
    }
    for name, wanted in expected.items():
        value = statements[name]
        fields, root, context = gate.domains(value)
        if set(fields) != wanted:
            raise ValueError('transferred failure changed its native inputs: ' + name)
        for field, (index, _) in fields.items():
            constants = gate.step.constants_below(value, index)
            if constants & {NATIVE + 'CallerInput', OWNED + 'Caller.Origin', NATIVE + 'TransferredFailure',
                    NATIVE + 'PrivateFrame', NS + 'Returns', NS + 'GraphFrame', NS + 'FramePost'}:
                raise ValueError('transferred failure assumes a caller origin or final result: ' + name + '.' + field)
        post, local = choice.one_call(value, root, context, NATIVE + 'TransferredFailure')
        if gate.named(value, post[1], local) != 'normalized':
            raise ValueError('transferred failure consumes a different owner')
        if name in CLAIMS[1:3]:
            joint.path(value, post[2], local, (OWNED + 'World.memory',), 'before')
            if gate.named(value, post[3], local) != 'failed':
                raise ValueError('transferred failure rewinds allocation history')
            call, local = choice.one_call(value, root, context, NATIVE + 'execution')
            if [gate.named(value, x, local) for x in call] != ['σ', 'ops', 'allocate', 'runtimeSafety', 'allocator',
                    'container', 'source', 'itemSource', 'meaning', 'input', 'key', 'normalized', 'Bool.false', 'cells', 'before', 'growth']:
                raise ValueError('transferred failure changed the native execution')
    value = statements[CLAIMS[3]]
    fields, root, context = gate.domains(value)
    old = definitions[NATIVE + 'preparation_oom_execution']['type']
    old_fields, _, _ = gate.domains(old)
    if set(fields) != set(old_fields) | {'deterministic'}:
        raise ValueError('selected preparation added a final preservation premise')
    for field, (index, local) in fields.items():
        if field in ('deterministic', 'failed'):
            continue
        prior, prior_local = old_fields[field]
        if expression(value, index, local) != expression(old, prior, prior_local):
            raise ValueError('selected preparation changed an existing input: ' + field)
    index, local = fields['failed']
    selected = joint.app(value, index, NATIVE + 'PreparationOOMAt')
    if [gate.named(value, x, local) for x in selected[:-1]] != ['σ', 'ops', 'allocator', 'input', 'normalized', 'deterministic']:
        raise ValueError('preparation admission lost the actual ownership mode')
    joint.path(value, selected[-1], local, (OWNED + 'World.memory',), 'before')
    actual, local = choice.one_call(value, root, context, NATIVE + 'execution')
    if [gate.named(value, x, local) for x in actual] != ['σ', 'ops', 'allocate', 'safety', 'allocator', 'container',
            'source', 'address', 'meaning', 'input', 'key', 'normalized', 'deterministic', 'rows', 'before', 'growth']:
        raise ValueError('selected preparation changes the source execution')
    audit_interfaces(definitions)


def audit_interfaces(definitions):
    value = definitions[NATIVE + 'TransferredFailure.mk']['type']
    fields, root, context = gate.domains(value)
    if list(fields) != ['σ', 'normalized', 'before', 'history', 'after', 'valid', 'consumed', 'nextId', 'nextAddress',
                        'frame', 'object', 'value', 'marker']:
        raise ValueError('transferred failure changed its postconditions')
    index, local = fields['frame']
    args = joint.app(value, index, NATIVE + 'PrivateFrame')
    if [gate.named(value, x, local) for x in args[:-1]] != ['σ', 'normalized', 'before']:
        raise ValueError('transferred failure rebound its private frame')
    joint.path(value, args[-1], local, (OWNED + 'Insertion.memory',), 'after')
    for name in ('nextId', 'nextAddress'):
        index, local = fields[name]
        eq = joint.app(value, index, 'Eq')
        joint.path(value, eq[-2], local, ('Compiler.ZigAir.Memory.State.' + name, MEMORY + 'Session.memory', OWNED + 'Insertion.memory'), 'after')
        joint.path(value, eq[-1], local, ('Compiler.ZigAir.Memory.State.' + name, MEMORY + 'Session.memory'), 'history')
    index, local = fields['consumed']
    args = joint.app(value, index, MEMORY + 'Consumed')
    if gate.named(value, args[-2], local) != 'normalized':
        raise ValueError('transferred failure consumes a different argument owner')
    joint.path(value, args[-1], local, (OWNED + 'Insertion.memory',), 'after')
    info = definitions[NATIVE + 'TransferredPreparationOOM']
    if info['kind'] != 'inductive' or info['constructors'] != [NATIVE + 'TransferredPreparationOOM.' + name for name in ('create', 'clone')]:
        raise ValueError('transferred admission lost a source outcome')
    for name, extra in (('create', set()), ('clone', {'object', 'allocated', 'created'})):
        value = definitions[NATIVE + 'TransferredPreparationOOM.' + name]['type']
        fields, _, _ = gate.domains(value)
        if set(fields) != {'σ', 'ops', 'allocator', 'input', 'before', 'failed', 'called'} | extra:
            raise ValueError('transferred admission added a non-source premise')
        index, local = fields['called']
        eq = joint.app(value, index, 'Eq')
        call = 'Compiler.Extraction.AssemblyItem.Creation.create' if name == 'create' else 'Compiler.Extraction.AssemblyClone.Physical.run'
        args = joint.app(value, eq[-2], call)
        if gate.named(value, args[-1], local) != ('before' if name == 'create' else 'allocated'):
            raise ValueError('transferred admission observes a different reached session')
        pair = joint.app(value, eq[-1], 'Prod.mk')
        error = joint.app(value, pair[-2], 'Except.error')
        if not gate.named(value, error[-1], local).endswith('.outOfMemory') or gate.named(value, pair[-1], local) != 'failed':
            raise ValueError('transferred admission changed its ordinary failure')
    value = definitions[NATIVE + 'PreparationOOMAt']['value']
    fields, root, context = gate.domains(value)
    if list(fields) != ['σ', 'ops', 'allocator', 'input', 'normalized', 'deterministic', 'before']:
        raise ValueError('preparation selection added assumptions')
    branch = joint.app(value, root, 'ite')
    eq = joint.app(value, branch[-4], 'Eq')
    if [gate.named(value, x, context) for x in eq[-2:]] != ['deterministic', 'Bool.true']:
        raise ValueError('preparation selection inverted the source classifier')
    yes = joint.app(value, branch[-2], NATIVE + 'PreparationOOM')
    no = joint.app(value, branch[-1], NATIVE + 'TransferredPreparationOOM')
    if [gate.named(value, x, context) for x in yes] != ['σ', 'ops', 'allocator', 'input', 'normalized', 'before']:
        raise ValueError('duplicated preparation changed its input binding')
    if [gate.named(value, x, context) for x in no] != ['σ', 'ops', 'allocator', 'input', 'before']:
        raise ValueError('transferred preparation changed its input binding')


def dependencies():
    return {
        CLAIMS[0]: {MEMORY + 'free_valid', NATIVE + 'free_private_frame', NATIVE + 'free_keeps_dead'},
        CLAIMS[1]: {CLAIMS[0], 'Compiler.Extraction.AssemblyItem.Creation.create_oom', 'Compiler.Extraction.Storage.insert_transferred_create_oom'},
        CLAIMS[2]: {CLAIMS[0], 'Compiler.Extraction.AssemblyItem.Creation.create_verified',
            'Compiler.Extraction.AssemblyClone.Physical.run_oom', 'Compiler.Extraction.AssemblyItem.destroy_verified',
            'Compiler.Extraction.AssemblyItem.Creation.NativeFields.clone_oom', 'Compiler.Extraction.Storage.insert_transferred_clone_oom'},
        CLAIMS[3]: {CLAIMS[1], CLAIMS[2], NATIVE + 'preparation_oom_execution'},
    }


def mutation_cases():
    def source(name):
        raw = (gate.harness.ROOT / 'lean/Compiler/Extraction' / (name + '.lean')).read_text()
        return '\n'.join(line for line in raw.splitlines() if line.startswith('import ')) + '\n' + (
            'set_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw))
    return (
        ('reached', source('InternerInsertionTransferredFailure'), (
            ('wrong-mode', 'input key normalized false cells before growth', 'input key normalized true cells before growth', 2),
            ('wrong-create-outcome', 'input.item before.memory = (.error .outOfMemory, failed)', 'input.item before.memory = (.ok 0, failed)', 1),
            ('wrong-clone-outcome', 'input allocated = (.error .outOfMemory, failed)', 'input allocated = (.ok input, failed)', 1),
            ('stale-source', 'allocated allocator object itemSource input\n    valid represented createdPost',
             'allocated allocator object ⟨itemSource.allocation + 1, itemSource.offset⟩ input\n    valid represented createdPost', 1),
            ('retain-arguments', 'consumed : Consumed normalized (memory after)', 'consumed : ¬ Consumed normalized (memory after)', 1),
            ('rewind-history', 'nextId = history.memory.nextId', 'nextId = before.memory.nextId', 1),
            ('omit-native-retention', '(memory reached).memory.heap.lookup id = some cell ∧',
             'before.memory.heap.lookup id = some cell ∧', 1),
            ('omit-registry-retention', '(memory reached).heap id = before.heap id)', 'before.heap id = before.heap id)', 1),
            ('double-release', '(Storage.Cleanup.sequence [.arguments]).run transferredArguments',
             '(Storage.Cleanup.sequence [.arguments, .normalized]).run transferredArguments', 1),
        )),
        ('selection', source('InternerInsertionPreparationOutcome'), (
            ('inverted-mode', 'if deterministic then PreparationOOM', 'if !deterministic then PreparationOOM', 1),
            ('success-after-oom', '((.ok (some .allocationFailure), closed), after)', '((.ok (some .success), closed), after)', 2),
            ('lost-normalized-binding', 'PrivateFrame normalized before.memory (memory after)',
             'PrivateFrame { normalized with address := normalized.address + 1 } before.memory (memory after)', 2),
        )),
    )


def controls(output, env, lean):
    records = []
    for group, source, changes in mutation_cases():
        records += checked_controls(output, [mutation_check(output, 'transferred-frame-' + group + '-unchanged', source, True, env, lean)])
        for name, before, after, count in changes:
            if source.count(before) != count:
                raise ValueError('ambiguous transferred frame mutation: ' + name)
            records += checked_controls(output, [mutation_check(output, 'transferred-frame-' + group + '-' + name,
                source.replace(before, after), False, env, lean)])
    return records
