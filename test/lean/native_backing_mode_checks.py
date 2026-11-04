"""Audit source-selected backing refusal and its enclosing-frame consumer.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
import constructor_replay_choice_checks as choice
from assembly_item_creation_checks import checked_controls
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NATIVE = gate.OWNED + 'Insertion.Native.'
CLAIMS = [NATIVE + name for name in ('item_cleanup_apart', 'prepared_arguments', 'append_oom_reached_at',
    'first_allocation_oom_reached_at', 'growing_allocation_oom_reached_at')]
CLAIMS += [gate.NS + 'CallFrame.backing_oom_execution_at']
INTERFACES = tuple(NATIVE + name for name in ('PreparationInput', 'preparedFrameAt', 'preparationOwnershipAt',
    'appendFailureState', 'BackingAllocationOOMAt', 'BackingAllocationOOM', 'append_oom_reached',
    'first_allocation_oom_reached', 'growing_allocation_oom_reached')) + (gate.NS + 'CallFrame.backing_oom_execution',)


def audit_statements(statements, definitions):
    from native_constructor_checks import expression
    for name in CLAIMS[2:]:
        value = statements[name]
        fields, root, context = gate.domains(value)
        old = definitions[name.removesuffix('_at')]['type']
        previous, _, _ = gate.domains(old)
        if set(fields) != set(previous) | {'deterministic'}:
            raise ValueError('backing mode changed its native premises: ' + name)
        changed = {'deterministic', 'duplicateCall', 'failed', 'refused'}
        if 'duplicateCall' in fields:
            changed.add('admitted')
        for field, (index, local) in fields.items():
            if field not in changed:
                prior, prior_local = previous[field]
                if expression(value, index, local) != expression(old, prior, prior_local):
                    raise ValueError('backing mode changed an existing input: ' + name + '.' + field)
        if 'duplicateCall' in fields:
            index, local = fields['duplicateCall']
            args = joint.app(value, index, NATIVE + 'PreparationInput')
            if [gate.named(value, x, local) for x in args[:7]] != ['σ', 'ops', 'allocator', 'normalized', 'operands', 'remaining', 'deterministic']:
                raise ValueError('backing preparation changed its actual inputs')
            joint.path(value, args[7], local, (gate.OWNED + 'World.memory',), 'world')
            if gate.named(value, args[8], local) != 'duplicated':
                raise ValueError('backing preparation changed its reached session')
            index, local = fields['admitted']
            field = value['nodes'][index]
            if field[0] != 'forall':
                raise ValueError('transferred backing assumes duplication admission')
            condition = joint.app(value, field[3], 'Eq')
            if [gate.named(value, x, local) for x in condition[-2:]] != ['deterministic', 'Bool.true']:
                raise ValueError('duplication admission uses the wrong branch')
            prior, prior_local = previous['admitted']
            if expression(value, field[4], local + [field[1]]) != expression(old, prior, prior_local):
                raise ValueError('duplication admission added a stronger contract')
        else:
            index, local = fields['failed']
            args = joint.app(value, index, NATIVE + 'BackingAllocationOOMAt')
            if [gate.named(value, x, local) for x in args] != ['σ', 'ops', 'allocate', 'allocator', 'owner', 'native', 'normalized', 'deterministic', 'growth', 'world']:
                raise ValueError('native frame changed the reached refusal observation')
        executed, local = choice.one_call(value, root, context, NATIVE + 'execution')
        if gate.named(value, executed[12], local) != 'deterministic':
            raise ValueError('backing completion changes the source ownership mode')
        if gate.named(value, executed[-2], local) != 'world':
            raise ValueError('backing completion rebases the source world')
        closed, local = choice.one_call(value, root, context, NATIVE + 'appendFailureState')
        if gate.named(value, closed[-1], local) != 'deterministic':
            raise ValueError('backing completion uses the wrong cleanup protocol')
    value = statements[CLAIMS[0]]
    fields, _, _ = gate.domains(value)
    if len(fields) != 15 or list(fields)[:14] != ['σ', 'ops', 'allocator', 'object', 'input', 'copied', 'before', 'allocated', 'middle', 'initial', 'created', 'cloned', 'id', 'cell']:
        raise ValueError('cleanup freshness assumes caller or final ownership')
    audit_interfaces(definitions)


def audit_interfaces(definitions):
    value = definitions[NATIVE + 'PreparationInput']['value']
    fields, root, context = gate.domains(value)
    if list(fields) != ['σ', 'ops', 'allocator', 'normalized', 'operands', 'remaining', 'deterministic', 'before', 'duplicated']:
        raise ValueError('preparation input added non-source premises')
    branch = joint.app(value, root, 'ite')
    eq = joint.app(value, branch[-4], 'Eq')
    if [gate.named(value, x, context) for x in eq[-2:]] != ['deterministic', 'Bool.true']:
        raise ValueError('preparation input inverted the native classifier')
    transferred = joint.app(value, branch[-1], 'And')
    for index, names in zip(transferred, (['operands', 'normalized'], ['duplicated', 'before'])):
        eq = joint.app(value, index, 'Eq')
        if [gate.named(value, x, context) for x in eq[-2:]] != names:
            raise ValueError('transferred preparation rebases its session or owner')
    take, local = choice.one_call(value, branch[-2], context, 'Compiler.Extraction.Memory.Arguments.Normalization.takeOwned')
    if gate.named(value, take[-1], local) != 'before':
        raise ValueError('duplicated preparation starts at a different session')
    value = definitions[NATIVE + 'BackingAllocationOOMAt']['value']
    fields, root, context = gate.domains(value)
    if list(fields) != ['σ', 'ops', 'allocate', 'allocator', 'owner', 'input', 'normalized', 'deterministic', 'growth', 'world']:
        raise ValueError('backing refusal added a final frame premise')
    selected, local = choice.one_call(value, root, context, NATIVE + 'PreparationInput')
    if [gate.named(value, x, local) for x in selected[:7]] != ['σ', 'ops', 'allocator', 'normalized', 'operands', 'remaining', 'deterministic']:
        raise ValueError('backing refusal observes a different source preparation')
    joint.path(value, selected[7], local, (gate.OWNED + 'World.memory',), 'world')
    if gate.named(value, selected[8], local) != 'duplicated':
        raise ValueError('backing refusal observes a different preparation result')
    value = definitions[NATIVE + 'BackingAllocationOOM']['value']
    _, root, context = gate.domains(value)
    args = joint.app(value, root, NATIVE + 'BackingAllocationOOMAt')
    if [gate.named(value, x, context) for x in args] != ['σ', 'ops', 'allocate', 'allocator', 'owner', 'input', 'normalized', 'Bool.true', 'growth', 'world']:
        raise ValueError('original deterministic refusal no longer specializes the selected observation')


def dependencies():
    return {
        CLAIMS[0]: {'Compiler.Extraction.AssemblyItem.Creation.create_verified', 'Compiler.Extraction.AssemblyClone.Physical.run_valid'},
        CLAIMS[1]: {NATIVE + 'PreparationInput', NATIVE + 'preparedFrameAt', NATIVE + 'preparationOwnershipAt'},
        CLAIMS[2]: {NATIVE + 'append_oom_reached', NATIVE + 'prepare_item', NATIVE + 'local_cleanup', CLAIMS[0],
            'Compiler.Extraction.Storage.insert_transferred_append_oom'},
        CLAIMS[3]: {CLAIMS[2], CLAIMS[1], 'Compiler.Extraction.RepresentativeArray.Append.Registered.first_refused'},
        CLAIMS[4]: {CLAIMS[2], CLAIMS[1], 'Compiler.Extraction.RepresentativeArray.Append.Registered.growing_oom'},
        CLAIMS[5]: {CLAIMS[3], CLAIMS[4]},
    }


def mutation_cases():
    def source(name):
        raw = (gate.harness.ROOT / 'lean/Compiler/Extraction' / (name + '.lean')).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)
    return (
        ('freshness', source('InternerInsertionItemPreparation'), (
            ('object-alias', 'id ≠ object ∧ ¬AssemblyItemDeinit.Touches', 'id = object ∧ ¬AssemblyItemDeinit.Touches', 1),
            ('source-payload-fresh', 'id ≠ object ∧ ¬AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload copied) id',
             'id ≠ object ∧ ¬AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload input) id', 1),
        )),
        ('execution', source('InternerInsertionAppendFailureModes'), (
            ('inverted-preparation', 'if deterministic then takeOwned', 'if !deterministic then takeOwned', 1),
            ('different-transferred-owner', 'else operands = normalized ∧', 'else operands = { normalized with address := normalized.address + 1 } ∧', 1),
            ('rewind-create-session', 'allocator input.item duplicated = (.ok object, allocated)',
             'allocator input.item world.memory = (.ok object, allocated)', 1),
            ('wrong-admission-guard', 'deterministic = true → Admitted ops.arguments', 'deterministic = false → Admitted ops.arguments', 1),
            ('wrong-execution-mode', 'normalized deterministic cells world growth', 'normalized (!deterministic) cells world growth', 1),
            ('double-normalized-cleanup', 'else (Storage.Cleanup.sequence [.value, .allocation, .arguments]).run',
             'else (Storage.Cleanup.sequence [.value, .allocation, .arguments, .normalized]).run', 1),
            ('rewind-history', '(memory after).memory.nextId = middle.memory.nextId', '(memory after).memory.nextId = world.memory.memory.nextId', 1),
            ('retain-argument-owner', 'Consumed normalized (memory after) ∧', '¬ Consumed normalized (memory after) ∧', 1),
            ('wrong-private-owner', 'PrivateFrame normalized world.memory (memory after) ∧',
             'PrivateFrame { normalized with address := normalized.address + 1 } world.memory (memory after) ∧', 1),
        )),
    )


def controls(output, env, lean):
    records = []
    for group, source, changes in mutation_cases():
        records += checked_controls(output, [mutation_check(output, 'backing-mode-' + group + '-unchanged', source, True, env, lean)])
        for name, before, after, count in changes:
            if source.count(before) != count:
                raise ValueError('ambiguous backing mode mutation: ' + name)
            records += checked_controls(output, [mutation_check(output, 'backing-mode-' + group + '-' + name,
                source.replace(before, after), False, env, lean)])
    return records
