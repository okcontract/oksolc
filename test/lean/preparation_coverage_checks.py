"""Audit actual preparation coverage consumed by the shared native miss reducer.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
import constructor_replay_choice_checks as choice
from native_algebraic_dispatch_checks import source
from native_miss_frame_checks import named
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check

NS, OWNED = gate.NS, gate.OWNED
NATIVE = OWNED + 'Insertion.Native.'
STORAGE = 'Compiler.Extraction.Storage.'
CLAIMS = [STORAGE + 'insert_execution_preparation']
CLAIMS += [NATIVE + name for name in ('duplicate_observation', 'create_observation', 'clone_observation',
                                     'execution_preparation_coverage', 'insert_preparation_coverage')]
CLAIMS += [NS + 'Enclosing.insertion_prepared']
INTERFACES = (NATIVE + 'PreparationSuccessAt', NS + 'Enclosing.insertion_rollback_derived')


def audit(claims):
    required = {
        CLAIMS[0]: {STORAGE + 'Program.scope_completed', STORAGE + 'insertProgram'},
        CLAIMS[1]: {OWNED + 'Insertion.callbacks'},
        CLAIMS[2]: {'Compiler.Extraction.AssemblyItem.Creation.Insertion.operations'},
        CLAIMS[3]: {'Compiler.Extraction.AssemblyItem.Creation.NativeFields.operations',
                    'Compiler.Extraction.AssemblyClone.Physical.Insertion.operations'},
        CLAIMS[4]: set(CLAIMS[:4]) | {NATIVE + 'PreparationInput'},
        CLAIMS[5]: {CLAIMS[4], NATIVE + 'checkedExecution_read', NATIVE + 'body'},
        CLAIMS[6]: {CLAIMS[5], NS + 'Enclosing.insertion_rollback_derived', OWNED + 'finish_handoff'},
        NS + 'Enclosing.native_miss_frames': {CLAIMS[6]},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('preparation coverage lost source composition: ' + name + ': ' + ', '.join(sorted(missing)))
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('general preparation coverage depends on fixtures: ' + name)
    return {'checkedDependencies': sorted(required), 'ordinaryPreparationOutcomesCovered': True,
            'successfulPrefixDerivedInSharedReducer': True, 'backingAndPublicationCoverageComplete': False,
            'resourceAdmissionDerived': False, 'recursiveInductionVerified': False}


def audit_statements(rows, interfaces):
    from native_constructor_checks import expression
    statements = {row['theorem']: row['statement'] for row in rows}
    definitions = {row['name']: row for row in interfaces}
    value = definitions[NATIVE + 'PreparationSuccessAt']['value']
    fields, root, context = gate.domains(value)
    if list(fields) != ['σ', 'ops', 'allocator', 'input', 'normalized', 'deterministic', 'before']:
        raise ValueError('successful preparation added a non-source premise')
    for expected in ('operands', 'remaining', 'duplicated', 'object', 'allocated', 'copied', 'middle'):
        body = value['nodes'][joint.app(value, root, 'Exists')[-1]]
        if body[0] != 'lambda' or body[1] != expected:
            raise ValueError('successful preparation changed its source witnesses')
        context, root = context + [body[1]], body[4]
    selected, rest = joint.app(value, root, 'And')
    created, cloned = joint.app(value, rest, 'And')
    args = joint.app(value, selected, NATIVE + 'PreparationInput')
    named(value, args, context, ('σ', 'ops', 'allocator', 'normalized', 'operands', 'remaining', 'deterministic', 'before', 'duplicated'))
    for index, callee, incoming, output, reached in (
        (created, 'Compiler.Extraction.AssemblyItem.Creation.create', 'duplicated', 'object', 'allocated'),
        (cloned, 'Compiler.Extraction.AssemblyClone.Physical.run', 'allocated', 'copied', 'middle'),
    ):
        eq = joint.app(value, index, 'Eq')
        args = joint.app(value, eq[-2], callee)
        named(value, args[-1:], context, (incoming,))
        named(value, args[-3:-2], context, ('allocator',))
        response = joint.app(value, eq[-1], 'Prod.mk')
        named(value, response[-1:], context, (reached,))
        ok = joint.app(value, response[-2], 'Except.ok')
        named(value, ok[-1:], context, (output,))
    # Compare complete source calls to the existing backing-failure observation,
    # which uses exactly this preparation prefix with further append conditions.
    old = definitions[NATIVE + 'BackingAllocationOOMAt']['value']
    _, old_root, old_context = gate.domains(old)
    for callee in ('Compiler.Extraction.AssemblyItem.Creation.create', 'Compiler.Extraction.AssemblyClone.Physical.run'):
        args, local = choice.one_call(value, root, context, callee)
        prior, prior_local = choice.one_call(old, old_root, old_context, callee)
        if [expression(value, arg, local) for arg in args] != [expression(old, arg, prior_local) for arg in prior]:
            raise ValueError('successful preparation changed an actual allocation callback')

    common = {'σ', 'ops', 'allocate', 'safety', 'allocator', 'container', 'source', 'address', 'input',
              'key', 'normalized', 'rows', 'growth', 'meaning', 'deterministic', 'before', 'room', 'completed'}
    for name, extra in ((CLAIMS[4], {'outcome'}), (CLAIMS[5], {'data', 'projected', 'header'})):
        value = statements[name]
        fields, root, context = gate.domains(value)
        if set(fields) != common | extra:
            raise ValueError('preparation coverage gained a successful prefix, frame or allocation-admission premise')
        for branch, observation in zip(joint.app(value, root, 'Or'), ('PreparationOOMAt', 'PreparationSuccessAt')):
            args = joint.app(value, branch, NATIVE + observation)
            named(value, args[:-1], context, ('σ', 'ops', 'allocator', 'input', 'normalized', 'deterministic'))
            joint.path(value, args[-1], context, (OWNED + 'World.memory',), 'before')
        completion, local = fields['completed']
        eq = joint.app(value, completion, 'Eq')
        if name == CLAIMS[4]:
            ok = joint.app(value, eq[-1], 'Except.ok')
            named(value, ok[-1:], local, ('outcome',))
            first = joint.app(value, eq[-2], 'Prod.fst')
            joint.app(value, first[-1], 'Prod.fst')
        else:
            named(value, eq[-1:], local, ('Bool.true',))
            ordinary = joint.app(value, eq[-2], OWNED + 'ordinary')
            joint.app(value, ordinary[-1], 'Prod.fst')
        prior = statements[NATIVE + 'preparation_oom_execution_at']
        prior_fields, _, _ = gate.domains(prior)
        if expression(value, *fields['room']) != expression(prior, *prior_fields['room']):
            raise ValueError('coverage changed the existing native count bound')
        call_name = NATIVE + ('execution' if name == CLAIMS[4] else 'insert')
        args, local = choice.one_call(value, *fields['completed'], call_name)
        expected = ('σ', 'ops', 'allocate', 'safety', 'allocator', 'container', 'source', 'address', 'meaning',
                    'input', 'key', 'normalized', 'deterministic')
        named(value, args[:13], local, expected)
        named(value, args[13:], local, ('rows', 'before', 'growth') if name == CLAIMS[4] else ('growth', 'before'))

    old = definitions[NS + 'Enclosing.insertion_rollback_derived']['type']
    value = statements[CLAIMS[6]]
    previous, old_root, old_context = gate.domains(old)
    fields, root, context = gate.domains(value)
    if set(fields) != set(previous):
        raise ValueError('prepared reducer added a new top-level premise')
    for field in fields.keys() - {'remaining'}:
        if expression(value, *fields[field]) != expression(old, *previous[field]):
            raise ValueError('prepared reducer changed an original input: ' + field)
    if expression(value, root, context) != expression(old, old_root, old_context):
        raise ValueError('prepared reducer changed the original frame conclusion')
    index, local = fields['remaining']
    prior, prior_local = previous['remaining']
    for _ in range(6):
        node, old_node = value['nodes'][index], old['nodes'][prior]
        if node[0] != 'forall' or old_node[0] != 'forall':
            raise ValueError('prepared reducer lost an existing exclusion')
        if expression(value, node[3], local) != expression(old, old_node[3], prior_local):
            raise ValueError('prepared reducer changed an existing exclusion')
        index, local = node[4], local + [node[1]]
        prior, prior_local = old_node[4], prior_local + [old_node[1]]
    node = value['nodes'][index]
    if node[0] != 'forall':
        raise ValueError('prepared reducer did not supply a successful prefix')
    args = joint.app(value, node[3], NATIVE + 'PreparationSuccessAt')
    named(value, args[:-1], local, ('σ', 'ops', 'allocator', 'native', 'owned', 'deterministic'))
    joint.path(value, args[-1], local, (OWNED + 'World.memory',), 'world')
    if expression(value, node[4], local + [node[1]]) != expression(old, prior, prior_local):
        raise ValueError('prepared residual changed the actual insertion or its frame')
    return {'sourcePrefixAndReachedSessionsExact': True, 'ordinaryOutcomeRequired': True,
            'existingReducerInputsAndConclusionUnchanged': True, 'onlyDerivedPreparationAddedToResidual': True,
            'completeNativeInsertionVerified': False}


def controls(output, env, lean):
    groups = (
        ('control', 'Compiler.Extraction.StorageExecutionPolicy', (
            ('ignore-capacity', '⟨deterministic, true, fun _ => false⟩ calls {} before',
             '⟨deterministic, false, fun _ => false⟩ calls {} before', 2),
            ('skip-clone', '(clone.1 = .ok false ∨ clone.1 = .ok true)', '(clone.1 = .ok true)', 1),
        )),
        ('source', 'Compiler.Extraction.InternerInsertionPreparationCoverage', (
            ('rewind-create', 'allocator input.item duplicated = (.ok object, allocated)',
             'allocator input.item before = (.ok object, allocated)', 1),
            ('rewind-clone', 'AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle)\n',
             'AssemblyClone.Physical.run (observe ops.copy) allocator input duplicated = (.ok copied, middle)\n', 1),
            ('lose-oom', 'PreparationOOMAt ops allocator input normalized deterministic before.memory ∨\n      PreparationSuccessAt ops allocator input normalized deterministic before.memory := by\n  have checked :=',
             'False ∨\n      PreparationSuccessAt ops allocator input normalized deterministic before.memory := by\n  have checked :=', 1),
            ('no-ordinary-completion', '(completed : (execution ops allocate safety allocator container source address meaning input key normalized\n      deterministic rows before growth).1.1 = .ok outcome)',
             '(completed : (execution ops allocate safety allocator container source address meaning input key normalized\n      deterministic rows before growth).1.1 = (execution ops allocate safety allocator container source address meaning input key normalized\n      deterministic rows before growth).1.1)', 1),
            ('invert-ownership', 'PreparationSuccessAt ops allocator input normalized deterministic before.memory',
             'PreparationSuccessAt ops allocator input normalized (!deterministic) before.memory', 2),
            ('wrong-source-input', 'PreparationInput ops allocator normalized operands remaining deterministic before duplicated',
             'PreparationInput ops allocator normalized operands remaining (!deterministic) before duplicated', 1),
        )),
        ('consumer', 'Compiler.Extraction.InternerEnclosingPreparationCoverage', (
            ('wrong-prepared-allocator', 'PreparationSuccessAt ops allocator native owned deterministic world.memory',
             'PreparationSuccessAt ops (allocator + 1) native owned deterministic world.memory', 1),
            ('wrong-prepared-item', 'PreparationSuccessAt ops allocator native owned deterministic world.memory',
             'PreparationSuccessAt ops allocator { native with item := { native.item with data := native.item.data + 1 } } owned deterministic world.memory', 1),
            ('missing-no-oom', '(¬ Insertion.Native.PreparationOOMAt ops allocator native owned deterministic world.memory) →',
             '(¬ Insertion.Native.PreparationOOMAt ops allocator native owned (!deterministic) world.memory) →', 1),
        )),
    )
    records = []
    for group, module, changes in groups:
        code = source(module)
        for name, old, _, count in changes:
            if code.count(old) != count:
                raise ValueError('ambiguous preparation coverage mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'preparation-coverage-' + group + '-unchanged', code, True, env, lean)])
        for name, old, new, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'preparation-coverage-' + group + '-' + name,
                                                                 code.replace(old, new), False, env, lean)])
    return records
