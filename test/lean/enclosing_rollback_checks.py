"""Audit native rollback retention and its enclosing recursive consumer.
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
NATIVE = OWNED + 'Insertion.Native.'
GRAPH = OWNED + 'NativeGraph.Facts.'
BRANCHES = [NS + 'CallFrame.' + name for name in
            ('unrelocated_rollback_frame', 'growing_rollback_frame', 'publication_rollback_frame')]
CLAIMS = [GRAPH + 'logical_fields', NATIVE + 'insert_unpublished_projected', NS + 'CallFrame.storage_frame',
          NS + 'RollbackReturn.graph', NS + 'RollbackFrame.parent'] + BRANCHES
CLAIMS += [NS + 'Enclosing.' + name for name in ('rolled_back', 'insertion_rollback', 'insertion_rollback_derived')]
INTERFACES = (NS + 'RollbackFrame.mk', NS + 'RollbackReturn') + tuple(name.removesuffix('_frame') for name in BRANCHES)


def audit_statements(statements, definitions):
    from native_constructor_checks import expression
    from enclosing_frame_checks import insertion_gates, parent_at
    common = {'σ', 'safety', 'allocator', 'owner'}
    origin = {'source', 'request', 'values', 'taken', 'owned', 'lookup', 'origin'}
    parent = common | {'oldCapacity', 'oldData', 'rows', 'parentRows', 'source', 'values', 'normalized',
        'address', 'native', 'outer', 'original', 'before', 'after', 'childSource', 'request', 'childValues',
        'taken', 'owned', 'lookup', 'origin', 'initial', 'reached', 'facts', 'outerKept'}
    insertion = common | origin | {'parent', 'stack', 'before', 'world', 'initial', 'rows', 'address', 'native',
        'frame', 'ops', 'allocate', 'growth', 'meaning', 'key', 'admitted', 'aligned'}
    expected = {
        CLAIMS[0]: common | {'capacity', 'data', 'rows', 'world', 'facts', 'graph', 'representatives', 'table'},
        CLAIMS[1]: {'σ', 'ops', 'allocate', 'safety', 'allocator', 'container', 'source', 'address', 'meaning',
            'input', 'key', 'normalized', 'deterministic', 'before', 'rows', 'growth', 'backing', 'header',
            'projected', 'outcome', 'closed', 'after', 'unappended', 'unpublished', 'ran'},
        CLAIMS[2]: parent | {'afterNative', 'keys', 'retained'},
        CLAIMS[3]: common | {'rows', 'owned', 'before', 'actual', 'completed', 'reads'},
        CLAIMS[4]: parent | {'post'},
        CLAIMS[8]: common | origin | {'parent', 'stack', 'original', 'before', 'after', 'initial', 'reached',
            'rows', 'data', 'capacity', 'facts', 'post'},
        CLAIMS[9]: insertion | {'room', 'refused'},
        CLAIMS[10]: insertion | {'deterministic', 'remaining'},
    }
    for name in BRANCHES:
        old = definitions[name.removesuffix('_frame')]['type']
        old_fields, _, _ = gate.domains(old)
        value = statements[name]
        fields, root, context = gate.domains(value)
        if set(fields) != set(old_fields) - {'reads'}:
            raise ValueError('rollback added a premise or changed its source observations: ' + name)
        for field, (index, local) in fields.items():
            old_index, old_local = old_fields[field]
            if expression(value, index, local) != expression(old, old_index, old_local):
                raise ValueError('rollback changed an existing input: ' + name + '.' + field)
        result = joint.app(value, root, NS + 'RollbackReturn')
        if [gate.named(value, x, context) for x in result[:-1]] != ['σ', 'safety', 'allocator', 'owner', 'rows', 'normalized', 'world']:
            raise ValueError('rollback completion changed its original rows or owner')
        call = joint.app(value, result[-1], NATIVE + 'insert')
        if [gate.named(value, x, context) for x in call] != ['σ', 'ops', 'allocate', 'safety', 'allocator', 'owner',
                'source', 'address', 'meaning', 'native', 'key', 'normalized', 'Bool.true', 'growth', 'world']:
            raise ValueError('rollback completion describes a different native insertion')
    for name, wanted in expected.items():
        value = statements[name]
        fields, root, context = gate.domains(value)
        if set(fields) != wanted:
            raise ValueError('rollback changed its explicit premises: ' + name)
        for field, (index, _) in fields.items():
            constants = gate.step.constants_below(value, index)
            forbidden = {NS + 'Returns', NS + 'InvocationPost', NS + 'MissFrames', joint.PNS + 'JointPost',
                         'Compiler.Extraction.Interner.Represented'}
            if constants & forbidden or (field != 'remaining' and NS + 'FramePost' in constants):
                raise ValueError('rollback assumes a final recursive result: ' + name + '.' + field)
        if name in (CLAIMS[2], CLAIMS[4]):
            args = joint.app(value, root, NS + 'CallFrame')
            if [gate.named(value, x, context) for x in args] != ['σ', 'safety', 'allocator', 'owner', 'parentRows',
                    'source', 'values', 'normalized', 'address', 'native', 'outer', 'after']:
                raise ValueError('rollback lost the reached parent geometry')
        if name == CLAIMS[8] and gate.named(value, parent_at(value, root, context), context) != 'after':
            raise ValueError('rollback rewinds the enclosing predicate')
        if name in CLAIMS[9:]:
            args = joint.app(value, root, NS + 'FramePost')
            choice.one_call(value, args[-1], context, OWNED + 'finish')
        if name == CLAIMS[10]:
            index, local = fields['remaining']
            index, local = insertion_gates(value, index, local, 'deterministic', published=True, refused=True, transferred=True)
            final = value['root']
            while value['nodes'][final][0] == 'forall':
                final = value['nodes'][final][4]
            if expression(value, index, local) != expression(value, final, context[:-1]):
                raise ValueError('rollback residual and derived frame concern different executions')
    audit_frame(definitions, statements)


def audit_frame(definitions, statements):
    from native_constructor_checks import expression
    value = definitions[NS + 'RollbackFrame.mk']['type']
    fields, root, context = gate.domains(value)
    parameters = ['σ', 'safety', 'allocator', 'owner', 'oldData', 'oldCapacity', 'rows', 'owned', 'before', 'after']
    if list(fields) != parameters + ['native', 'projected', 'keys', 'retained', 'consumed']:
        raise ValueError('rollback frame changed its postconditions')
    args = joint.app(value, root, NS + 'RollbackFrame')
    if [gate.named(value, x, context) for x in args] != parameters:
        raise ValueError('rollback frame changed its indices')
    storage = statements[NS + 'CallFrame.storage_frame']
    storage_fields, _, _ = gate.domains(storage)
    for field, target in (('native', 'afterNative'), ('keys', 'keys'), ('retained', 'retained')):
        index, local = fields[field]
        other, other_local = storage_fields[target]
        if expression(value, index, local) != expression(storage, other, other_local):
            raise ValueError('rollback discards native storage retention: ' + field)
    index, local = fields['projected']
    equal = joint.app(value, index, 'Eq')
    joint.path(value, equal[-2], local, (OWNED + 'World.graph',), 'after')
    update = value['nodes'][equal[-1]]
    if update[0] != 'let':
        raise ValueError('rollback projection lost its original graph')
    joint.path(value, update[3], local, (OWNED + 'World.graph',), 'before')
    local = local + [update[1]]
    heap = joint.app(value, update[4], 'Compiler.Extraction.Interner.Heap.mk')
    if len(heap) != 4:
        raise ValueError('rollback projection changed graph fields')
    read = joint.app(value, heap[0], 'Compiler.Extraction.Storage.readValue')
    if gate.named(value, read[-1], local) != 'rows':
        raise ValueError('rollback projected different native rows')
    for term, field in zip(heap[1:], ('table', 'representatives', 'allocationCursor')):
        joint.path(value, term, local, ('Compiler.Extraction.Interner.Heap.' + field,), update[1])
    index, local = fields['consumed']
    args = joint.app(value, index, 'Compiler.Extraction.Memory.Arguments.Normalization.Consumed')
    if gate.named(value, args[-2], local) != 'owned':
        raise ValueError('rollback consumes a different owner')
    joint.path(value, args[-1], local, (OWNED + 'World.memory',), 'after')
    value = definitions[NS + 'RollbackReturn']['value']
    fields, root, context = gate.domains(value)
    if list(fields) != ['σ', 'safety', 'allocator', 'owner', 'rows', 'owned', 'before', 'actual']:
        raise ValueError('rollback return added an admission premise')
    result, remainder = joint.app(value, root, 'And')
    equal = joint.app(value, result, 'Eq')
    joint.path(value, equal[-2], context, ('Prod.fst',), 'actual')
    error = joint.app(value, equal[-1], 'Except.error')
    language = joint.app(value, error[-1], OWNED + 'Fault.language')
    if gate.named(value, language[-1], context) != 'Compiler.Extraction.Interner.Error.outOfMemory':
        raise ValueError('rollback return changed its ordinary failure')
    for _ in range(3):
        exists = joint.app(value, remainder, 'Exists')
        binder = value['nodes'][exists[-1]]
        if binder[0] != 'lambda':
            raise ValueError('rollback return lost reached storage witnesses')
        context, remainder = context + [binder[1]], binder[4]
    facts, post = joint.app(value, remainder, 'And')
    native = joint.app(value, facts, OWNED + 'NativeGraph.Facts')
    frame = joint.app(value, post, NS + 'RollbackFrame')
    appended = joint.app(value, native[-1], 'HAppend.hAppend')
    if [gate.named(value, x, context) for x in appended[-2:]] != ['rows', context[-3]]:
        raise ValueError('rollback return lost the original row prefix')
    if [gate.named(value, x, context) for x in native[:-1]] != ['σ', 'safety', 'allocator', 'owner', context[-2], context[-1], 'before']:
        raise ValueError('rollback return lost its original native storage')
    if [gate.named(value, x, context) for x in frame[:6]] != ['σ', 'safety', 'allocator', 'owner', context[-2], context[-1]]:
        raise ValueError('rollback return rebound its storage witnesses')
    if expression(value, native[-1], context) != expression(value, frame[6], context):
        raise ValueError('rollback return changes reached rows')
    if [gate.named(value, x, context) for x in frame[7:-1]] != ['owned', 'before']:
        raise ValueError('rollback return rebound its private owner or initial world')
    joint.path(value, frame[-1], context, ('Prod.snd',), 'actual')


def dependencies():
    return {
        CLAIMS[0]: {OWNED + 'NativeGraph.Facts'},
        CLAIMS[1]: {NATIVE + 'checkedExecution_read', OWNED + 'Insertion.projected'},
        CLAIMS[2]: {OWNED + 'Caller.Origin.freshNative', OWNED + 'Caller.Origin.fresh', OWNED + 'ArraySource.storage',
            'Compiler.Extraction.AssemblyClone.NativeFields.Represents.storage'},
        CLAIMS[3]: {NS + 'RollbackFrame.projected', NS + 'RollbackFrame.consumed'},
        CLAIMS[4]: {CLAIMS[2]},
        BRANCHES[0]: {NATIVE + 'unrelocated_publication_oom_reached', CLAIMS[1], GRAPH + 'frame_storage'},
        BRANCHES[1]: {NATIVE + 'growing_publication_oom_reached', CLAIMS[1], GRAPH + 'frame_storage'},
        BRANCHES[2]: set(BRANCHES[:2]),
        CLAIMS[8]: {CLAIMS[4], NS + 'Enclosing.rec'},
        CLAIMS[9]: {BRANCHES[2], CLAIMS[8], OWNED + 'finish_handoff'},
        CLAIMS[10]: {NS + 'Enclosing.insertion_derived', NS + 'Enclosing.insertion_transferred', CLAIMS[9]},
    }


def mutations():
    return (
        ('wrong-refusal-exclusion', '(deterministic = true → ¬ Insertion.Native.RefusedObservation',
         '(deterministic = false → ¬ Insertion.Native.RefusedObservation', 2),

    )


def mutation_cases():
    def source(name):
        raw = (gate.harness.ROOT / 'lean/Compiler/Extraction' / (name + '.lean')).read_text()
        return '\n'.join(line for line in raw.splitlines() if line.startswith('import ')) + '\n' + (
            'set_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw))
    return (
        ('storage', source('InternerNativeParentRelease'), (
            ('omit-native-retention', 'after.memory.memory.heap.lookup id = some cell ∧',
             'before.memory.memory.heap.lookup id = some cell ∧', 1),
            ('omit-registry-retention', 'after.memory.heap id = before.memory.heap id)',
             'before.memory.heap id = before.memory.heap id)', 1),
            ('exclude-empty-backing', '(oldCapacity ≠ 0 → id ≠ oldData.allocation)', '(id ≠ oldData.allocation)', 3),
            ('exclude-empty-owner', '(owned.items ≠ [] → id ≠ owned.address)', '(id ≠ owned.address)', 3),
            ('rebase-source-geometry', 'reached.arraySource.storage facts', 'initial.arraySource.storage facts', 1),
            ('rebase-item-geometry', 'reached.2.1.storage facts', 'initial.2.1.storage facts', 1),
        )),
        ('frame', source('InternerNativeRollbackFrame'), (
            ('wrong-normalized-owner', 'Consumed owned after.memory', 'Consumed { owned with address := owned.address + 1 } after.memory', 1),
            ('change-allocation-cursor', 'with read := Storage.readValue rows }',
             'with read := Storage.readValue rows, allocationCursor := 0 }', 1),
            ('rewind-outer', '(outerKept : outer after)', '(outerKept : outer before)', 1),
        )),
    )


def controls(output, env, lean):
    records = []
    for group, source, changes in mutation_cases():
        records += checked_controls(output, [mutation_check(output, 'enclosing-rollback-' + group + '-unchanged', source, True, env, lean)])
        for name, before, after, count in changes:
            if source.count(before) != count:
                raise ValueError('ambiguous rollback frame mutation: ' + name)
            records += checked_controls(output, [mutation_check(output, 'enclosing-rollback-' + group + '-' + name,
                source.replace(before, after), False, env, lean)])
    return records
