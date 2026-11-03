"""Audit direct native constant-fold preservation without a projected child model.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
from assembly_item_creation_checks import checked_controls
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NS, OWNED = gate.NS, gate.OWNED
DISPATCH = 'Compiler.Extraction.Dispatch.'
MODULE = 'Compiler.Extraction.InternerNativeConstantDispatch'
CORE = ('ordinary_map', 'constant_dispatch_result', 'ensures_map', 'constant_dispatch_words',
        'dispatcher_constant_result', 'dispatcher_constant_verified', 'miss_constant_verified')
SHARED = (DISPATCH + 'folded_value', DISPATCH + 'constant_stage_safe')
FIXTURE = gate.ITEM + 'ConstantFoldTests.iszero_result'
CLAIMS = [NS + name for name in CORE] + list(SHARED) + [FIXTURE]


def audit(claims):
    required = {
        DISPATCH + 'folded_value': {DISPATCH + 'collected_values', DISPATCH + 'folding_found'},
        DISPATCH + 'constant_stage_safe': {DISPATCH + 'folded_value'},
        NS + 'constant_dispatch_result': {DISPATCH + 'constantStage', DISPATCH + 'simplifyWithInputs'},
        NS + 'constant_dispatch_words': {DISPATCH + 'folded_value', NS + 'constant_dispatch_result', NS + 'ensures_map'},
        NS + 'dispatcher_constant_result': {NS + 'dispatcher_snapshot', NS + 'constant_dispatch_result', OWNED + 'NativeGraph.Facts.reads'},
        NS + 'dispatcher_constant_verified': {NS + 'dispatcher_constant_result', NS + 'constant_dispatch_words',
                                             'Compiler.Extraction.Interner.representative_reads_sound'},
        NS + 'miss_constant_verified': {NS + 'dispatcher_constant_verified', NS + 'miss_frame', NS + 'miss_words'},
        FIXTURE: {NS + 'constant_dispatch_result', 'Compiler.Extraction.Folding.folding_correct'},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('constant dispatch lost shared reasoning: ' + name + ': ' + ', '.join(sorted(missing)))
    for name in CLAIMS[:-1]:
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('constant dispatch depends on fixture reasoning: ' + name)
    return {'checkedDependencies': sorted(required), 'logicalAndNativeFoldFactShared': True,
            'existingIszeroUsesGeneralDispatch': True, 'nativeMissConsumesDirectChildWords': True,
            'recursiveInductionVerified': False, 'completeStreamCorrespondenceVerified': False}


def audit_statements(rows, interfaces):
    statements = {row['theorem']: row['statement'] for row in rows}
    common = {'σ', 'safety', 'owner', 'usizeBits', 'base', 'children', 'debug', 'source', 'address', 'native',
              'key', 'normalized', 'before', 'rows', 'data', 'capacity', 'collectedValues', 'computed',
              'facts', 'bounded', 'nonempty', 'collected', 'folded'}
    semantic = {'other', 'expected', 'operation', 'valid', 'evaluated', 'ready', 'childFrame', 'childWords'}
    for name, parameters in (
        ('dispatcher_constant_result', common),
        ('dispatcher_constant_verified', common | semantic),
        ('miss_constant_verified', common | semantic | {'frame', 'initial', 'request', 'lookup', 'deterministic',
                                                       'selected', 'frames', 'words'}),
    ):
        statement = statements[NS + name]
        fields, conclusion, context = gate.domains(statement)
        if set(fields) != parameters:
            raise ValueError('native constant branch changed assumptions: ' + name + ': ' + str(sorted(set(fields) ^ parameters)))
        for field, (root, _) in fields.items():
            constants = gate.step.constants_below(statement, root)
            if any('Uniform.' in dep or dep.endswith('.projection') or dep.endswith('.SourceConstructorsAt')
                   or dep.endswith('.ConstructorsCorrect') for dep in constants):
                raise ValueError('native constant branch regained model correspondence: ' + name + '.' + field)
            if NS + 'FramePost' in constants:
                raise ValueError('native constant branch assumes final frame: ' + field)
            if OWNED + 'Semantic.Ensures' in constants and field != 'childWords':
                raise ValueError('native constant branch assumes parent preservation: ' + field)
        if OWNED + 'NativeGraph.Facts' not in gate.step.constants_below(statement, fields['facts'][0]):
            raise ValueError('native constant branch lost native read correspondence')
        if name.endswith('_verified'):
            audit_child(statement, fields)
        if name == 'miss_constant_verified':
            needed = {NS + 'FramePost', OWNED + 'Semantic.Ensures', 'Compiler.Extraction.Interner.FindCode.controlMiss',
                      OWNED + 'finish', OWNED + 'execution'}
            body = statement['root']
            while statement['nodes'][body][0] == 'forall':
                body = statement['nodes'][body][4]
            if not needed <= gate.step.constants_below(statement, body):
                raise ValueError('native constant branch lost completed owned-miss execution')
    return {'checkedNativeBranchAssumptions': True, 'actualChildWordAndReachedGraphBound': True,
            'nativeReadFactsRequired': True, 'nativeSuffixContractsRequired': True,
            'childSuccessAssumed': False, 'logicalChildModelRequired': False,
            'recursiveInductionVerified': False, 'completeStreamCorrespondenceVerified': False}


def audit_child(statement, fields):
    import constructor_joint_checks as joint
    from recursive_joint_entry_checks import applications
    for field in ('childFrame', 'childWords'):
        root, context = fields[field]
        calls = list(applications(statement, root, context, 'Compiler.Extraction.Associative.Constructors.constant'))
        if len(calls) != 2:
            raise ValueError('native constant branch lost child outcome or reached world: ' + field)
        for args, local in calls:
            if [gate.named(statement, x, local) for x in args[-4:]] != ['children', 'computed', 'debug', 'before']:
                raise ValueError('native constant branch rebound its actual child: ' + field)
    root, context = fields['childWords']
    args = joint.app(statement, root, OWNED + 'Semantic.Ensures')
    initial = joint.app(statement, args[-4], OWNED + 'World.graph')[-1]
    if gate.named(statement, initial, context) != 'before':
        raise ValueError('native constant child lost its initial graph')
    joint.app(statement, args[-3], 'Prod.fst')
    reached = joint.app(statement, args[-2], OWNED + 'World.graph')[-1]
    joint.app(statement, reached, 'Prod.snd')
    post = statement['nodes'][args[-1]]
    if post[:2] != ['lambda', 'id']:
        raise ValueError('native constant child post lost returned ID')
    post = statement['nodes'][post[4]]
    if post[:2] != ['lambda', 'after']:
        raise ValueError('native constant child post lost reached graph')
    equality = joint.app(statement, post[4], 'Eq')
    local = context + ['id', 'after']
    read = joint.app(statement, equality[-2], 'Compiler.Extraction.Interner.Heap.read')
    word = joint.app(statement, equality[-1], 'Option.some')
    if [gate.named(statement, x, local) for x in read[-2:]] != ['after', 'id'] or gate.named(statement, word[-1], local) != 'computed':
        raise ValueError('native constant child post lost actual returned word')
    root, context = fields['childFrame']
    node = statement['nodes'][root]
    if node[0] != 'forall':
        raise ValueError('native constant child frame lost ordinary guard')
    equality = joint.app(statement, node[3], 'Eq')
    if gate.named(statement, equality[-1], context) != 'Bool.true':
        raise ValueError('native constant child frame changed ordinary guard')
    result = joint.app(statement, equality[-2], OWNED + 'ordinary')[-1]
    joint.app(statement, result, 'Prod.fst')
    body = statement['nodes'][node[4]]
    local = context + [node[1]]
    if body[0] != 'app' or gate.named(statement, body[1], local) != 'ready':
        raise ValueError('native constant child frame lost reached predicate')
    joint.app(statement, body[2], 'Prod.snd')


def controls(output, env, lean):
    raw = (gate.harness.ROOT / ('lean/' + MODULE.replace('.', '/') + '.lean')).read_text()
    source = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
    source += '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)
    records = checked_controls(output, [mutation_check(output, 'native-fold-unchanged', source, True, env, lean)])
    changes = (
        ('erase-rejected-fault', 'ordinary (result.map f) = ordinary result', 'ordinary (result.map f) = true', 1),
        ('wrong-folded-child', '(children.constant computed debug before).1.map some',
         '(children.constant (computed + 1) debug before).1.map some', 3),
        ('rewind-child-world', '(children.constant computed debug before).2) := by', 'before) := by', 3),
        ('skip-arity-guard', 'key.arguments.length ≤ 3', 'key.arguments.length ≤ 4', 3),
        ('skip-nonempty-guard', '(nonempty : arguments ≠ [])', '(nonempty : True)', 2),
        ('wrong-child-post', '(fun id after => after.read id = some computed)',
         '(fun id after => after.read id = some (computed + 1))', 3),
        ('wrong-parent-word', 'key.eval (Folding.wordMeaning other) before.graph.read = some expected',
         'key.eval (Folding.wordMeaning other) before.graph.read = some (expected + 1)', 2),
        ('inactive-miss-branch', '(selected : (deterministic && (request.item.kind == 1)) = true)',
         '(selected : (deterministic && (request.item.kind == 1)) = false)', 1),
    )
    for name, before, after, count in changes:
        if source.count(before) != count:
            raise ValueError('ambiguous native fold mutation: ' + name + ': ' + str(source.count(before)))
        records += checked_controls(output, [mutation_check(output, 'native-fold-' + name,
            source.replace(before, after), False, env, lean)])
    return records
