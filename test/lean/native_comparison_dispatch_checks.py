"""Audit shared comparison preservation consumed by the native owned miss.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
import constructor_replay_choice_checks as choice
from native_algebraic_dispatch_checks import source, audit_builder_premise
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check

NS, OWNED = gate.NS, gate.OWNED
DISPATCH = 'Compiler.Extraction.Dispatch.'
SHARED = DISPATCH + 'Preservation.'
ALG = 'Compiler.Algebraic.'
SEM = OWNED + 'Semantic.'
FOLD = 'Compiler.Extraction.Folding.'
TESTS = gate.ITEM + 'NativeComparisonTests.'
MODULE = 'Compiler.Extraction.InternerNativeComparisonTests'
LOGICAL = ('algebraic_selected_safe', 'binary_comparison_safe', 'comparison_word_value', 'comparison_simplify_safe')
NATIVE = ('binary_dispatch_result', 'comparison_dispatch_verified', 'dispatcher_comparison_verified', 'miss_comparison_verified')
REGRESSIONS = ('reads_sound', 'equal_outcome', 'unequal_miss', 'constant_table_oom', 'second_read_failure', 'preserved')
CLAIMS = [SHARED + name for name in ('algebraic_selected_safe', 'binary_comparison_safe')]
CLAIMS += [DISPATCH + name for name in LOGICAL] + [NS + name for name in NATIVE] + [TESTS + name for name in REGRESSIONS]
INTERFACES = (SHARED + 'logicalBuilderRules', DISPATCH + 'BooleanOperation', TESTS + 'reads', TESTS + 'rightFailure')


def audit(claims):
    required = {
        SHARED + 'algebraic_selected_safe': {DISPATCH + 'selected_word_value', ALG + 'BuilderRules.replacement',
                                           ALG + 'BuilderLogic.bind', ALG + 'BuilderLogic.pure'},
        DISPATCH + 'algebraic_selected_safe': {SHARED + 'algebraic_selected_safe', SHARED + 'logicalBuilderRules'},
        SHARED + 'binary_comparison_safe': {SHARED + 'algebraic_selected_safe', SHARED + 'ReadRules.bind',
            DISPATCH + 'constant_facts_reliable', DISPATCH + 'equal_facts_reliable', ALG + 'BuilderRules.constant'},
        DISPATCH + 'binary_comparison_safe': {SHARED + 'binary_comparison_safe', SHARED + 'logicalReadRules', SHARED + 'logicalBuilderRules'},
        DISPATCH + 'comparison_simplify_safe': {DISPATCH + 'binary_comparison_safe', DISPATCH + 'comparison_word_value', DISPATCH + 'binary_simplify_safe'},
        NS + 'algebraic_dispatch_result': {NS + 'binary_dispatch_result'},
        NS + 'algebraic_dispatch_verified': {SHARED + 'algebraic_selected_safe', NS + 'algebraic_dispatch_result'},
        NS + 'binary_dispatch_result': {DISPATCH + 'simplifyOptionsWithInputs', DISPATCH + 'constantStage', DISPATCH + 'binaryStageWithInputs'},
        NS + 'comparison_dispatch_verified': {NS + 'binary_dispatch_verified', SHARED + 'binary_comparison_safe',
            SEM + 'readRules', DISPATCH + 'comparison_word_value'},
        NS + 'dispatcher_comparison_verified': {NS + 'dispatcher_binary_verified', SHARED + 'binary_comparison_safe',
            DISPATCH + 'comparison_word_value'},
        NS + 'miss_comparison_verified': {NS + 'dispatcher_comparison_verified', NS + 'miss_frame', NS + 'miss_words'},
        TESTS + 'preserved': {NS + 'comparison_dispatch_verified', TESTS + 'reads_sound',
                             gate.ITEM + 'NativeAlgebraicTests.rules', gate.ITEM + 'NativeAlgebraicTests.fixture_valid'},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('comparison proof lost shared composition: ' + name + ': ' + ', '.join(sorted(missing)))
    for name in CLAIMS:
        if not name.startswith(TESTS) and any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('production comparison depends on a fixture: ' + name)
    return {'checkedDependencies': sorted(required), 'logicalAndNativeComparisonProofShared': True,
            'bothTablesUseSharedReplacementProof': True, 'fullFoldingPrefixConsumed': True,
            'completeComparisonConsumedByOwnedMiss': True, 'recursiveInductionVerified': False,
            'completeStreamCorrespondenceVerified': False}


def audit_statements(rows, interfaces):
    statements = {row['theorem']: row['statement'] for row in rows}
    definitions = {row['name']: row for row in interfaces}
    value = definitions[DISPATCH + 'BooleanOperation']['value']
    _, root, context = gate.domains(value)
    def members(index):
        head, args = gate.applied(value, index)
        if head[:2] == ['const', 'Or']:
            return members(args[0]) + members(args[1])
        args = joint.app(value, index, 'Eq')
        if gate.named(value, args[-2], context) != 'op':
            raise ValueError('comparison membership lost its actual opcode')
        return [gate.named(value, args[-1], context)]
    if set(members(root)) != {FOLD + 'Op.' + name for name in ('eq', 'lt', 'slt', 'gt', 'sgt')}:
        raise ValueError('comparison scope is not exactly the five supported operations')
    value = statements[SHARED + 'binary_comparison_safe']
    fields, root, context = gate.domains(value)
    if {'collected', 'selected', 'equal', 'leftRead', 'rightRead', 'model', 'outcome', 'inputs'} & fields.keys():
        raise ValueError('shared comparison assumes a read, branch or operand outcome')
    result = joint.app(value, root, ALG + 'BuilderLogic.safe')
    if gate.named(value, result[-2], context) != 'before':
        raise ValueError('shared comparison changed its initial state')
    action = joint.app(value, result[-3], DISPATCH + 'binaryStageWithInputs')[-10:]
    for index, name in ((0, 'reads'), (1, 'constructors'), (2, 'usizeBits'), (4, 'left'), (5, 'right'),
                        (6, 'debug'), (7, 'options'), (8, 'operand')):
        if gate.named(value, action[index], context) != name:
            raise ValueError('shared comparison changed the actual input: ' + name)
    joint.path(value, action[3], context, (FOLD + 'Op.opcode',), 'op')
    call, local = choice.one_call(value, result[-1], context, FOLD + 'Op.value')
    if [gate.named(value, x, local) for x in call[:3]] != ['op', 'a', 'b']:
        raise ValueError('comparison word postcondition changed operand order')
    common = {'σ', 'safety', 'owner', 'usizeBits', 'base', 'children', 'debug', 'source', 'address', 'native',
              'key', 'normalized', 'before', 'rows', 'data', 'capacity', 'left', 'right', 'op', 'comparison',
              'facts', 'arguments', 'instruction', 'other', 'expected', 'operation', 'valid', 'evaluated',
              'ready', 'initial', 'proper'}
    for name, extra in (('dispatcher_comparison_verified', set()),
                         ('miss_comparison_verified', {'frame', 'request', 'lookup', 'deterministic', 'active', 'frames', 'words'})):
        value = statements[NS + name]
        fields, root, context = gate.domains(value)
        if set(fields) != common | extra:
            raise ValueError('native comparison changed its premises: ' + name + ': ' + str(sorted(set(fields) ^ (common | extra))))
        for field, (term, _) in fields.items():
            constants = gate.step.constants_below(value, term)
            if any('Uniform.' in dep or dep.endswith('.projection') or dep.endswith('.SourceConstructorsAt') for dep in constants):
                raise ValueError('native comparison assumes projected child correspondence: ' + field)
            if {NS + 'FramePost', SEM + 'NativeSafe', SEM + 'Ensures', ALG + 'zigApply'} & constants:
                raise ValueError('native comparison assumes its final preservation: ' + field)
        audit_builder_premise(value, fields['proper'])
        term, local = fields['comparison']
        args = joint.app(value, term, DISPATCH + 'BooleanOperation')
        if gate.named(value, args[-1], local) != 'op':
            raise ValueError('native comparison changed its scope witness')
        term, local = fields['instruction']
        args = joint.app(value, term, 'Eq')
        joint.path(value, args[-2], local, ('Compiler.Extraction.Cache.Key.instruction',), 'key')
        joint.path(value, args[-1], local, (FOLD + 'Op.opcode',), 'op')
        term, local = fields['arguments']
        args = joint.app(value, term, 'Eq')
        joint.path(value, args[-2], local, ('Compiler.Extraction.Cache.Key.arguments',), 'key')
        ids = args[-1]
        for argument in ('left', 'right'):
            args = joint.app(value, ids, 'List.cons')
            if gate.named(value, args[-2], local) != argument:
                raise ValueError('native comparison changed its actual key arguments')
            ids = args[-1]
        joint.app(value, ids, 'List.nil')
        required = {SEM + 'Ensures'}
        if extra:
            required |= {NS + 'FramePost', OWNED + 'finish', 'Compiler.Extraction.Interner.FindCode.controlMiss'}
        body = value['root']
        while value['nodes'][body][0] == 'forall':
            body = value['nodes'][body][4]
        if not required <= gate.step.constants_below(value, body):
            raise ValueError('native comparison lost actual execution composition')
    for name in LOGICAL:
        fields, _, _ = gate.domains(statements[DISPATCH + name])
        if {'logic', 'rules', 'proper', 'ready', 'model', 'projection'} & fields.keys():
            raise ValueError('logical comparison gained an implementation premise')
    for name, parameters in {
        'reads_sound': {'meaning', 'memory', 'value', 'knownZero'},
        'equal_outcome': {'before', 'literal', 'op', 'comparison'},
        'unequal_miss': {'before', 'op', 'comparison'}, 'constant_table_oom': {'before'},
        'second_read_failure': {'before', 'error', 'op', 'comparison'},
        'preserved': {'other', 'memory', 'value', 'op', 'comparison', 'knownZero', 'leftZero', 'sameIds'},
    }.items():
        fields, _, _ = gate.domains(statements[TESTS + name])
        if set(fields) != parameters:
            raise ValueError('comparison regression gained an outcome premise: ' + name)
    return {'allFiveComparisonOperationsBound': True, 'noSelectedReadOrBranchPremise': True,
            'actualKeyArgumentsAndOpcodeBound': True, 'actualBuilderAndCallerDebugBound': True,
            'noLogicalChildModelPremise': True, 'regressionsHaveNoOutcomePremise': True,
            'recursiveInductionVerified': False}


def controls(output, env, lean):
    groups = (
        ('shared-selection', 'Compiler.Extraction.DispatchAlgebraicProofs', (
            ('wrong-word', 'logic.read after id = some expected) := by\n  have same',
             'logic.read after id = some (expected + 1)) := by\n  have same', 1),
            ('wrong-child-order', 'exact correct.replacement before valid replacement left right a b lhs rhs',
             'exact correct.replacement before valid replacement right left a b lhs rhs', 1),
        )),
        ('shared-comparison', 'Compiler.Extraction.DispatchComparisonProofs', (
            ('reversed-word', 'logic.read after id = some (op.value a b 0)', 'logic.read after id = some (op.value b a 0)', 1),
        )),
        ('native-comparison', 'Compiler.Extraction.InternerNativeComparisonDispatch', (
            ('wrong-argument-order', 'children usizeBits op.opcode [left, right] debug operand address',
             'children usizeBits op.opcode [right, left] debug operand address', 1),
        )),
        ('native-comparison-fixture', MODULE, (
            ('signed-fallback-one', '| _ => .ok (some 0)', '| .slt | .sgt => .ok (some 1) | _ => .ok (some 0)', 1),
            ('rewind-effects', 'before.mapEffects Nat.succ', 'before', 2),
            ('equal-as-zero', '| .eq => .error (.language .outOfMemory)', '| .eq => .ok (some 0)', 1),
            ('miss-as-zero', '(.ok none, before)', '(.ok (some 0), before)', 1),
            ('second-read-as-miss', '(.error (.language (match error with | .invalidId => .invalidId | .invalidOptional => .invalidOptional | .safetyFault => .safetyFault)), before)',
             '(.ok none, before)', 1),
            ('table-oom-as-miss', '(.error (.language .outOfMemory), before.mapEffects Nat.succ)', '(.ok none, before)', 1),
        )),
    )
    records = []
    for label, module, changes in groups:
        original = source(module)
        records += checked_controls(output, [mutation_check(output, label + '-unchanged', original, True, env, lean)])
        for name, before, after, count in changes:
            if original.count(before) != count:
                raise ValueError('ambiguous comparison mutation: ' + name + ': ' + str(original.count(before)))
            records += checked_controls(output, [mutation_check(output, label + '-' + name,
                original.replace(before, after), False, env, lean)])
    return records
