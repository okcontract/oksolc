"""Audit native DIV's indexed initializer and shared binary composition.
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
UNARY = DISPATCH + 'UnaryPreservation.'
ALG = 'Compiler.Algebraic.'
SEM = OWNED + 'Semantic.'
FOLD = 'Compiler.Extraction.Folding.'
ASSOC = 'Compiler.Extraction.Associative.'
TESTS = gate.ITEM + 'NativeDivisionTests.'
MODULE = 'Compiler.Extraction.InternerNativeDivisionTests'
LOGICAL = ('shift_divisor_safe', 'binary_div_safe', 'div_simplify_safe')
NATIVE = ('binary_dispatch_verified', 'dispatcher_binary_verified', 'division_dispatch_verified',
          'dispatcher_division_verified', 'miss_division_verified')
REGRESSIONS = ('fixture_valid', 'reads_sound', 'inputs', 'shift_rule', 'initializer_outcome',
               'wrong_base_miss', 'wrong_arity_miss', 'base_read_failure', 'forwarded', 'preserved')
CLAIMS = [SHARED + name for name in ('shift_divisor_safe', 'binary_div_safe')]
CLAIMS += [DISPATCH + name for name in LOGICAL] + [NS + name for name in NATIVE] + [TESTS + name for name in REGRESSIONS]
INTERFACES = (SHARED + 'OperationRule', TESTS + 'reads', TESTS + 'loading', TESTS + 'fixture')


def audit(claims):
    required = {
        SHARED + 'shift_divisor_safe': {'Compiler.Extraction.Nested.binary_values', 'Compiler.Extraction.ShiftMasks.divisor_shift_value',
            SHARED + 'ReadRules.bind', ALG + 'BuilderLogic.bind', UNARY + 'some_safe'},
        SHARED + 'binary_div_safe': {SHARED + 'shift_divisor_safe', SHARED + 'algebraic_selected_safe',
            SHARED + 'ReadRules.bind', DISPATCH + 'constant_facts_reliable', DISPATCH + 'equal_facts_reliable'},
        DISPATCH + 'shift_divisor_safe': {SHARED + 'shift_divisor_safe', SHARED + 'logicalReadRules', UNARY + 'logicalInputs'},
        DISPATCH + 'binary_div_safe': {SHARED + 'binary_div_safe', SHARED + 'logicalBuilderRules', UNARY + 'logicalInputs'},
        DISPATCH + 'div_simplify_safe': {DISPATCH + 'binary_div_safe', DISPATCH + 'binary_simplify_safe'},
        NS + 'binary_dispatch_verified': {SHARED + 'constant_stage_safe', SHARED + 'or_next_safe',
            NS + 'binary_dispatch_result', SEM + 'NativeSafe.ensures'},
        NS + 'dispatcher_binary_verified': {NS + 'binary_dispatch_verified', NS + 'dispatcher_snapshot',
            OWNED + 'NativeGraph.Facts.reads', 'Compiler.Extraction.Interner.representative_reads_sound'},
        NS + 'division_dispatch_verified': {NS + 'binary_dispatch_verified', SHARED + 'binary_div_safe', SEM + 'readRules'},
        NS + 'dispatcher_division_verified': {NS + 'dispatcher_binary_verified', SHARED + 'binary_div_safe', NS + 'unary_inputs'},
        NS + 'miss_division_verified': {NS + 'dispatcher_division_verified', NS + 'miss_frame', NS + 'miss_words'},
        TESTS + 'preserved': {NS + 'division_dispatch_verified', TESTS + 'reads_sound', TESTS + 'inputs', TESTS + 'shift_rule',
            TESTS + 'fixture_valid', gate.ITEM + 'NativeAlgebraicTests.rules'},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('DIV lost shared composition: ' + name + ': ' + ', '.join(sorted(missing)))
    for name in CLAIMS:
        if not name.startswith(TESTS) and any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('production DIV depends on a fixture: ' + name)
    return {'checkedDependencies': sorted(required), 'logicalAndNativeDivisionProofShared': True,
            'comparisonAndDivisionCompositionShared': True, 'nativeIndexedLoadDerived': True,
            'completeDefaultDivisionConsumedByOwnedMiss': True, 'revisionSpecificDivisionVerified': False,
            'recursiveInductionVerified': False, 'completeStreamCorrespondenceVerified': False}


def audit_statements(rows, interfaces):
    statements = {row['theorem']: row['statement'] for row in rows}
    definitions = {row['name']: row for row in interfaces}
    value = definitions[SHARED + 'OperationRule']['value']
    fields, root, context = gate.domains(value)
    if not {'logic', 'constructors', 'debug', 'op', 'ids', 'values', 'value', 'before'} <= fields.keys():
        raise ValueError('operation rule lost a reached-state input')
    result = joint.app(value, root, ALG + 'BuilderLogic.safe')
    if gate.named(value, result[-2], context) != 'before':
        raise ValueError('operation rule changed reached state')
    action = joint.app(value, result[-3], ASSOC + 'Constructors.operation')
    for term, name in zip(action[-4:], ('constructors', None, 'ids', 'debug')):
        if name is not None and gate.named(value, term, context) != name:
            raise ValueError('operation rule changed callback input: ' + name)
    joint.path(value, action[-3], context, (FOLD + 'Op.opcode',), 'op')
    if not {ALG + 'BuilderLogic.valid', 'Compiler.Extraction.Cache.readArguments', FOLD + 'Op.eval'} <= gate.step.constants_below(value, value['root']):
        raise ValueError('operation rule lost validity or word evaluation')
    for name in ('shift_divisor_safe', 'binary_div_safe'):
        value = statements[SHARED + name]
        fields, root, context = gate.domains(value)
        if {'collected', 'selected', 'equal', 'leftRead', 'rightRead', 'model', 'outcome', 'loaded'} & fields.keys():
            raise ValueError('shared DIV assumes a selected branch or result')
        term, local = fields['inputs']
        args = joint.app(value, term, UNARY + 'Inputs')
        if [gate.named(value, x, local) for x in args[-4:]] != ['logic', 'reads', 'operand', 'before']:
            raise ValueError('DIV initializer law detached from actual source or state')
        term, local = fields['shift']
        args = joint.app(value, term, SHARED + 'OperationRule')
        if [gate.named(value, x, local) for x in args[-4:]] != ['logic', 'constructors', 'debug', FOLD + 'Op.shr']:
            raise ValueError('DIV child law is not actual SHR at caller debug')
        result = joint.app(value, root, ALG + 'BuilderLogic.safe')
        if gate.named(value, result[-2], context) != 'before':
            raise ValueError('shared DIV changed initial state')
        if name == 'binary_div_safe':
            action = joint.app(value, result[-3], DISPATCH + 'binaryStageWithInputs')[-10:]
            for index, actual in enumerate(('reads', 'constructors', 'usizeBits', DISPATCH + 'opDIV', 'left', 'right', 'debug', 'options', 'operand')):
                if gate.named(value, action[index], context) != actual:
                    raise ValueError('shared DIV changed binary input: ' + actual)
    common = {'σ', 'safety', 'owner', 'usizeBits', 'base', 'children', 'debug', 'source', 'address', 'native',
              'key', 'normalized', 'before', 'rows', 'data', 'capacity', 'left', 'right', 'facts', 'arguments',
              'instruction', 'other', 'expected', 'operation', 'valid', 'evaluated', 'ready', 'initial', 'proper', 'shift'}
    for name, extra in (('dispatcher_division_verified', set()),
                         ('miss_division_verified', {'frame', 'request', 'lookup', 'deterministic', 'active', 'frames', 'words'})):
        value = statements[NS + name]
        fields, root, context = gate.domains(value)
        if set(fields) != common | extra:
            raise ValueError('native DIV changed premises: ' + name + ': ' + str(sorted(set(fields) ^ (common | extra))))
        for field, (term, _) in fields.items():
            constants = gate.step.constants_below(value, term)
            if {NS + 'FramePost', SEM + 'NativeSafe', SEM + 'Ensures', UNARY + 'Inputs'} & constants:
                raise ValueError('native DIV assumes preservation or native load: ' + field)
            if any('Uniform.' in dep or dep.endswith('.projection') or dep.endswith('.SourceConstructorsAt') for dep in constants):
                raise ValueError('native DIV assumes a projected child model: ' + field)
        audit_builder_premise(value, fields['proper'])
        term, local = fields['shift']
        args = joint.app(value, term, SHARED + 'OperationRule')
        if [gate.named(value, x, local) for x in args[-3:]] != ['children', 'debug', FOLD + 'Op.shr']:
            raise ValueError('native DIV child callback changed')
        logic = joint.app(value, args[-4], SEM + 'builderLogic')
        if gate.named(value, logic[-1], local) != 'ready':
            raise ValueError('native DIV child lost the reached frame')
        meaning = joint.app(value, logic[-2], FOLD + 'wordMeaning')
        if gate.named(value, meaning[-1], local) != 'other':
            raise ValueError('native DIV child changed meaning')
        term, local = fields['instruction']
        args = joint.app(value, term, 'Eq')
        joint.path(value, args[-2], local, ('Compiler.Extraction.Cache.Key.instruction',), 'key')
        if gate.named(value, args[-1], local) != DISPATCH + 'opDIV':
            raise ValueError('native DIV changed actual key opcode')
        term, local = fields['arguments']
        args = joint.app(value, term, 'Eq')
        joint.path(value, args[-2], local, ('Compiler.Extraction.Cache.Key.arguments',), 'key')
        ids = args[-1]
        for argument in ('left', 'right'):
            args = joint.app(value, ids, 'List.cons')
            if gate.named(value, args[-2], local) != argument:
                raise ValueError('native DIV changed key operand order')
            ids = args[-1]
        joint.app(value, ids, 'List.nil')
        body = value['root']
        while value['nodes'][body][0] == 'forall':
            body = value['nodes'][body][4]
        required = {SEM + 'Ensures'} | ({NS + 'FramePost', OWNED + 'finish', 'Compiler.Extraction.Interner.FindCode.controlMiss'} if extra else set())
        if not required <= gate.step.constants_below(value, body):
            raise ValueError('native DIV lost actual owned execution')
    for name in ('binary_dispatch_verified', 'dispatcher_binary_verified'):
        value = statements[NS + name]
        fields, _, _ = gate.domains(value)
        term, local = fields['next']
        args, context = choice.one_call(value, term, local, DISPATCH + 'binaryStageWithInputs')
        expected = ['children', 'usizeBits', 'instruction', 'left', 'right', 'debug', DISPATCH + 'defaultOptions', 'operand']
        actual = [gate.named(value, x, context) for x in args[-9:-1]]
        if name == 'dispatcher_binary_verified':
            expected[2] = None
            expected[-1] = None
            operand = joint.app(value, args[-2], NS + 'operand')
            effects = joint.app(value, operand[-1], OWNED + 'Publication.Effects')
            if gate.named(value, effects[-1], context) != 'σ':
                raise ValueError('common binary stage changed native effect state')
            joint.path(value, args[-7], context, ('Compiler.Extraction.Cache.Key.instruction',), 'key')
        if any(want is not None and got != want for want, got in zip(expected, actual)):
            raise ValueError('common binary stage detached from actual dispatch: ' + name + ': ' + str(actual))
    for name in LOGICAL:
        fields, _, _ = gate.domains(statements[DISPATCH + name])
        if {'logic', 'rules', 'proper', 'ready', 'model', 'projection', 'inputs', 'shift'} & fields.keys():
            raise ValueError('logical DIV gained implementation premises')
    for name, parameters in {
        'initializer_outcome': {'before', 'fail'}, 'wrong_base_miss': {'before'}, 'wrong_arity_miss': {'before'},
        'base_read_failure': {'before', 'error'}, 'forwarded': {'before'},
        'preserved': {'other', 'memory', 'amount', 'base', 'numerator', 'fail'},
    }.items():
        fields, _, _ = gate.domains(statements[TESTS + name])
        if set(fields) != parameters:
            raise ValueError('DIV regression gained an outcome premise: ' + name)
    return {'actualShrChildAndDebugBound': True, 'actualIndexedLoadDerived': True,
            'actualKeyArgumentsAndOpcodeBound': True, 'localBinaryStageImmediatelyConsumed': True,
            'regressionsHaveNoOutcomePremise': True, 'recursiveInductionVerified': False}


def controls(output, env, lean):
    groups = (
        ('shared-division', 'Compiler.Extraction.DispatchDivisionProofs', (
            ('wrong-load-index', 'operand shift 0 amount', 'operand shift 1 amount', 1),
            ('reversed-shift-inputs', '[← operand shift 0 amount, left]', '[left, ← operand shift 0 amount]', 1),
            ('reversed-quotient', 'logic.read after id = some (a / b)', 'logic.read after id = some (b / a)', 2),
        )),
        ('native-division', 'Compiler.Extraction.InternerNativeDivisionDispatch', (
            ('wrong-argument-order', 'children usizeBits Dispatch.opDIV [left, right] debug operand address',
             'children usizeBits Dispatch.opDIV [right, left] debug operand address', 1),
        )),
        ('native-division-fixture', MODULE, (
            ('rewind-child-effect', 'else (before.mapEffects Nat.succ).mapEffects Nat.succ', 'else before.mapEffects Nat.succ', 1),
            ('load-failure-calls-child', 'if fail then before.mapEffects Nat.succ', 'if fail then (before.mapEffects Nat.succ).mapEffects Nat.succ', 1),
            ('wrong-load-address', 'source.address = 17', 'source.address = 18', 1),
            ('wrong-shr-order', 'ids = [1, 4]', 'ids = [4, 1]', 1),
            ('miss-as-zero', '(.ok none, before)', '(.ok (some 0), before)', 2),
            ('base-error-as-miss', '(.error (.language (match error with | .invalidId => .invalidId | .invalidOptional => .invalidOptional | .safetyFault => .safetyFault)), before)',
             '(.ok none, before)', 1),
        )),
    )
    records = []
    for label, module, changes in groups:
        original = source(module)
        records += checked_controls(output, [mutation_check(output, label + '-unchanged', original, True, env, lean)])
        for name, before, after, count in changes:
            if original.count(before) != count:
                raise ValueError('ambiguous DIV mutation: ' + name + ': ' + str(original.count(before)))
            records += checked_controls(output, [mutation_check(output, label + '-' + name,
                original.replace(before, after), False, env, lean)])
    return records
