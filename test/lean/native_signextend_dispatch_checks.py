"""Audit SIGNEXTEND's reached-state initializers and native frame connection.
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
SHIFT = 'Compiler.Extraction.ArithmeticShift.'
ASSOC = 'Compiler.Extraction.Associative.'
TESTS = gate.ITEM + 'NativeSignExtendTests.'
MODULE = 'Compiler.Extraction.InternerNativeSignExtendTests'
LOGICAL = ('signextend_shift_sub', 'signextend_index_add', 'signextend_nested_safe',
           'signextend_shift_safe', 'signextend_tail_safe', 'binary_signextend_safe')
NATIVE = ('inputs_of_projection', 'InputFrame.semantic_inputs', 'signextend_dispatch_verified',
          'dispatcher_signextend_verified', 'miss_signextend_verified')
REGRESSIONS = ('fixture_valid', 'reads_sound', 'inputs', 'operation_rule', 'sar_rule', 'nested_outcome',
               'first_child_oom', 'sar_outcome', 'large_index_keeps_right', 'malformed_miss',
               'index_read_failure', 'forwarded_after_constant', 'preserved')
CLAIMS = [SHARED + 'constant_left_operation_inputs_safe', DISPATCH + 'constant_left_operation_some_safe']
CLAIMS += [prefix + name for prefix in (SHARED, DISPATCH) for name in LOGICAL]
CLAIMS += [NS + name for name in NATIVE] + [TESTS + name for name in REGRESSIONS]
INTERFACES = (SHARED + 'SarRule', TESTS + 'reads', TESTS + 'fixture', TESTS + 'loading')


def audit(claims):
    required = {
        SHARED + 'constant_left_operation_inputs_safe': {ALG + 'BuilderLogic.bind', UNARY + 'some_safe'},
        DISPATCH + 'constant_left_operation_some_safe': {SHARED + 'constant_left_operation_inputs_safe'},
        SHARED + 'signextend_nested_safe': {SHARED + 'constant_left_operation_inputs_safe',
            DISPATCH + 'signextend_repeat_value', DISPATCH + 'signextend_min_value', 'Compiler.Extraction.Nested.binary_values'},
        SHARED + 'signextend_shift_safe': {DISPATCH + 'signextend_shr_value', ALG + 'BuilderLogic.bind',
            SHARED + 'signextend_shift_sub', SHARED + 'signextend_index_add'},
        SHARED + 'binary_signextend_safe': {SHARED + 'signextend_nested_safe', SHARED + 'signextend_tail_safe',
            SHARED + 'algebraic_selected_safe', DISPATCH + 'constant_facts_reliable', DISPATCH + 'equal_facts_reliable'},
        NS + 'inputs_of_projection': {DISPATCH + 'Effects.Inputs.queried'},
        NS + 'InputFrame.semantic_inputs': {NS + 'inputs_of_projection', NS + 'InputFrame.queries',
            OWNED + 'NativeGraph.Facts.operand_after_append'},
        NS + 'signextend_dispatch_verified': {NS + 'binary_dispatch_verified', SHARED + 'binary_signextend_safe', SEM + 'readRules'},
        NS + 'dispatcher_signextend_verified': {NS + 'dispatcher_binary_verified', SHARED + 'binary_signextend_safe', NS + 'InputFrame.semantic_inputs'},
        NS + 'miss_signextend_verified': {NS + 'dispatcher_signextend_verified', NS + 'miss_frame', NS + 'miss_words'},
        TESTS + 'preserved': {NS + 'signextend_dispatch_verified', TESTS + 'reads_sound', TESTS + 'inputs',
            TESTS + 'operation_rule', TESTS + 'sar_rule', TESTS + 'fixture_valid', gate.ITEM + 'NativeAlgebraicTests.rules'},
    }
    required.update({DISPATCH + name: {SHARED + name} for name in LOGICAL})
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('SIGNEXTEND lost shared composition: ' + name + ': ' + ', '.join(sorted(missing)))
    for name in CLAIMS:
        if not name.startswith(TESTS) and any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('production SIGNEXTEND depends on a fixture: ' + name)
    return {'checkedDependencies': sorted(required), 'logicalAndNativeSignextendProofShared': True,
            'postChildLoadUsesExistingAppendFrame': True, 'completeDefaultSignextendConsumedByOwnedMiss': True,
            'properChildContractsDerived': False, 'recursiveInductionVerified': False,
            'completeStreamCorrespondenceVerified': False}


def named_arguments(value, terms, context, expected, description):
    if [gate.named(value, term, context) for term in terms] != list(expected):
        raise ValueError('SIGNEXTEND changed ' + description)


def audit_statements(rows, interfaces):
    statements = {row['theorem']: row['statement'] for row in rows}
    definitions = {row['name']: row for row in interfaces}
    value = statements[SHARED + 'constant_left_operation_inputs_safe']
    fields, root, context = gate.domains(value)
    if set(fields) != {'State', 'Failure', 'Debug', 'logic', 'constructors', 'debug', 'op', 'operation',
                      'before', 'constant', 'value', 'expected', 'annotation', 'operand', 'constantSafe', 'input', 'actual', 'evaluated'}:
        raise ValueError('constant/load composition changed its local obligations')
    term, local = fields['input']
    args, local = choice.one_call(value, term, local, ALG + 'BuilderLogic.safe')
    named_arguments(value, args[-3:-1], local, ('operand', 'middle'), 'post-child initializer state')
    result = joint.app(value, root, ALG + 'BuilderLogic.safe')
    named_arguments(value, result[-2:-1], context, ('before',), 'constant/load initial state')
    for method, expected in (('constant', ('constructors', 'constant', 'debug')),
                              ('operation', ('constructors', None, None, 'debug'))):
        args, local = choice.one_call(value, result[-3], context, ASSOC + 'Constructors.' + method)
        for term, name in zip(args[-len(expected):], expected):
            if name is not None:
                named_arguments(value, [term], local, (name,), 'constant/load callback input')
    value = definitions[SHARED + 'SarRule']['value']
    fields, root, context = gate.domains(value)
    if not {'logic', 'constructors', 'debug', 'left', 'right', 'amount', 'word', 'before'} <= fields.keys():
        raise ValueError('SAR child lost a reached-state input')
    result = joint.app(value, root, ALG + 'BuilderLogic.safe')
    named_arguments(value, result[-2:-1], context, ('before',), 'SAR reached state')
    call = joint.app(value, result[-3], ASSOC + 'Constructors.operation')
    named_arguments(value, call[-4:-2], context, ('constructors', SHIFT + 'opcode'), 'SAR callback/opcode')
    named_arguments(value, call[-1:], context, ('debug',), 'SAR caller debug')
    ids = call[-2]
    for name in ('left', 'right'):
        args = joint.app(value, ids, 'List.cons')
        named_arguments(value, args[-2:-1], context, (name,), 'SAR operand order')
        ids = args[-1]
    joint.app(value, ids, 'List.nil')
    args, local = choice.one_call(value, result[-1], context, SHIFT + 'value')
    named_arguments(value, args[-2:], local, ('amount', 'word'), 'SAR word order')
    if not {ALG + 'BuilderLogic.valid', ALG + 'BuilderLogic.read'} <= gate.step.constants_below(value, value['root']):
        raise ValueError('SAR child lost reached validity or actual operand reads')
    for name in LOGICAL[2:]:
        value = statements[SHARED + name]
        fields, root, context = gate.domains(value)
        if {'collected', 'selected', 'equal', 'leftRead', 'rightRead', 'model', 'outcome', 'loaded'} & fields.keys():
            raise ValueError('shared SIGNEXTEND assumes a selected branch/result')
        term, local = fields['inputs']
        args, local = choice.one_call(value, term, local, UNARY + 'Inputs')
        named_arguments(value, args[-4:], local, ('logic', 'reads', 'operand', 'middle'), 'reached initializer law')
        result = joint.app(value, root, ALG + 'BuilderLogic.safe')
        named_arguments(value, result[-2:-1], context, ('before',), 'initial state')
        if name == 'binary_signextend_safe':
            action = joint.app(value, result[-3], DISPATCH + 'binaryStageWithInputs')[-10:]
            named_arguments(value, action[:-1], context,
                ('reads', 'constructors', 'usizeBits', DISPATCH + 'opSIGNEXTEND', 'left', 'right', 'debug', 'options', 'operand'),
                'complete binary-stage inputs')
    value = statements[NS + 'InputFrame.semantic_inputs']
    fields, root, context = gate.domains(value)
    if set(fields) != {'σ', 'safety', 'allocator', 'owner', 'rows', 'source', 'values', 'normalized',
                      'meaning', 'ready', 'framed', 'heap', 'projected', 'before', 'valid'}:
        raise ValueError('reached native load gained an outcome or constructor-model premise')
    args = joint.app(value, root, UNARY + 'Inputs')
    named_arguments(value, args[-1:], context, ('before',), 'native input state')
    storage = joint.app(value, args[-3], 'Compiler.Extraction.Nested.storageReads')
    named_arguments(value, storage[-1:], context, ('rows',), 'original query rows')
    joint.app(value, args[-2], NS + 'operand')
    common = {'σ', 'safety', 'owner', 'usizeBits', 'base', 'children', 'debug', 'source', 'sourceValues', 'address', 'native',
              'key', 'normalized', 'before', 'rows', 'data', 'capacity', 'left', 'right', 'facts', 'arguments',
              'instruction', 'other', 'expected', 'operation', 'valid', 'evaluated', 'ready', 'initial', 'proper', 'signextend', 'sar', 'framed'}
    for name, extra in (('dispatcher_signextend_verified', set()),
                         ('miss_signextend_verified', {'frame', 'request', 'lookup', 'deterministic', 'active', 'frames', 'words'})):
        value = statements[NS + name]
        fields, _, _ = gate.domains(value)
        if set(fields) != common | extra:
            raise ValueError('native SIGNEXTEND changed premises: ' + name + ': ' + str(sorted(set(fields) ^ (common | extra))))
        for field, (term, _) in fields.items():
            constants = gate.step.constants_below(value, term)
            if {NS + 'FramePost', SEM + 'NativeSafe', SEM + 'Ensures', UNARY + 'Inputs'} & constants:
                raise ValueError('native SIGNEXTEND assumes preservation or native load: ' + field)
            if any('Uniform.' in dep or dep.endswith('.projection') or dep.endswith('.SourceConstructorsAt') for dep in constants):
                raise ValueError('native SIGNEXTEND assumes a projected child model: ' + field)
        audit_builder_premise(value, fields['proper'], SHIFT + 'meaning')
        for field, rule, tail in (('signextend', 'OperationRule', ('children', 'debug', FOLD + 'Op.signextend')),
                                   ('sar', 'SarRule', ('children', 'debug'))):
            term, local = fields[field]
            args = joint.app(value, term, SHARED + rule)
            named_arguments(value, args[-len(tail):], local, tail, 'actual child callback')
            logic = joint.app(value, args[-len(tail)-1], SEM + 'builderLogic')
            named_arguments(value, logic[-1:], local, ('ready',), 'child reached frame')
            meaning = joint.app(value, logic[-2], SHIFT + 'meaning')
            named_arguments(value, meaning[-1:], local, ('other',), 'child meaning')
        term, local = fields['framed']
        args, context = choice.one_call(value, term, local, NS + 'InputFrame')
        named_arguments(value, args[-8:-7], context, ('safety',), 'frame safety')
        joint.path(value, args[-7], context, (gate.ITEM + 'ShiftInput.Context.allocator',), 'base')
        named_arguments(value, args[-6:], context, ('owner', 'rows', 'source', 'sourceValues', 'normalized', 'world'), 'frame source and reached world')
        term, local = fields['instruction']
        args = joint.app(value, term, 'Eq')
        joint.path(value, args[-2], local, ('Compiler.Extraction.Cache.Key.instruction',), 'key')
        named_arguments(value, args[-1:], local, (DISPATCH + 'opSIGNEXTEND',), 'actual key opcode')
        term, local = fields['arguments']
        args = joint.app(value, term, 'Eq')
        joint.path(value, args[-2], local, ('Compiler.Extraction.Cache.Key.arguments',), 'key')
        ids = args[-1]
        for argument in ('left', 'right'):
            args = joint.app(value, ids, 'List.cons')
            named_arguments(value, args[-2:-1], local, (argument,), 'actual key operand order')
            ids = args[-1]
        joint.app(value, ids, 'List.nil')
        body = value['root']
        while value['nodes'][body][0] == 'forall':
            body = value['nodes'][body][4]
        required = {SEM + 'Ensures'} | ({NS + 'FramePost', OWNED + 'finish', 'Compiler.Extraction.Interner.FindCode.controlMiss'} if extra else set())
        if not required <= gate.step.constants_below(value, body):
            raise ValueError('native SIGNEXTEND lost actual owned execution')
    for name in LOGICAL + ('constant_left_operation_some_safe',):
        fields, _, _ = gate.domains(statements[DISPATCH + name])
        if {'logic', 'rules', 'proper', 'ready', 'model', 'projection', 'inputs', 'sar', 'framed'} & fields.keys():
            raise ValueError('logical SIGNEXTEND gained implementation premises')
    for name, parameters in {
        'nested_outcome': {'before', 'fail'}, 'first_child_oom': {'before'}, 'sar_outcome': {'before', 'fail'},
        'large_index_keeps_right': {'before'}, 'malformed_miss': {'before'}, 'index_read_failure': {'before', 'error'},
        'forwarded_after_constant': {'before'}, 'preserved': {'other', 'memory', 'shifted', 'outer', 'inner', 'base', 'failureIndex'},
    }.items():
        fields, _, _ = gate.domains(statements[TESTS + name])
        if set(fields) != parameters:
            raise ValueError('SIGNEXTEND regression gained an outcome premise: ' + name)
    return {'actualChildrenAndCallerDebugBound': True, 'actualKeyArgumentsAndOpcodeBound': True,
            'postChildInputsDerivedFromReachedFrame': True, 'regressionsHaveNoOutcomePremise': True,
            'recursiveInductionVerified': False}


def controls(output, env, lean):
    groups = (
        ('shared-post-child-input', 'Compiler.Extraction.DispatchAlgebraicProofs', (
            ('reversed-initializers', '[← constructors.constant constant debug, ← operand]', '[← operand, ← constructors.constant constant debug]', 1),
        )),
        ('shared-signextend', 'Compiler.Extraction.DispatchSignExtendProofs', (
            ('wrong-nested-load', 'operand inner 1 value', 'operand inner 0 value', 2),
            ('wrong-minimum', 'if outerByte.toNat ≤ innerByte.toNat then outerByte else innerByte',
             'if outerByte.toNat ≤ innerByte.toNat then innerByte else outerByte', 2),
            ('reversed-sar-inputs', '[← operand shift 0 amountId, ← operand shift 1 baseId]',
             '[← operand shift 1 baseId, ← operand shift 0 amountId]', 1),
            ('wrong-shift-boundary', 'remaining.toNat / 8 = endIndex.toNat', 'remaining.toNat / 8 = index.toNat', 4),
        )),
        ('native-signextend', 'Compiler.Extraction.InternerNativeSignExtendDispatch', (
            ('wrong-argument-order', 'children usizeBits Dispatch.opSIGNEXTEND [left, right] debug operand address',
             'children usizeBits Dispatch.opSIGNEXTEND [right, left] debug operand address', 1),
        )),
        ('native-signextend-fixture', MODULE, (
            ('rewind-load-effect', 'if fail then (before.mapEffects Nat.succ).mapEffects Nat.succ', 'if fail then before.mapEffects Nat.succ', 1),
            ('first-child-failure-continues', '(.error (.language .outOfMemory), before.mapEffects Nat.succ) := rfl',
             '(.error (.language .outOfMemory), (before.mapEffects Nat.succ).mapEffects Nat.succ) := rfl', 1),
            ('second-load-failure-calls-child', '| some true => (before.mapEffects Nat.succ).mapEffects Nat.succ',
             '| some true => ((before.mapEffects Nat.succ).mapEffects Nat.succ).mapEffects Nat.succ', 1),
            ('load-before-constant', 'world.memory.effects = 1', 'world.memory.effects = 0', 1),
            ('wrong-load-address', 'source.address = 17', 'source.address = 18', 1),
            ('wrong-child-inputs', 'ids = [0, 2]', 'ids = [2, 0]', 1),
            ('large-index-as-miss', '(.ok (some 3), before)', '(.ok none, before)', 1),
            ('malformed-as-zero', '(.ok none, before)', '(.ok (some 0), before)', 1),
            ('read-error-as-miss', '(.error (.language (match error with | .invalidId => .invalidId | .invalidOptional => .invalidOptional | .safetyFault => .safetyFault)), before)',
             '(.ok none, before)', 1),
        )),
    )
    records = []
    for label, module, changes in groups:
        original = source(module)
        records += checked_controls(output, [mutation_check(output, label + '-unchanged', original, True, env, lean)])
        for name, before, after, count in changes:
            if original.count(before) != count:
                raise ValueError('ambiguous SIGNEXTEND mutation: ' + name + ': ' + str(original.count(before)))
            records += checked_controls(output, [mutation_check(output, label + '-' + name,
                original.replace(before, after), False, env, lean)])
    return records
