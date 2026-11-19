"""Audit shared unary preservation and its native source-memory connection.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
import constructor_replay_choice_checks as choice
from native_algebraic_dispatch_checks import source
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check

NS, OWNED = gate.NS, gate.OWNED
DISPATCH = 'Compiler.Extraction.Dispatch.'
SHARED = DISPATCH + 'UnaryPreservation.'
PREFIX = DISPATCH + 'Preservation.'
SEM = OWNED + 'Semantic.'
TESTS = gate.ITEM + 'NativeUnaryTests.'
MODULE = 'Compiler.Extraction.InternerNativeUnaryTests'
LOGICAL = ('operation_some_safe', 'borrowed_operation_some_safe', 'operation_probe_safe',
           'unary_not_safe', 'unary_iszero_safe', 'unary_stage_safe', 'interner_unary_stage_safe')
GENERIC = ('some_safe', 'operation_probe_safe', 'unary_not_safe', 'unary_iszero_safe', 'unary_stage_safe')
NATIVE = ('unary_inputs', 'unary_dispatch_result', 'unary_dispatch_verified', 'dispatcher_unary_verified', 'miss_unary_verified')
REGRESSIONS = ('rules', 'fixture_valid', 'reads_sound', 'inputs', 'initializer_then_oom', 'preserved',
               'read_failure', 'unknown_miss', 'borrowed_stops')
CLAIMS = [DISPATCH + name for name in LOGICAL] + [SHARED + name for name in GENERIC]
CLAIMS += [NS + name for name in NATIVE] + [TESTS + name for name in REGRESSIONS]
INTERFACES = (PREFIX + 'ReadRules.mk', SHARED + 'Children.mk', SHARED + 'Inputs',
              PREFIX + 'logicalReadRules', SHARED + 'logicalChildren', SEM + 'readRules',
              TESTS + 'reads', TESTS + 'fixture', TESTS + 'loading', TESTS + 'borrowing')


def audit(claims):
    required = {
        DISPATCH + 'operation_some_safe': {SHARED + 'some_safe'},
        DISPATCH + 'borrowed_operation_some_safe': {SHARED + 'some_safe'},
        DISPATCH + 'operation_probe_safe': {SHARED + 'operation_probe_safe', SHARED + 'logicalChildren'},
        DISPATCH + 'unary_not_safe': {SHARED + 'unary_not_safe'},
        DISPATCH + 'unary_iszero_safe': {SHARED + 'unary_iszero_safe', SHARED + 'logicalChildren', SHARED + 'logicalInputs'},
        DISPATCH + 'unary_stage_safe': {SHARED + 'unary_stage_safe', SHARED + 'logicalChildren', SHARED + 'logicalInputs'},
        SHARED + 'operation_probe_safe': {'Compiler.Extraction.Nested.operation_values', SHARED + 'Children.borrowed'},
        SHARED + 'unary_iszero_safe': {DISPATCH + 'triple_iszero', DISPATCH + 'boolean_double_iszero',
            DISPATCH + 'equality_of_zero_test', SHARED + 'operation_probe_safe', 'Compiler.Algebraic.BuilderLogic.bind'},
        NS + 'unary_inputs': {OWNED + 'NativeGraph.Facts.operand'},
        NS + 'unary_dispatch_result': {DISPATCH + 'simplifyOptionsWithInputs', DISPATCH + 'unaryStageWithInputs'},
        NS + 'unary_dispatch_verified': {SHARED + 'unary_stage_safe', SEM + 'readRules',
            NS + 'singleton_dispatch_result', PREFIX + 'constant_stage_safe', PREFIX + 'or_next_safe', SEM + 'NativeSafe.ensures'},
        NS + 'dispatcher_unary_verified': {NS + 'dispatcher_snapshot', OWNED + 'NativeGraph.Facts.reads',
            'Compiler.Extraction.Interner.representative_reads_sound', NS + 'unary_inputs', NS + 'unary_dispatch_verified'},
        NS + 'miss_unary_verified': {NS + 'dispatcher_unary_verified', NS + 'miss_frame', NS + 'miss_words'},
        TESTS + 'initializer_then_oom': {NS + 'unary_dispatch_result'},
        TESTS + 'preserved': {NS + 'unary_dispatch_verified', TESTS + 'rules', TESTS + 'reads_sound',
            TESTS + 'fixture_valid', TESTS + 'inputs'},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('unary proof lost a shared/source connection: ' + name + ': ' + ', '.join(sorted(missing)))
    for name in CLAIMS:
        if not name.startswith(TESTS) and any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('production unary proof depends on a fixture: ' + name)
    return {'checkedDependencies': sorted(required), 'logicalAndNativeUnaryProofShared': True,
            'actualIndexedLoadDerived': True, 'nativeMissConsumesCompleteUnaryStage': True,
            'recursiveInductionVerified': False, 'completeStreamCorrespondenceVerified': False}


def audit_statements(rows, interfaces):
    statements = {row['theorem']: row['statement'] for row in rows}
    definitions = {row['name']: row for row in interfaces}
    value = definitions[SHARED + 'Children.mk']['type']
    fields, _, _ = gate.domains(value)
    for field, method, names in (
        ('operation', 'operation', [('constructors', None), ('op', 'Compiler.Extraction.Folding.Op.opcode'), ('ids', None), ('debug', None)]),
        ('borrowed', 'borrowedOperation', [('constructors', None), ('source', 'Compiler.Extraction.Storage.ArgumentSlice.address'),
            ('op', 'Compiler.Extraction.Folding.Op.opcode'), ('source', 'Compiler.Extraction.Storage.ArgumentSlice.items'), ('debug', None)]),
    ):
        root, local = fields[field]
        args, context = choice.one_call(value, root, local, 'Compiler.Extraction.Associative.Constructors.' + method)
        expected = args[-len(names):]
        for term, (name, projection) in zip(expected, names):
            actual = gate.named(value, term, context)
            if projection:
                joint.path(value, term, context, (projection,), name)
            elif actual != name:
                raise ValueError('unary child changed actual arguments: ' + field + ': ' + str(actual))
        required = {'Compiler.Algebraic.BuilderLogic.valid', 'Compiler.Algebraic.BuilderLogic.safe',
                    'Compiler.Extraction.Cache.readArguments', 'Compiler.Extraction.Folding.Op.eval'}
        if not required <= gate.step.constants_below(value, root):
            raise ValueError('unary children lost reached-state or word conditions')
    root, local = fields['borrowed']
    call, context = choice.one_call(value, root, local, 'Compiler.Extraction.Nested.Reads.operation')
    if [gate.named(value, term, context) for term in call[-3:]] != ['reads', 'id', 'queried']:
        raise ValueError('borrowed child no longer requires an actual source query')
    cursor, context = root, local[:]
    bound = False
    while value['nodes'][cursor][0] == 'forall':
        node = value['nodes'][cursor]
        if 'Compiler.Extraction.Nested.Reads.operation' in gate.step.constants_below(value, node[3]):
            equality = joint.app(value, node[3], 'Eq')
            observed = joint.app(value, equality[-1], 'Except.ok')
            selected = joint.app(value, observed[-1], 'Option.some')
            if gate.named(value, selected[-1], context) != 'source':
                raise ValueError('borrowed child query does not return the actual slice')
            bound = True
        context.append(node[1])
        cursor = node[4]
    if not bound:
        raise ValueError('borrowed child lacks its query equation')
    fields, _, _ = gate.domains(statements[NS + 'unary_inputs'])
    if set(fields) != {'σ', 'safety', 'allocator', 'owner', 'before', 'rows', 'data', 'capacity',
                      'facts', 'meaning', 'ready', 'initial', 'valid'}:
        raise ValueError('native indexed-load derivation added a load/outcome premise')
    for name in LOGICAL:
        fields, _, _ = gate.domains(statements[DISPATCH + name])
        if {'logic', 'rules', 'inputs', 'ready', 'model', 'projection'} & fields.keys():
            raise ValueError('logical unary wrapper added proof premises: ' + name)
    common = {'σ', 'safety', 'owner', 'usizeBits', 'base', 'children', 'debug', 'source', 'address', 'native',
              'key', 'normalized', 'before', 'rows', 'data', 'capacity', 'id', 'facts', 'arguments', 'constant',
              'other', 'expected', 'operation', 'valid', 'evaluated', 'ready', 'initial', 'proper'}
    for name, extra in (('dispatcher_unary_verified', set()),
                         ('miss_unary_verified', {'frame', 'request', 'lookup', 'deterministic', 'active', 'frames', 'words'})):
        statement = statements[NS + name]
        fields, _, _ = gate.domains(statement)
        if set(fields) != common | extra:
            raise ValueError('native unary branch changed assumptions: ' + name + ': ' + str(sorted(set(fields) ^ (common | extra))))
        for field, (root, _) in fields.items():
            constants = gate.step.constants_below(statement, root)
            if any('Uniform.' in dep or dep.endswith('.projection') or dep.endswith('.SourceConstructorsAt') for dep in constants):
                raise ValueError('native unary branch assumes a projected child model: ' + field)
            if {NS + 'FramePost', SEM + 'NativeSafe', SEM + 'Ensures', SHARED + 'Inputs'} & constants:
                raise ValueError('native unary branch assumes final preservation or an underived input: ' + field)
        root, local = fields['proper']
        args = joint.app(statement, root, SHARED + 'Children')
        if [gate.named(statement, arg, local) for arg in args[-2:]] != ['children', 'debug']:
            raise ValueError('native unary branch changed actual child callbacks or debug')
        source_reads = joint.app(statement, args[-3], 'Compiler.Extraction.Nested.storageReads')
        if gate.named(statement, source_reads[-1], local) != 'rows':
            raise ValueError('native unary borrowed calls are not tied to reached graph rows')
        logic = joint.app(statement, args[-4], SEM + 'builderLogic')
        if gate.named(statement, logic[-1], local) != 'ready':
            raise ValueError('native unary child contract dropped reached caller validity')
        meaning = joint.app(statement, logic[-2], 'Compiler.Extraction.Folding.wordMeaning')
        if gate.named(statement, meaning[-1], local) != 'other':
            raise ValueError('native unary child contract changed word meaning')
        body = statement['root']
        while statement['nodes'][body][0] == 'forall':
            body = statement['nodes'][body][4]
        required = {SEM + 'Ensures'}
        if name.startswith('miss_'):
            required |= {NS + 'FramePost', OWNED + 'finish', 'Compiler.Extraction.Interner.FindCode.controlMiss'}
        if not required <= gate.step.constants_below(statement, body):
            raise ValueError('native unary result lost actual owned execution')
    for name, parameters in {
        'rules': {'meaning', 'reads'}, 'fixture_valid': {'meaning', 'memory'},
        'reads_sound': {'other', 'memory'}, 'inputs': {'meaning', 'before', 'valid'},
        'initializer_then_oom': {'before'}, 'preserved': {'other', 'memory'},
        'read_failure': {'before', 'error'}, 'unknown_miss': {'before'}, 'borrowed_stops': {'before'},
    }.items():
        fields, _, _ = gate.domains(statements[TESTS + name])
        if set(fields) != parameters:
            raise ValueError('native unary regression gained an outcome premise: ' + name)
    return {'onlyCallerDebugAndQueryBackedChildrenRequired': True, 'indexedInputDerivedNotAssumed': True,
            'noLogicalChildModelPremise': True, 'logicalWrappersKeepAssumptions': True,
            'regressionsHaveNoOutcomePremise': True, 'recursiveInductionVerified': False}


def controls(output, env, lean):
    groups = (
        ('shared-unary', 'Compiler.Extraction.DispatchUnaryPreservation', (
            ('wrong-borrowed-address', 'constructors.borrowedOperation inner.address',
             'constructors.borrowedOperation (inner.address + 1)', 3),
            ('wrong-loaded-id', 'loaded = annotation', 'loaded = annotation + 1', 1),
            ('wrong-child-inputs', 'readArguments (logic.read before) ids = some values',
             'readArguments (logic.read before) [0] = some values', 1),
            ('wrong-result-word', 'some (Unary.iszero.eval value)', 'some value', 3),
        )),
        ('native-unary', 'Compiler.Extraction.InternerNativeUnaryDispatch', (
            ('wrong-index', '(Nested.storageReads rows) operand before := by\n  intro id',
             '(Nested.storageReads rows) (fun source index annotation => operand source (index + 1) annotation) before := by\n  intro id', 1),
            ('wrong-parent-word', 'key.eval (Folding.wordMeaning other) before.graph.read = some expected',
             'key.eval (Folding.wordMeaning other) before.graph.read = some (expected + 1)', 2),
            ('inactive-miss', '(active : (deterministic && (request.item.kind == 1)) = true)',
             '(active : (deterministic && (request.item.kind == 1)) = false)', 1),
        )),
        ('native-unary-fixture', MODULE, (
            ('erase-initializer-effect', '(before.mapEffects Nat.succ).mapEffects Nat.succ', 'before.mapEffects Nat.succ', 1),
            ('erase-read-failure', '(.error (.language (match error with | .invalidId => .invalidId | .invalidOptional => .invalidOptional | .safetyFault => .safetyFault)), before)',
             '(.ok none, before)', 1),
            ('wrong-borrowed-return', '(.ok (some 0), before.mapEffects Nat.succ)',
             '(.ok (some 1), before.mapEffects Nat.succ)', 1),
        )),
    )
    records = []
    for label, module, changes in groups:
        original = source(module)
        records += checked_controls(output, [mutation_check(output, label + '-unchanged', original, True, env, lean)])
        for name, before, after, count in changes:
            if original.count(before) != count:
                raise ValueError('ambiguous unary mutation: ' + name + ': ' + str(original.count(before)))
            records += checked_controls(output, [mutation_check(output, label + '-' + name,
                original.replace(before, after), False, env, lean)])
    return records
