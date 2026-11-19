"""Audit complete folding-prefix preservation and native unary composition.
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
SHARED = DISPATCH + 'Preservation.'
ALG = 'Compiler.Algebraic.'
SEM = OWNED + 'Semantic.'
TESTS = gate.ITEM + 'NativePrefixTests.'
MODULE = 'Compiler.Extraction.InternerNativePrefixTests'
GENERIC = ('ReadRules.arithmetic', 'constant_stage_safe', 'or_next_safe')
REGRESSIONS = ('known_sound', 'constant_child', 'folded_hit', 'folded_oom', 'folded_preserved',
               'collection_failure', 'arity_skips_queries', 'no_applicable_fold', 'arithmetic_failure')
CLAIMS = [SHARED + name for name in GENERIC]
CLAIMS += [DISPATCH + 'arithmetic_bind_safe', DISPATCH + 'or_next_safe_of_unchanged', NS + 'singleton_dispatch_result']
CLAIMS += [TESTS + name for name in REGRESSIONS]
INTERFACES = (SHARED + 'ConstantChild', TESTS + 'known')


def audit(claims):
    required = {
        SHARED + 'ReadRules.arithmetic': {SHARED + 'ReadRules.bind', DISPATCH + 'arithmetic', 'Compiler.Extraction.Nested.readAction'},
        DISPATCH + 'arithmetic_bind_safe': {SHARED + 'ReadRules.arithmetic', SHARED + 'logicalReadRules'},
        DISPATCH + 'constant_stage_safe': {SHARED + 'constant_stage_safe', SHARED + 'logicalReadRules'},
        DISPATCH + 'or_next_safe_of_unchanged': {SHARED + 'or_next_safe'},
        SHARED + 'constant_stage_safe': {DISPATCH + 'folded_value', SHARED + 'ReadRules.bind', SHARED + 'ReadRules.arithmetic',
            SHARED + 'ConstantChild', ALG + 'BuilderLogic.bind', ALG + 'BuilderLogic.pure'},
        SHARED + 'or_next_safe': {ALG + 'BuilderLogic.bind', ALG + 'BuilderLogic.pure'},
        NS + 'singleton_dispatch_result': {DISPATCH + 'simplifyOptionsWithInputs', DISPATCH + 'constantStage', DISPATCH + 'unaryStageWithInputs'},
        NS + 'unary_dispatch_verified': {SHARED + 'constant_stage_safe', SHARED + 'or_next_safe',
            DISPATCH + 'UnaryPreservation.unary_stage_safe', NS + 'singleton_dispatch_result'},
        NS + 'dispatcher_unary_verified': {NS + 'unary_dispatch_verified', NS + 'dispatcher_snapshot', OWNED + 'NativeGraph.Facts.reads'},
        NS + 'miss_unary_verified': {NS + 'dispatcher_unary_verified', NS + 'miss_frame', NS + 'miss_words'},
        TESTS + 'constant_child': {gate.ITEM + 'NativeAlgebraicTests.rules', gate.ITEM + 'NativeUnaryTests.fixture_valid'},
        TESTS + 'folded_preserved': {NS + 'unary_dispatch_verified', TESTS + 'constant_child', TESTS + 'known_sound',
            gate.ITEM + 'NativeUnaryTests.fixture_valid', gate.ITEM + 'NativeUnaryTests.rules'},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('folding prefix lost shared composition: ' + name + ': ' + ', '.join(sorted(missing)))
    for name in CLAIMS:
        if not name.startswith(TESTS) and any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('production prefix depends on a fixture: ' + name)
    return {'checkedDependencies': sorted(required), 'logicalAndNativeFoldingProofShared': True,
            'completePrefixConsumedByNativeUnary': True, 'missStateDerivedInSharedProof': True,
            'recursiveInductionVerified': False, 'completeStreamCorrespondenceVerified': False}


def miss_post(value, post, context):
    node = value['nodes'][post]
    if node[:2] != ['lambda', 'result']:
        raise ValueError('folding prefix lost its actual result')
    result = node[1]
    node = value['nodes'][node[4]]
    if node[:2] != ['lambda', 'after']:
        raise ValueError('folding prefix lost its full reached state')
    local = context + [result, node[1]]
    word, missed = joint.app(value, node[4], 'And')
    guard = value['nodes'][missed]
    if guard[0] != 'forall':
        raise ValueError('folding prefix lost the normal-miss guard')
    equality = joint.app(value, guard[3], 'Eq')
    if gate.named(value, equality[-2], local) != 'result':
        raise ValueError('normal-miss guard changed the observed result')
    joint.app(value, equality[-1], 'Option.none')
    equality = joint.app(value, guard[4], 'Eq')
    if [gate.named(value, x, local + [guard[1]]) for x in equality[-2:]] != ['after', 'before']:
        raise ValueError('normal miss no longer retains the full initial state')
    return word, local


def audit_statements(rows, interfaces):
    statements = {row['theorem']: row['statement'] for row in rows}
    definitions = {row['name']: row for row in interfaces}
    value = definitions[SHARED + 'ConstantChild']['value']
    fields, root, context = gate.domains(value)
    args = joint.app(value, root, ALG + 'BuilderLogic.safe')
    if gate.named(value, args[-2], context) != 'before':
        raise ValueError('constant child is not checked at its actual initial state')
    action = joint.app(value, args[-3], 'Compiler.Extraction.Associative.Constructors.constant')
    if [gate.named(value, x, context) for x in action[-3:]] != ['constructors', 'expected', 'debug']:
        raise ValueError('constant child changed its request word or caller debug')
    constants = gate.step.constants_below(value, value['root'])
    if not {DISPATCH + 'collectConstants', 'Compiler.Extraction.Folding.run', 'List.length', 'List.nil', 'Ne'} <= constants:
        raise ValueError('constant child lost its source-selection or arity conditions')
    call, local = choice.one_call(value, value['root'], [], DISPATCH + 'collectConstants')
    if [gate.named(value, x, local) for x in call[-2:]] != ['reads', 'arguments']:
        raise ValueError('constant child uses different source reads or arguments')
    call, local = choice.one_call(value, value['root'], [], 'Compiler.Extraction.Folding.run')
    if [gate.named(value, x, local) for x in call[-4:]] != [
        'Compiler.Extraction.Folding.helpers', 'Compiler.Extraction.Folding.clauses', 'instruction', 'values']:
        raise ValueError('constant child no longer follows the actual folder')
    post = value['nodes'][args[-1]]
    after = value['nodes'][post[4]]
    if post[:2] != ['lambda', 'id'] or after[:2] != ['lambda', 'after']:
        raise ValueError('constant child lost its actual returned ID or state')
    local = context + ['id', 'after']
    equality = joint.app(value, after[4], 'Eq')
    read = joint.app(value, equality[-2], ALG + 'BuilderLogic.read')
    expected = joint.app(value, equality[-1], 'Option.some')
    if [gate.named(value, x, local) for x in read[-2:]] != ['after', 'id'] or gate.named(value, expected[-1], local) != 'expected':
        raise ValueError('constant child lost its returned-word condition')
    value = statements[SHARED + 'constant_stage_safe']
    fields, root, context = gate.domains(value)
    if {'collected', 'folded', 'bounded', 'nonempty', 'model', 'outcome'} & fields.keys():
        raise ValueError('full folding stage assumes a selected outcome or arity')
    result = joint.app(value, root, ALG + 'BuilderLogic.safe')
    action = joint.app(value, result[-3], DISPATCH + 'constantStage')
    if [gate.named(value, x, context) for x in action[-5:-1]] != ['constructors', 'instruction', 'arguments', 'debug']:
        raise ValueError('folding stage changed the actual constructor inputs')
    if gate.named(value, result[-2], context) != 'before':
        raise ValueError('folding stage changed the initial state')
    word, local = miss_post(value, result[-1], context)
    call, words = choice.one_call(value, word, local, ALG + 'BuilderLogic.read')
    if [gate.named(value, x, words) for x in call[-2:]] != ['after', 'id']:
        raise ValueError('folding stage lost its reached returned word')
    for name in ('dispatcher_unary_verified', 'miss_unary_verified'):
        value = statements[NS + name]
        fields, _, _ = gate.domains(value)
        if {'collected', 'folded', 'result', 'outcome'} & fields.keys():
            raise ValueError('native unary still assumes a folding outcome')
        root, context = fields['constant']
        args = joint.app(value, root, SHARED + 'ConstantChild')
        if [gate.named(value, x, context) for x in args[-3:]] != ['debug', 'before', 'expected']:
            raise ValueError('native unary changed the selected constant call')
        if gate.named(value, args[-6], context) != 'children':
            raise ValueError('native unary constant contract uses a different callback')
        joint.path(value, args[-5], context, ('Compiler.Extraction.Cache.Key.instruction',), 'key')
        ids = joint.app(value, args[-4], 'List.cons')
        if gate.named(value, ids[-2], context) != 'id':
            raise ValueError('native unary constant contract changed its source argument')
        joint.app(value, ids[-1], 'List.nil')
        reads = joint.app(value, args[-7], 'Compiler.Extraction.Nested.storageReads')
        if gate.named(value, reads[-1], context) != 'rows':
            raise ValueError('native unary constant contract lost the actual reached rows')
        logic = joint.app(value, args[-8], SEM + 'builderLogic')
        if gate.named(value, logic[-1], context) != 'ready':
            raise ValueError('native unary constant contract changed the caller predicate')
    for name, parameters in {
        'known_sound': {'other', 'memory'}, 'constant_child': {'meaning', 'memory', 'instruction', 'arguments', 'expected'},
        'folded_hit': {'before'}, 'folded_oom': {'before'}, 'folded_preserved': {'other', 'memory', 'nonzero'},
        'collection_failure': {'before', 'error'}, 'arity_skips_queries': {'before', 'instruction', 'error'},
        'no_applicable_fold': {'before'}, 'arithmetic_failure': {'before', 'fault'},
    }.items():
        fields, _, _ = gate.domains(statements[TESTS + name])
        if set(fields) != parameters:
            raise ValueError('prefix regression gained an outcome premise: ' + name)
    return {'constantChildBoundToSourceSelection': True, 'fullStateRetainedOnlyOnMiss': True,
            'nativeUnaryHasNoFoldingOutcomePremise': True, 'sameActualNativeInputsAndSuffix': True,
            'regressionsHaveNoOutcomePremise': True, 'recursiveInductionVerified': False}


def controls(output, env, lean):
    groups = (
        ('shared-prefix', 'Compiler.Extraction.DispatchProofs', (
            ('lose-miss-state', '(result = none → after = before)', '(result = none → before = before)', 3),
            ('wrong-selected-word', 'constructors.constant expected debug', 'constructors.constant (expected + 1) debug', 1),
            ('wrong-fold-inputs', 'Folding.clauses instruction values = .ok (some expected)',
             'Folding.clauses instruction [] = .ok (some expected)', 1),
        )),
        ('native-prefix-fixture', MODULE, (
            ('rewind-hit', '(.ok (some 0), before.mapEffects Nat.succ)', '(.ok (some 0), before)', 1),
            ('rewind-oom', '(.error (.language .outOfMemory), before.mapEffects Nat.succ)',
             '(.error (.language .outOfMemory), before)', 1),
            ('read-error-as-miss', '(.error (.language (match error with | .invalidId => .invalidId | .invalidOptional => .invalidOptional | .safetyFault => .safetyFault)), before)',
             '(.ok none, before)', 1),
            ('arithmetic-as-oom', '(.error (.language .safetyFault), before)', '(.error (.language .outOfMemory), before)', 1),
            ('wrong-known-word', 'if id = 1 then 1 else 0', 'if id = 1 then 2 else 0', 1),
        )),
    )
    records = []
    for label, module, changes in groups:
        original = source(module)
        records += checked_controls(output, [mutation_check(output, label + '-unchanged', original, True, env, lean)])
        for name, before, after, count in changes:
            if original.count(before) != count:
                raise ValueError('ambiguous prefix mutation: ' + name + ': ' + str(original.count(before)))
            records += checked_controls(output, [mutation_check(output, label + '-' + name,
                original.replace(before, after), False, env, lean)])
    return records
