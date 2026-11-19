"""Audit shared logical/native construction and the selected algebraic branch.
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
ALG = 'Compiler.Algebraic.'
SEM = OWNED + 'Semantic.'
LOGICAL = 'Compiler.Extraction.Interner.'
TESTS = gate.ITEM + 'NativeAlgebraicTests.'
MODULE = 'Compiler.Extraction.InternerNativeAlgebraicTests'
NATIVE = ('algebraic_dispatch_result', 'algebraic_dispatch_verified', 'dispatcher_algebraic_verified', 'miss_algebraic_verified')
CLAIMS = [ALG + 'BuilderRules.' + name for name in ('bitnot', 'sub', 'iszero', 'replacement')]
CLAIMS += [LOGICAL + 'replacement_safe_of_builder']
CLAIMS += [SEM + 'NativeSafe.' + name for name in ('of_ensures', 'ensures', 'pure', 'bind')]
CLAIMS += [NS + name for name in NATIVE]
CLAIMS += [TESTS + name for name in ('rules', 'sequential_oom', 'first_oom', 'dispatch_oom', 'fixture_valid',
                                    'sequential_preserved', 'oracle_sound', 'dispatch_preserved')]
INTERFACES = (ALG + 'BuilderLogic.mk', ALG + 'BuilderRules.mk', LOGICAL + 'builderLogic',
              SEM + 'NativeSafe', SEM + 'builderLogic', TESTS + 'children', TESTS + 'fixture')


def audit(claims):
    required = {
        ALG + 'BuilderRules.replacement': {ALG + 'BuilderLogic.bind', ALG + 'BuilderLogic.pure',
                                          ALG + 'BuilderRules.sub', ALG + 'BuilderRules.iszero'},
        LOGICAL + 'replacement_safe_of_builder': {ALG + 'BuilderRules.replacement', LOGICAL + 'builderLogic'},
        SEM + 'NativeSafe.bind': {SEM + 'NativeSafe', ALG + 'Effect.bind', ALG + 'Preserves.trans'},
        NS + 'algebraic_dispatch_result': {'Compiler.Extraction.Dispatch.binaryStageWithInputs',
                                         'Compiler.Extraction.Dispatch.constantStage'},
        NS + 'algebraic_dispatch_verified': {ALG + 'BuilderRules.replacement', ALG + 'zigApply_eq',
            'Compiler.Extraction.Dispatch.constant_facts_reliable', 'Compiler.Extraction.Dispatch.selected_word_value',
            SEM + 'NativeSafe.ensures', NS + 'algebraic_dispatch_result', 'Compiler.Extraction.Dispatch.Preservation.algebraic_selected_safe'},
        NS + 'dispatcher_algebraic_verified': {NS + 'dispatcher_snapshot', NS + 'algebraic_dispatch_verified',
                                              OWNED + 'NativeGraph.Facts.reads', LOGICAL + 'representative_reads_sound'},
        NS + 'miss_algebraic_verified': {NS + 'dispatcher_algebraic_verified', NS + 'miss_frame', NS + 'miss_words'},
        TESTS + 'dispatch_oom': {NS + 'algebraic_dispatch_result', TESTS + 'children', TESTS + 'reads'},
        TESTS + 'sequential_preserved': {ALG + 'BuilderRules.replacement', TESTS + 'rules', TESTS + 'fixture_valid'},
        TESTS + 'dispatch_preserved': {NS + 'algebraic_dispatch_verified', TESTS + 'rules', TESTS + 'fixture_valid', TESTS + 'oracle_sound'},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('native algebraic proof lost reuse: ' + name + ': ' + ', '.join(sorted(missing)))
    for name in CLAIMS:
        if name.startswith(TESTS):
            continue
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('native algebraic production proof depends on a fixture: ' + name)
    return {'checkedDependencies': sorted(required), 'oneReplacementProofForLogicalAndNative': True,
            'nativeTableSelectionAndMissConsumed': True, 'sequentialFailureRetainsReachedWorld': True,
            'recursiveInductionVerified': False, 'completeStreamCorrespondenceVerified': False}


def audit_builder_premise(statement, field, meaning_head='Compiler.Extraction.Folding.wordMeaning'):
    root, local = field
    args = joint.app(statement, root, ALG + 'BuilderRules')
    if gate.named(statement, args[-1], local) != 'debug':
        raise ValueError('native algebraic child contract lost caller debug')
    builder = joint.app(statement, args[-2], 'Compiler.Extraction.Dispatch.algebraicBuilder')
    if gate.named(statement, builder[-1], local) != 'children':
        raise ValueError('native algebraic child contract changed callbacks')
    logic = joint.app(statement, args[-3], SEM + 'builderLogic')
    if gate.named(statement, logic[-1], local) != 'ready':
        raise ValueError('native algebraic child contract changed reached predicate')
    meaning = joint.app(statement, logic[-2], meaning_head)
    if gate.named(statement, meaning[-1], local) != 'other':
        raise ValueError('native algebraic child contract changed word meaning')


def audit_statements(rows, interfaces):
    statements = {row['theorem']: row['statement'] for row in rows}
    definitions = {row['name']: row for row in interfaces}
    for name, native in ((LOGICAL + 'builderLogic', False), (SEM + 'builderLogic', True)):
        value = definitions[name]['value']
        _, root, context = gate.domains(value)
        args = joint.app(value, root, ALG + 'BuilderLogic.mk')
        read, valid, safe, pure, bind = args[-5:]
        owner = SEM + 'NativeSafe' if native else LOGICAL + 'Safe'
        for term, suffix in ((safe, ''), (pure, '.pure'), (bind, '.bind')):
            local = context[:]
            while value['nodes'][term][0] == 'lambda':
                node = value['nodes'][term]
                local.append(node[1])
                term = node[4]
            supplied = joint.app(value, term, owner + suffix)
            if [gate.named(value, x, local) for x in supplied[-(2 if native else 1):]] != (['meaning', 'ready'] if native else ['meaning']):
                raise ValueError('construction instance changed its actual semantics: ' + name + suffix)
        if native:
            if not {OWNED + 'World.graph', LOGICAL + 'Heap.read'} <= gate.step.constants_below(value, read):
                raise ValueError('native construction does not read the actual world graph')
            if not {'And', OWNED + 'World.graph', LOGICAL + 'Invariant'} <= gate.step.constants_below(value, valid):
                raise ValueError('native construction dropped its graph invariant')
    value = definitions[ALG + 'BuilderRules.mk']['type']
    fields, _, _ = gate.domains(value)
    for field, method, names in (('constant', 'makeConstant', ['builder', 'value', 'debug']),
                                 ('operation', 'makeOperation', ['builder', 'op', 'ids', 'debug'])):
        root, context = fields[field]
        args, local = choice.one_call(value, root, context, ALG + 'Builder.' + method)
        if [gate.named(value, x, local) for x in args[-len(names):]] != names:
            raise ValueError('shared builder contract changed actual callback inputs')
        constants = gate.step.constants_below(value, root)
        if not {ALG + 'BuilderLogic.safe', ALG + 'BuilderLogic.valid'} <= constants:
            raise ValueError('shared builder contract lost validity or preservation')
        if {ALG + 'zigApply', ALG + 'Replacement.build'} & constants:
            raise ValueError('shared builder contract assumes complete replacement preservation')
    statement = statements[LOGICAL + 'replacement_safe_of_builder']
    fields, root, context = gate.domains(statement)
    if set(fields) != {'Debug', 'meaning', 'builder', 'correct', 'before', 'valid', 'replacement',
                       'left', 'right', 'a', 'b', 'debug', 'ha', 'hb'}:
        raise ValueError('logical replacement changed its public assumptions')
    correct, local = fields['correct']
    joint.app(statement, correct, LOGICAL + 'BuilderSafe')
    result = joint.app(statement, root, LOGICAL + 'Safe')
    if gate.named(statement, result[-2], context) != 'before':
        raise ValueError('logical replacement changed its initial heap')
    action = joint.app(statement, result[-3], ALG + 'Replacement.build')
    if [gate.named(statement, x, context) for x in action[-5:]] != ['replacement', 'builder', 'left', 'right', 'debug']:
        raise ValueError('logical replacement changed its action')
    post, local = choice.one_call(statement, result[-1], context, ALG + 'Replacement.eval')
    if [gate.named(statement, x, local) for x in post] != ['replacement', 'a', 'b']:
        raise ValueError('logical replacement changed its value postcondition')
    value = definitions[SEM + 'NativeSafe']['value']
    fields, root, context = gate.domains(value)
    needed = {'And', LOGICAL + 'Invariant', LOGICAL + 'Stable', OWNED + 'World.graph', SEM + 'NativeSafe.match_1'}
    if not needed <= gate.step.constants_below(value, root):
        raise ValueError('native construction lost ordinary-error invariant, stability or success postcondition')
    guard, local = list(fields.values())[-1]
    equality = joint.app(value, guard, 'Eq')
    if gate.named(value, equality[-1], local) != 'Bool.true':
        raise ValueError('native construction changed its ordinary-result guard')
    joint.app(value, equality[-2], OWNED + 'ordinary')
    audit_native_safe(value, root, context)
    common = {'σ', 'safety', 'owner', 'usizeBits', 'base', 'children', 'debug', 'source', 'address', 'native',
              'key', 'normalized', 'before', 'rows', 'data', 'capacity', 'left', 'right', 'lc', 'rc', 'replacement',
              'facts', 'arguments', 'collected', 'leftRead', 'rightRead', 'selected', 'other', 'expected',
              'operation', 'valid', 'evaluated', 'ready', 'initial', 'proper'}
    for name, parameters in (
        ('dispatcher_algebraic_verified', common),
        ('miss_algebraic_verified', common | {'frame', 'request', 'lookup', 'deterministic', 'active', 'frames', 'words'}),
    ):
        statement = statements[NS + name]
        fields, _, context = gate.domains(statement)
        if set(fields) != parameters:
            raise ValueError('native algebraic branch changed assumptions: ' + name + ': ' + str(sorted(set(fields) ^ parameters)))
        for field, (root, _) in fields.items():
            constants = gate.step.constants_below(statement, root)
            if any('Uniform.' in dep or dep.endswith('.projection') or dep.endswith('.SourceConstructorsAt') for dep in constants):
                raise ValueError('native algebraic branch regained model correspondence: ' + field)
            if {NS + 'FramePost', SEM + 'NativeSafe', SEM + 'Ensures', ALG + 'zigApply'} & constants:
                raise ValueError('native algebraic branch assumes its final execution: ' + field)
        audit_builder_premise(statement, fields['proper'])
        body = statement['root']
        while statement['nodes'][body][0] == 'forall':
            body = statement['nodes'][body][4]
        required = {SEM + 'Ensures'}
        if name.startswith('miss_'):
            required |= {NS + 'FramePost', OWNED + 'finish', 'Compiler.Extraction.Interner.FindCode.controlMiss'}
        if not required <= gate.step.constants_below(statement, body):
            raise ValueError('native algebraic branch lost actual execution composition')
    for name, expected in {'sequential_oom': {'before', 'left', 'right'}, 'first_oom': {'before'},
                           'dispatch_oom': {'before'}, 'fixture_valid': {'meaning', 'memory', 'value'},
                           'sequential_preserved': {'meaning', 'memory', 'value'}, 'rules': {'meaning'},
                           'oracle_sound': {'meaning', 'memory', 'value'},
                           'dispatch_preserved': {'other', 'memory', 'value'}}.items():
        fields, _, _ = gate.domains(statements[TESTS + name])
        if set(fields) != expected:
            raise ValueError('native algebraic regression added an outcome or validity premise: ' + name)
    return {'nativeLogicUsesActualWorldAndFaults': True, 'sameLogicalReplacementStatement': True,
            'onlyCallerDebugAndNativeChildrenRequired': True, 'noLogicalChildModelPremise': True,
            'ordinaryFailureInvariantRetained': True, 'regressionsHaveNoOutcomePremise': True,
            'recursiveInductionVerified': False, 'completeStreamCorrespondenceVerified': False}


def audit_native_safe(value, root, context):
    cursor, local = value['root'], []
    while value['nodes'][cursor][0] == 'lambda':
        node = value['nodes'][cursor]
        local.append(node[1])
        cursor = node[4]
    node = value['nodes'][cursor]
    if node[:2] != ['let', 'ran'] or gate.named(value, node[3], local) != ('app', 'action', 'before'):
        raise ValueError('native preservation is not attached to the actual call')
    frame, rest = joint.app(value, root, 'And')
    node = value['nodes'][frame]
    if node[0] != 'app' or gate.named(value, node[1], context) != 'ready':
        raise ValueError('native preservation lost the reached caller predicate')
    joint.path(value, node[2], context, ('Prod.snd',), 'ran')
    invariant, rest = joint.app(value, rest, 'And')
    args = joint.app(value, invariant, LOGICAL + 'Invariant')
    if gate.named(value, args[-2], context) != 'meaning':
        raise ValueError('native preservation changed its invariant meaning')
    joint.path(value, args[-1], context, (OWNED + 'World.graph', 'Prod.snd'), 'ran')
    stable, post = joint.app(value, rest, 'And')
    args = joint.app(value, stable, LOGICAL + 'Stable')
    joint.path(value, args[-2], context, (OWNED + 'World.graph',), 'before')
    joint.path(value, args[-1], context, (OWNED + 'World.graph', 'Prod.snd'), 'ran')
    args = joint.app(value, post, SEM + 'NativeSafe.match_1')
    joint.path(value, args[-3], context, ('Prod.fst',), 'ran')
    failure = value['nodes'][args[-2]]
    success = value['nodes'][args[-1]]
    if failure[0] != 'lambda' or gate.named(value, failure[4], context + [failure[1]]) != 'True':
        raise ValueError('native failure branch changed the returned-value obligation')
    if success[0] != 'lambda':
        raise ValueError('native success branch lost the returned value')
    local = context + [success[1]]
    body = value['nodes'][success[4]]
    if body[0] != 'app' or gate.named(value, body[1], local) != ('app', 'post', success[1]):
        raise ValueError('native success branch lost its actual value postcondition')
    joint.path(value, body[2], local, ('Prod.snd',), 'ran')


def source(module):
    raw = (gate.harness.ROOT / ('lean/' + module.replace('.', '/') + '.lean')).read_text()
    return ('\n'.join(line for line in raw.splitlines() if line.startswith('import '))
            + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw))


def controls(output, env, lean):
    groups = (
        ('shared-builder', 'Compiler.Extraction.BuilderPreservation', (
            ('swap-result-operands', '(replacement.eval a b)', '(replacement.eval b a)', 1),
            ('lose-old-reads', 'Preserves read before after', 'Preserves read after after', 1),
        )),
        ('native-builder', 'Compiler.Extraction.InternerNativeBuilder', (
            ('erase-fault-guard', 'ordinary ran.1 = true →', 'True →', 1),
            ('lose-stability', 'Interner.Stable before.graph ran.2.graph', 'Interner.Stable ran.2.graph ran.2.graph', 1),
            ('rewind-second-child', 'NativeSafe meaning ready (first >>= next) before post := by',
             'NativeSafe meaning ready (first >>= fun value => fun _ => next value before) before post := by', 1),
        )),
        ('native-algebraic', 'Compiler.Extraction.InternerNativeAlgebraicDispatch', (
            ('wrong-selected-stage', 'zigSelect key.instruction .constants', 'zigSelect key.instruction .equal', 2),
            ('wrong-parent-word', 'key.eval (Folding.wordMeaning other) before.graph.read = some expected',
             'key.eval (Folding.wordMeaning other) before.graph.read = some (expected + 1)', 3),
            ('inactive-miss', '(active : (deterministic && (request.item.kind == 1)) = true)',
             '(active : (deterministic && (request.item.kind == 1)) = false)', 1),
        )),
        ('native-algebraic-fixture', MODULE, (
            ('erase-second-effect', '(before.mapEffects Nat.succ).mapEffects Nat.succ', 'before.mapEffects Nat.succ', 2),
            ('erase-oom', '(.error (.language .outOfMemory), (before.mapEffects Nat.succ).mapEffects Nat.succ) := by',
             '(.ok (some 0), (before.mapEffects Nat.succ).mapEffects Nat.succ) := by', 1),
        )),
    )
    records = []
    for label, module, changes in groups:
        original = source(module)
        records += checked_controls(output, [mutation_check(output, label + '-unchanged', original, True, env, lean)])
        for name, before, after, count in changes:
            if original.count(before) != count:
                raise ValueError('ambiguous algebraic mutation: ' + name + ': ' + str(original.count(before)))
            records += checked_controls(output, [mutation_check(output, label + '-' + name,
                original.replace(before, after), False, env, lean)])
    return records
