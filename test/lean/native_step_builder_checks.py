"""Audit native recursive entries supplying shared builder/dispatcher contracts.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
import constructor_replay_choice_checks as choice
import native_miss_frame_checks as miss_frames
from native_algebraic_dispatch_checks import source
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check

NS, OWNED = gate.NS, gate.OWNED
DISPATCH = 'Compiler.Extraction.Dispatch.'
SHARED = DISPATCH + 'Preservation.'
ALG = 'Compiler.Algebraic.'
SEM = OWNED + 'Semantic.'
TESTS = gate.ITEM + 'NativeStepTests.'
MODULE = 'Compiler.Extraction.InternerNativeStepTests'
PRODUCTION = ('Enclosing.cleanup', 'ConstructorPost.nativeSafe', 'step_constant_safe', 'step_operation_safe',
              'step_operation_rule', 'step_builder_rules', 'step_sar_rule', 'CallFrame.step_rules', 'miss_signextend_unfold_verified')
REGRESSIONS = ('entry_at_capacity', 'entries_at_capacity', 'capacity_rules', 'constant_observed',
               'operation_observed', 'parent_operand_survives')
CLAIMS = [NS + name for name in PRODUCTION] + [TESTS + name for name in REGRESSIONS] + miss_frames.CLAIMS
INTERFACES = (SHARED + 'builderRules_of_operations', NS + 'StepEntryFrames.mk', TESTS + 'full', TESTS + 'callbacks', TESTS + 'constant', TESTS + 'operation') + miss_frames.INTERFACES


def audit(claims):
    required = {
        DISPATCH + 'algebraic_selected_safe': {SHARED + 'logicalBuilderRules', SHARED + 'builderRules_of_operations'},
        NS + 'Enclosing.cleanup': {NS + 'CallFrame.cleanup', NS + 'Enclosing.rec'},
        NS + 'ConstructorPost.nativeSafe': {NS + 'ConstructorPost', SEM + 'NativeSafe'},
        NS + 'step_constant_safe': {NS + 'step_constant_native_verified', NS + 'ConstructorPost.nativeSafe'},
        NS + 'step_operation_safe': {NS + 'step_operation_native_verified', NS + 'ConstructorPost.nativeSafe', NS + 'Enclosing.cleanup'},
        NS + 'step_operation_rule': {NS + 'step_operation_safe', 'Compiler.Extraction.Folding.word_meaning_operation'},
        NS + 'step_builder_rules': {SHARED + 'builderRules_of_operations', NS + 'step_constant_safe', NS + 'step_operation_rule'},
        NS + 'step_sar_rule': {NS + 'step_operation_safe', 'Compiler.Extraction.ArithmeticShift.operation'},
        NS + 'CallFrame.step_rules': {NS + 'step_builder_rules', NS + 'step_operation_rule', NS + 'step_sar_rule', NS + 'Enclosing.call'},
        NS + 'miss_signextend_unfold_verified': {NS + 'CallFrame.step_rules', NS + 'miss_signextend_verified', NS + 'native_miss_words', NS + 'Enclosing.native_miss_frames'},
        TESTS + 'entries_at_capacity': {TESTS + 'entry_at_capacity', NS + 'Enclosing.retained'},
        TESTS + 'capacity_rules': {TESTS + 'entries_at_capacity', NS + 'CallFrame.step_rules', NS + 'StepEntryFrames.of_operations'},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('native step lost entry composition: ' + name + ': ' + ', '.join(sorted(missing)))
    for name in CLAIMS:
        if not name.startswith(TESTS) and any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('production native step depends on a fixture: ' + name)
    return {'checkedDependencies': sorted(required), 'nativeMissFrames': miss_frames.audit(claims), 'nativeEntriesSupplyBuilderContracts': True,
            'actualRecursiveChildrenConsumedByOwnedMiss': True, 'literalCleanupDerivedFromEnclosingStack': True,
            'lowerChildEntryObligationsDischarged': False, 'recursiveInductionVerified': False,
            'completeStreamCorrespondenceVerified': False}


def args_named(value, terms, context, expected, description):
    if [gate.named(value, term, context) for term in terms] != list(expected):
        raise ValueError('native step changed ' + description)


def native_base(value, term, context, base='base'):
    args = joint.app(value, term, NS + 'callerContext')
    args_named(value, args[-7:-3], context, ('ops', 'allocate', 'safety', 'owner'), 'native host and owner')
    args_named(value, args[-2:], context, (base, 'growth'), 'native context and growth')
    meaning = joint.app(value, args[-3], DISPATCH + 'wordDispatchMeaning')
    args_named(value, meaning[-2:], context, ('env', 'other'), 'native meaning')


def recursive_children(value, term, context, successor):
    args = joint.app(value, term, NS + 'unfold')
    native_base(value, args[-4], context)
    args_named(value, args[-3:-1], context, ('owner', 'usizeBits'), 'recursive geometry')
    if successor:
        args, context = choice.one_call(value, args[-1], context, 'HAdd.hAdd')
        args_named(value, args[-2:-1], context, ('depth',), 'proper-child depth')
        one = joint.app(value, args[-1], 'OfNat.ofNat')
        if gate.named(value, one[-2], context) != ('natural', '1'):
            raise ValueError('native step no longer uses the successor depth')
    else:
        args_named(value, args[-1:], context, ('depth',), 'lower-child depth')


def audit_statements(rows, interfaces):
    statements = {row['theorem']: row['statement'] for row in rows}
    definitions = {row['name']: row for row in interfaces}
    value = definitions[NS + 'StepEntryFrames.mk']['type']
    fields, _, _ = gate.domains(value)
    if set(fields) != {'σ', 'safety', 'owner', 'usizeBits', 'base', 'children', 'env', 'other', 'debug', 'ready', 'constant', 'operation'}:
        raise ValueError('native step entries changed their local obligations')
    for field, request, before in (('constant', 'constantRequest', 'before'), ('operation', 'operationRequest', 'prepared')):
        term, local = fields[field]
        args, local = choice.one_call(value, term, local, NS + 'EntryFrames')
        args_named(value, args[1:6], local, ('safety', 'owner', 'usizeBits', 'base', 'children'), 'entry context')
        args_named(value, args[-6:], local, ('debug', before, 'rows', 'ready', 'env', 'other'), 'entry frame and reached world')
        request_args = joint.app(value, args[-7], 'Compiler.Extraction.Interner.ConstructorCode.' + request)
        args_named(value, request_args[0:1], local, ('Compiler.Extraction.Interner.constructorCode',), 'actual request code')
        args_named(value, request_args[1:], local, ('value',) if field == 'constant' else ('opcode', 'ids'), 'actual request input')
    term, local = fields['operation']
    prepared, reached = choice.one_call(value, term, local, gate.ITEM + 'Arguments.Prepared')
    args_named(value, prepared[-4:], reached, ('ids', 'before', 'source', 'prepared'), 'actual literal preparation')
    prepared, reached = choice.one_call(value, term, local, gate.ITEM + 'Arguments.prepare')
    args_named(value, prepared[-2:], reached, ('ids', 'before'), 'literal preparation execution')

    common = {'σ', 'ops', 'allocate', 'safety', 'owner', 'usizeBits', 'base', 'growth', 'children',
              'env', 'other', 'debug', 'ready', 'admitted', 'typed', 'graphs', 'entries', 'before', 'valid'}
    for method, extra, arguments in (
        ('constant', {'pushes', 'literals', 'value'}, ('value', 'debug')),
        ('operation', {'stack', 'opcode', 'ids', 'values', 'expected', 'actual', 'evaluated'}, ('opcode', 'ids', 'debug')),
    ):
        value = statements[NS + 'step_' + method + '_safe']
        fields, root, context = gate.domains(value)
        if set(fields) != common | extra:
            raise ValueError('native step changed general entry inputs: ' + method)
        args = joint.app(value, root, SEM + 'NativeSafe')
        args_named(value, args[-4:-3], context, ('ready',), 'retained caller predicate')
        args_named(value, args[-2:-1], context, ('before',), 'actual entry world')
        callback = joint.app(value, args[-3], 'Compiler.Extraction.Associative.Constructors.' + method)
        args_named(value, callback[-len(arguments):], context, arguments, 'actual constructor operands and debug')
        step = joint.app(value, callback[-len(arguments)-1], NS + 'step')
        native_base(value, step[-4], context)
        args_named(value, step[-3:], context, ('owner', 'usizeBits', 'children'), 'actual recursive step')
        entry, local = fields['entries']
        entry = joint.app(value, entry, NS + 'StepEntryFrames')
        native_base(value, entry[-6], local)
        args_named(value, entry[-5:], local, ('children', 'env', 'other', 'debug', 'ready'), 'same entry contract')

    value = statements[NS + 'miss_signextend_unfold_verified']
    fields, _, _ = gate.domains(value)
    wanted = {'σ', 'ops', 'allocate', 'safety', 'owner', 'usizeBits', 'base', 'growth', 'env', 'other', 'debug',
              'rows', 'source', 'values', 'normalized', 'address', 'native', 'parent', 'depth', 'stack', 'admitted',
              'typed', 'pushes', 'literals', 'entries', 'before', 'initial', 'data', 'capacity', 'facts', 'key', 'left', 'right',
              'arguments', 'instruction', 'operation', 'expected', 'valid', 'evaluated', 'aligned', 'sequence', 'bound',
              'request', 'sourceArguments', 'lookup', 'deterministic', 'originBefore', 'originTaken', 'originValues', 'originInitial', 'origin', 'active'}
    if set(fields) != wanted:
        raise ValueError('native recursive miss changed premises: ' + str(sorted(set(fields) ^ wanted)))
    forbidden = {ALG + 'BuilderRules', SHARED + 'OperationRule', SHARED + 'SarRule', NS + 'ConstructorPost',
                 NS + 'MissWords', NS + 'MissFrames', SEM + 'NativeSafe', SEM + 'Ensures', DISPATCH + 'UnaryPreservation.Inputs'}
    for field, (term, _) in fields.items():
        if field not in ('p', 'ran', 'actual') and forbidden & gate.step.constants_below(value, term):
            raise ValueError('native recursive miss assumes a derived contract: ' + field)
    term, local = fields['entries']
    args = joint.app(value, term, NS + 'StepEntryFrames')
    native_base(value, args[-6], local)
    recursive_children(value, args[-5], local, False)
    args_named(value, args[-4:-1], local, ('env', 'other', 'debug'), 'entry semantics and debug')
    frame = joint.app(value, args[-1], NS + 'CallFrame')
    args_named(value, frame[-10:-9], local, ('safety',), 'live caller safety')
    joint.path(value, frame[-9], local, (gate.ITEM + 'ShiftInput.Context.allocator',), 'base')
    args_named(value, frame[-8:], local, ('owner', 'rows', 'source', 'values', 'normalized', 'address', 'native', 'parent'), 'live caller geometry')
    body, context = value['root'], []
    while value['nodes'][body][0] == 'forall':
        node = value['nodes'][body]
        context.append(node[1])
        body = node[4]
    calls, local = choice.one_call(value, body, context, NS + 'context')
    native_base(value, calls[-5], local)
    recursive_children(value, calls[-2], local, True)
    args_named(value, calls[-1:], local, ('debug',), 'actual recursive caller debug')
    if not {NS + 'FramePost', SEM + 'Ensures', OWNED + 'finish', 'Compiler.Extraction.Interner.FindCode.controlMiss'} <= gate.step.constants_below(value, body):
        raise ValueError('native recursive miss lost complete owned execution')
    for name in ('constant_observed', 'operation_observed', 'parent_operand_survives'):
        fields, _, _ = gate.domains(statements[TESTS + name])
        if set(fields) != {'safety'}:
            raise ValueError('native capacity regression gained an outcome premise')
    return {'nativeMissFrames': miss_frames.audit_statements(rows, interfaces), 'actualNativeEntryInputsBound': True, 'properDepthAndSuccessorExecutionBound': True,
            'noBuilderOrFinalResultPremise': True, 'regressionsHaveNoOutcomePremise': True,
            'recursiveInductionVerified': False}


def controls(output, env, lean):
    groups = (
        ('native-step-builder', 'Compiler.Extraction.InternerNativeStepBuilder', (
            ('wrong-constant', '(Interner.constructorCode.constantRequest value)', '(Interner.constructorCode.constantRequest (value + 1))', 1),
            ('wrong-operation', '(Interner.constructorCode.operationRequest opcode ids)', '(Interner.constructorCode.operationRequest opcode ids.reverse)', 2),
            ('wrong-literal-before', 'Arguments.prepare ids before = (.ok source, prepared)', 'Arguments.prepare ids prepared = (.ok source, prepared)', 1),
            ('drop-native-operation', 'exact checked.nativeSafe (fun _ reached => reached.2)', 'exact valid.1', 2),
            ('wrong-sar-order', '(by simp [readArguments, lhs, rhs])',
             '(show readArguments before.graph.read [left, right] = some [word, amount] from by simp [readArguments, lhs, rhs])', 1),
        )),
        ('native-step-dispatch', 'Compiler.Extraction.InternerNativeStepDispatch', (
            ('same-depth-execution', '(depth + 1)', 'depth', 4),
            ('wrong-parent-input', 'fun _ frame => frame.1', 'fun _ frame => frame.2', 1),
            ('wrong-key-words', 'key.arguments = normalized.items', 'key.arguments = values', 1),
        )),
        ('native-step-fixture', MODULE, (
            ('no-capacity-stop', 'atCapacity := fun _ => true', 'atCapacity := fun _ => false', 1),
            ('wrong-capacity-result', '.error (.language .capacity)', '.error (.language .outOfMemory)', 2),
            ('literal-array-not-allocated', 'nextId + 2', 'nextId + 1', 1),
            ('parent-owner-retired', 'heap.lookup ((before safety true).memory.memory.nextId + 1)',
             'heap.lookup 6', 1),
            ('wrong-parent-operand', '(.ok (some 0), .ok (some 0))', '(.ok (some 0), .ok (some 1))', 1),
        )),
    )
    records = []
    for label, module, changes in groups:
        original = source(module)
        records += checked_controls(output, [mutation_check(output, label + '-unchanged', original, True, env, lean)])
        for name, before, after, count in changes:
            if original.count(before) != count:
                raise ValueError('ambiguous native step mutation: ' + name + ': ' + str(original.count(before)))
            records += checked_controls(output, [mutation_check(output, label + '-' + name, original.replace(before, after), False, env, lean)])
    return records + miss_frames.controls(output, env, lean)
