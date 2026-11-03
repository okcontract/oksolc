"""Audit words for the fixed recursive replay and its native dispatcher consumer.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
from native_miss_frame_checks import named
from native_resource_admission_checks import telescope, local_call
from native_algebraic_dispatch_checks import source
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check

NS, OWNED, ITEM = gate.NS, gate.OWNED, gate.ITEM
TRACE = NS + 'AllocationTrace.'
INSERTION = OWNED + 'Insertion.Native.'
INTERNER = 'Compiler.Extraction.Interner.'
STORAGE = 'Compiler.Extraction.Storage.'
SCOPED = INTERNER + 'Scoped.'
TESTS = ITEM + 'AllocationWordTests.'
CLAIMS = [STORAGE + n for n in ('Program.execute_conditionAll', 'Program.conditionAll_ordinary',
          'insert_execution_prefix')]
CLAIMS += [INTERNER + 'InsertionExecution.' + n for n in ('project_prefix_safe', 'transaction_safe', 'action_safe')]
CLAIMS += [SCOPED + n for n in ('handoff_insert_safe_for', 'miss_safe_for', 'owned_safe_for',
          'control_find_safe_for', 'find_safe_for')]
CLAIMS += [INSERTION + n for n in ('candidate_value', 'allocationReplay_safe')]
CLAIMS += [TRACE + n for n in ('enter_bind_safe', 'insertionReplay_safe', 'publish_safe', 'request_key',
          'inputGraphReplay_contracts', 'requestModel_safe', 'entry_request_safe', 'body_words', 'recursive_words', 'recursive_dispatch_words')]
CLAIMS += [TESTS + n for n in ('fault_prefix_preserved', 'rejected_cleanup_retains_append', 'closed_words',
          'wrong_literal_rejected', 'unrelated_key_rejected')]
INTERFACES = tuple(STORAGE + n for n in ('ExecutionPost', 'Program.conditionAll', 'PublishedPrefix'))
INTERFACES += tuple(SCOPED + n for n in ('GraphContractsFor.mk', 'ContractsFor.mk'))
INTERFACES += (TRACE + 'RequestKey', TRACE + 'Words.mk')


def audit(claims):
    required = {
        STORAGE + 'Program.execute_conditionAll': {STORAGE + 'Cleanup.execute_conditionAll'},
        STORAGE + 'insert_execution_prefix': {STORAGE + 'Program.execute_conditionAll', STORAGE + 'insert_condition_prefix'},
        INTERNER + 'InsertionExecution.transaction_safe': {STORAGE + 'insert_execution_prefix', INTERNER + 'InsertionExecution.project_prefix_safe'},
        INTERNER + 'InsertionExecution.action_safe': {INTERNER + 'InsertionExecution.transaction_safe'},
        INSERTION + 'allocationReplay_safe': {INTERNER + 'InsertionExecution.action_safe', INSERTION + 'candidate_value'},
        INSERTION + 'candidate_words': {INSERTION + 'candidate_value', 'Compiler.Extraction.Cache.key_inputs'},
        TRACE + 'insertionReplay_safe': {INSERTION + 'allocationReplay_safe'},
        TRACE + 'publish_safe': {INTERNER + 'publish_safe'},
        TRACE + 'inputGraphReplay_contracts': {TRACE + 'insertionReplay_safe', TRACE + 'publish_safe'},
        TRACE + 'requestModel_safe': {TRACE + 'callerModel_safe', SCOPED + 'find_safe_for',
                                     'Compiler.Extraction.Dispatch.default_key_simplify_safe'},
        TRACE + 'entry_request_safe': {TRACE + 'requestModel_safe', TRACE + 'enter_bind_safe'},
        TRACE + 'body_words': {TRACE + 'entry_request_safe'},
        TRACE + 'recursive_words': {TRACE + 'body_words', TRACE + 'enter_bind_safe'},
        TRACE + 'recursive_dispatch_words': {TRACE + 'recursive_sources', TRACE + 'recursive_words',
            NS + 'dispatcher_resource_projected', OWNED + 'Recursive.safe_at', 'Compiler.Extraction.Dispatch.default_key_simplify_safe'},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('recursive words lost shared proof: ' + name + ': ' + ', '.join(sorted(missing)))
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('recursive words depend on fixtures: ' + name)
    return {'checkedDependencies': sorted(required), 'recursiveReplayWordLawsDerived': True,
            'nativeDispatcherWordsUnderAdmissionDerived': True, 'callbackFaultPrefixesCovered': True,
            'nativeAdmissionDerived': False, 'nonordinaryNativePreservationVerified': False,
            'composedProductionTheoremVerified': False}


def audit_statements(rows, interfaces):
    statements = {row['theorem']: row['statement'] for row in rows}
    definitions = {row['name']: row for row in interfaces}
    value = statements[TRACE + 'recursive_words']
    fields, _, root, context = telescope(value)
    if set(fields) != {'env', 'other', 'usizeBits', 'seed', 'stream', 'mismatch', 'pushes', 'pushValues', 'depth'}:
        raise ValueError('word induction gained a recursive or execution premise')
    joint.app(value, fields['pushes'][0], 'Compiler.Extraction.Associative.Pushes')
    joint.app(value, fields['pushValues'][0], INSERTION + 'PushValues')
    words = joint.app(value, root, TRACE + 'Words')
    named(value, words[:2], context, ('env', 'other'))
    replay = joint.app(value, words[-1], TRACE + 'streamReplay')
    named(value, replay[:1], context, ('stream',))
    model = joint.app(value, replay[-1], TRACE + 'recursiveModels')
    meaning = joint.app(value, model[0], 'Compiler.Extraction.Dispatch.wordDispatchMeaning')
    named(value, meaning, context, ('env', 'other'))
    named(value, model[1:], context, ('usizeBits', 'seed', 'stream', 'mismatch', 'depth'))
    value = statements[TRACE + 'recursive_dispatch_words']
    fields, lets, root, context = telescope(value)
    common = {'σ', 'ops', 'allocate', 'safety', 'owner', 'usizeBits', 'env', 'other', 'base', 'growth',
              'outerOps', 'outerAllocate', 'outerBase', 'outerGrowth', 'hosts', 'allocators', 'budgets', 'queries',
              'debug', 'seed', 'mismatch', 'admitted', 'outerAdmitted', 'typed', 'closedQuery',
              'capacityQuery', 'classificationQuery', 'pushes', 'pushValues', 'depth',
              'rows', 'source', 'values', 'normalized', 'address', 'native', 'parent', 'stack', 'before', 'initial',
              'data', 'capacity', 'facts', 'key', 'aligned', 'expected', 'operation', 'valid', 'evaluated'}
    if set(fields) != common or set(lets) != {'nativeChildren', 'action'}:
        raise ValueError('native word consumer changed its admitted input boundary: ' + str(sorted(fields)))
    forbidden = {TRACE + 'Words', TRACE + 'RecursiveSources', INTERNER + 'Safe', OWNED + 'Semantic.Ensures',
                 'Compiler.Extraction.Associative.ConstructorSound', 'Compiler.Extraction.Dispatch.Effects.SourceConstructorsAt',
                 'Compiler.Extraction.AddressMask.Constructs', 'Compiler.Extraction.ArithmeticShift.Constructs'}
    for name, (domain, _) in fields.items():
        if forbidden & gate.step.constants_below(value, domain):
            raise ValueError('native word consumer assumes preservation: ' + name)
    native = joint.app(value, lets['nativeChildren'][0], TRACE + 'children')
    named(value, native[1:5], lets['nativeChildren'][1], ('ops', 'allocate', 'safety', 'owner'))
    named(value, native[-4:], lets['nativeChildren'][1], ('base', 'growth', 'usizeBits', 'depth'))
    joint.app(value, native[5], 'Compiler.Extraction.Dispatch.wordDispatchMeaning')
    result = joint.app(value, root, OWNED + 'Semantic.Ensures')
    meaning = joint.app(value, result[-5], 'Compiler.Extraction.Dispatch.wordDispatchMeaning')
    named(value, meaning, context, ('env', 'other'))
    joint.path(value, result[-4], context, (OWNED + 'World.graph',), 'before')
    outcome = joint.app(value, result[-3], 'Prod.fst')[-1]
    named(value, local_call(value, outcome, context, 'action'), context, ('before',))
    reached = joint.app(value, result[-2], OWNED + 'World.graph')[-1]
    reached = joint.app(value, reached, 'Prod.snd')[-1]
    named(value, local_call(value, reached, context, 'action'), context, ('before',))
    post, _, conclusion, post_context = telescope(value, result[-1], context)
    anonymous = [name for name in post if name.startswith('a.')]
    if len(anonymous) != 1 or set(post) != {'found', 'after', 'id'} | set(anonymous):
        raise ValueError('native word postcondition lost the returned ID')
    equality = joint.app(value, post[anonymous[0]][0], 'Eq')
    named(value, equality[-2:-1], post[anonymous[0]][1], ('found',))
    joint.path(value, equality[-1], post[anonymous[0]][1], ('Option.some',), 'id')
    equality = joint.app(value, conclusion, 'Eq')
    read = joint.app(value, equality[-2], INTERNER + 'Heap.read')
    named(value, read, post_context, ('after', 'id'))
    joint.path(value, equality[-1], post_context, ('Option.some',), 'expected')
    # The scoped domain contains source key construction, not a heap, result or oracle.
    value = definitions[TRACE + 'RequestKey']['value']
    fields, _, root, context = telescope(value)
    if set(fields) != {'request', 'key'}:
        raise ValueError('request key domain gained a preservation condition')
    equality = joint.app(value, root, 'Eq')
    encoded = joint.app(value, equality[-2], 'Compiler.Extraction.Cache.KeyCode.run')
    joint.path(value, encoded[-3], context, (INTERNER + 'Request.item',), 'request')
    joint.path(value, encoded[-2], context, ('Compiler.Extraction.Cache.Key.arguments',), 'key')
    joint.path(value, encoded[-1], context, (INTERNER + 'Request.sequence',), 'request')
    joint.path(value, equality[-1], context, ('Option.some',), 'key')
    value = definitions[TRACE + 'Words.mk']['type']
    fields, _, root, context = telescope(value)
    if set(fields) != {'env', 'other', 'children', 'correct', 'addresses', 'shifts'}:
        raise ValueError('word contract changed its three dispatcher obligations')
    correct = joint.app(value, fields['correct'][0], 'Compiler.Extraction.Associative.ConstructorSound')
    named(value, correct[-1:], fields['correct'][1], ('children',))
    meaning = joint.app(value, correct[-2], 'Compiler.Extraction.Dispatch.wordBaseMeaning')
    named(value, meaning, fields['correct'][1], ('env', 'other'))
    addresses = joint.app(value, fields['addresses'][0], 'Compiler.Extraction.AddressMask.Constructs')
    named(value, addresses[-3:-2], fields['addresses'][1], ('env',))
    joint.path(value, addresses[-2], fields['addresses'][1], ('Compiler.Extraction.ArithmeticShift.shiftMeaning',), 'other')
    joint.path(value, addresses[-1], fields['addresses'][1], ('Compiler.Extraction.Associative.Constructors.operation',), 'children')
    shifts = joint.app(value, fields['shifts'][0], 'Compiler.Extraction.ArithmeticShift.Constructs')
    meaning = joint.app(value, shifts[-2], 'Compiler.Extraction.AddressMask.addressMeaning')
    named(value, meaning, fields['shifts'][1], ('env', 'other'))
    joint.path(value, shifts[-1], fields['shifts'][1], ('Compiler.Extraction.Associative.Constructors.operation',), 'children')
    named(value, joint.app(value, root, TRACE + 'Words'), context, ('env', 'other', 'children'))
    return {'recursiveWordPremisesAbsent': True, 'fixedStreamAndDepthBound': True,
            'nativeAdmissionExplicit': True, 'sameNativeResultAndGraphObserved': True, 'replayStreamAdmissionDerived': True,
            'composedProductionTheoremVerified': False}


def controls(output, env, lean):
    groups = (
        ('prefix', 'StorageExecutionFaults', (
            ('false-append', 'state.published = true → state.appended = true ∧ input.room = true',
             'state.published = true → state.appended = false ∧ input.room = true', 1),
            ('false-capacity', 'state.published = true → state.appended = true ∧ input.room = true',
             'state.published = true → state.appended = true ∧ input.room = false', 1),
        )),
        ('candidate', 'InternerNativeSuffixWords', (
            ('wrong-literal-guard', '(pushes : item.kind = 2#32 → PushValues meaning)',
             '(pushes : item.kind = 1#32 → PushValues meaning)', 1),
            ('wrong-candidate-sequence', '(bound : keyCode.run input.item normalized.items sequence = some key)',
             '(bound : keyCode.run input.item normalized.items 0 = some key)', 1),
        )),
        ('request', 'InternerAllocationWordModels', (
            ('unrelated-item', 'keyCode.run request.item key.arguments request.sequence = some key',
             'keyCode.run {request.item with data := 0} key.arguments request.sequence = some key', 1),
            ('missing-request-operands', 'request.item.eval (Dispatch.wordDispatchMeaning env other) before.read request.arguments request.sequence = some value',
             'request.item.eval (Dispatch.wordDispatchMeaning env other) before.read [] request.sequence = some value', 2),
        )),
        ('native', 'InternerAllocationNativeWords', (
            ('wrong-word-premise', '(evaluated : key.eval (Dispatch.wordDispatchMeaning env other) before.graph.read = some expected)',
             '(evaluated : key.eval (Dispatch.wordDispatchMeaning env other) before.graph.read = some (expected + 1))', 1),
            ('wrong-key-kind', '(operation : key.kind = 1)', '(operation : key.kind = 2)', 1),
        )),
    )
    records = []
    for group, module, mutations in groups:
        code = source('Compiler.Extraction.' + module)
        prefix = 'recursive-words-' + group + '-'
        records += checked_controls(output, [mutation_check(output, prefix + 'unchanged', code, True, env, lean)])
        for name, old, new, count in mutations:
            if code.count(old) != count:
                raise ValueError('ambiguous word mutation: ' + name + ': ' + str(code.count(old)))
            records += checked_controls(output, [mutation_check(output, prefix + name, code.replace(old, new), False, env, lean)])
    return records
