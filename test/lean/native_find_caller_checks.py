"""Audit native find ownership and its combined word-preservation contract.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
import native_find_checks as words
from native_miss_frame_checks import named
from native_resource_admission_checks import telescope
from native_recursive_invocation_checks import audit_native_admission
from native_algebraic_dispatch_checks import source
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check

NS, OWNED, ITEM = gate.NS, gate.OWNED, gate.ITEM
CALLER, TESTS = OWNED + 'Caller.', NS + 'FindWordsTests.'
MODULE = words.MODULE
CLAIMS = [OWNED + name for name in ('Good.source_frame', 'body_ready_at', 'body_ready', 'Caller.find_ready_at', 'Caller.find_ready')]
CLAIMS += [NS + name for name in ('CallFrame.unpublished_source', 'CallFrame.insertion_source',
                                 'native_find_caller', 'production_find_verified')]
CLAIMS += [TESTS + name for name in ('prepared_verified', 'certified_verified')]
INTERFACES = ()


def audit(claims):
    required = {
        OWNED + 'Good.source_frame': {OWNED + 'Good.backed'},
        OWNED + 'body_ready_at': {OWNED + 'body_split', OWNED + 'post_ready',
                                 words.NORMALIZATION + 'take_refines'},
        CALLER + 'find_ready_at': {CALLER + 'initialize_verified', CALLER + 'CanClose'},
        NS + 'CallFrame.unpublished_source': {OWNED + 'Good.source_frame',
                                             OWNED + 'Insertion.Native.insert_unpublished_projected'},
        NS + 'CallFrame.insertion_source': {NS + 'CallFrame.unpublished_source',
            OWNED + 'Insertion.Native.insert_insertion_coverage', NS + 'CallFrame.published_frame',
            NS + 'CallFrame.publication_rollback_frame', NS + 'CallFrame.transferred',
            NS + 'CallFrame.backing_oom_execution_at'},
        NS + 'native_find_caller': {CALLER + 'invoke_verified', CALLER + 'find_ready_at',
            OWNED + 'body_ready_at', OWNED + 'miss_post_at', OWNED + 'Insertion.Native.caller_input',
            NS + 'CallFrame.caller', NS + 'Enclosing.unfold_frames', NS + 'dispatcher_keeps',
            NS + 'CallFrame.insertion_source', OWNED + 'Publication.publish_held'},
        NS + 'production_find_verified': {NS + 'native_find_caller', words.TRACE + 'native_find_words'},
        TESTS + 'prepared_verified': {NS + 'production_find_verified', ITEM + 'ConstantFoldTests.established',
                                     ITEM + 'ConstantNegationTests.established'},
        TESTS + 'certified_verified': {TESTS + 'prepared_verified', 'Compiler.Extraction.Cache.put_valid'},
        OWNED + 'body_ready': {OWNED + 'body_ready_at'},
        CALLER + 'find_ready': {CALLER + 'find_ready_at'},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('native caller lost shared composition: ' + name + ': ' + ', '.join(sorted(missing)))
    for name in CLAIMS[:-2]:
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('native caller depends on a fixture: ' + name)
    return {'checkedDependencies': sorted(required), 'exactNativeFindBodyVerified': True,
            'childFramesAndCleanupAdmissionDerived': True, 'sharedReadinessSpecializations': True,
            'initialNativeAdmissionExplicit': True, 'terminationVerified': False,
            'composedProductionTheoremVerified': False}


def audit_statement(value, *, semantic):
    fields, lets, root, context = telescope(value)
    expected = {'σ', 'ops', 'allocate', 'safety', 'owner', 'usizeBits', 'base', 'growth', 'debug',
                'admitted', 'typed', 'depth', 'rows', 'parent', 'stack', 'source', 'request', 'before',
                'initial', 'data', 'capacity', 'facts', 'represented', 'privateSource', 'array',
                'address', 'native', 'item', 'sameItem', 'domain', 'memory', 'pointer', 'allocated'}
    expected |= ({'env', 'other', 'seed', 'mismatch', 'closedQuery', 'capacityQuery', 'classificationQuery',
                  'pushes', 'pushValues', 'valid', 'expected', 'evaluated'} if semantic else {'meaning'})
    if set(fields) != expected or set(lets) != {'nativeBase', 'nativeChildren', 'actual', 'buffer', 'input'}:
        raise ValueError('native caller changed its exact admission boundary')
    forbidden = {CALLER + 'Verified', CALLER + 'CanClose', OWNED + 'ReadyToClose',
                 OWNED + 'Semantic.Verified', OWNED + 'Semantic.Ensures', OWNED + 'Contracts',
                 OWNED + 'GraphContracts', OWNED + 'Semantic.GraphContracts', NS + 'InvocationPost',
                 NS + 'CallFrame', NS + 'FramePost', words.TRACE + 'RecursiveSources',
                 words.TRACE + 'Words', 'Compiler.Extraction.Associative.ConstructorSound'}
    for name, (term, _) in fields.items():
        if forbidden & gate.step.constants_below(value, term):
            raise ValueError('native caller assumes its preservation: ' + name)
    audit_native_admission(value, fields, semantic=semantic)
    words.audit_find_geometry(value, lets, word_meaning=semantic)
    words.audit_item_and_scratch(value, fields)
    term, scope = fields['admitted']
    host = joint.app(value, term, words.NORMALIZATION + 'Admitted')[-1]
    joint.path(value, host, scope, (OWNED + 'Insertion.Operations.arguments',), 'ops')
    term, scope = fields['stack']
    stack = joint.app(value, term, NS + 'Enclosing')
    named(value, stack[:1] + stack[2:3] + stack[-1:], scope, ('safety', 'owner', 'parent'))
    joint.path(value, stack[1], scope, (ITEM + 'ShiftInput.Context.allocator',), 'base')
    term, scope = fields['typed']
    named(value, joint.app(value, term, 'Compiler.Extraction.AssemblyItem.Initializers.DebugTyped'), scope, ('debug',))
    term, scope = fields['domain']
    member = joint.app(value, term, 'Membership.mem')
    named(value, member[-2:-1], scope, ('Compiler.Extraction.AssemblyItem.itemTagValues',))
    joint.path(value, member[-1], scope, ('Nat.cast', 'BitVec.toNat', 'Compiler.Extraction.Cache.Item.kind',
               'Compiler.Extraction.AssemblyClone.Value.item'), 'native')
    if semantic:
        external, allocator, source_term, values, meaning, action, initial, post = joint.app(
            value, root, OWNED + 'Semantic.Verified')[-8:]
        named(value, joint.app(value, meaning, 'Compiler.Extraction.Dispatch.wordDispatchMeaning'), context, ('env', 'other'))
        post_context = context[:]
        for name in ('id', 'after'):
            node = value['nodes'][post]
            if node[0] != 'lambda':
                raise ValueError('native caller lost its word postcondition')
            post_context.append(name)
            post = node[-1]
        equality = joint.app(value, post, 'Eq')
        named(value, joint.app(value, equality[-2], words.INTERNER + 'Heap.read'), post_context, ('after', 'id'))
        joint.path(value, equality[-1], post_context, ('Option.some',), 'expected')
    else:
        external, allocator, source_term, values, action, initial = joint.app(value, root, CALLER + 'Verified')[-6:]
    joint.path(value, external, context, (ITEM + 'ShiftInput.Context.external',), 'nativeBase')
    joint.path(value, allocator, context, (ITEM + 'ShiftInput.Context.allocator',), 'base')
    named(value, [source_term, initial], context, ('source', 'input'))
    joint.path(value, values, context, (words.INTERNER + 'Request.arguments',), 'request')
    words.audit_find_action(value, action, context)


def audit_statements(rows, interfaces=()):
    statements = {row['theorem']: row['statement'] for row in rows}
    audit_statement(statements[NS + 'native_find_caller'], semantic=False)
    audit_statement(statements[NS + 'production_find_verified'], semantic=True)
    value = statements[TESTS + 'certified_verified']
    fields, lets, root, context = telescope(value)
    if set(fields) != {'safety', 'negate', 'permitted', 'depth'} or lets:
        raise ValueError('complete native fixture acquired a correctness or admission premise')
    external, allocator, source_term, arguments, meaning, action, initial, post = joint.app(value, root, OWNED + 'Semantic.Verified')[-8:]
    joint.path(value, external, context, (OWNED + 'Publication.external', OWNED + 'Insertion.Operations.arguments'),
               OWNED + 'Insertion.Native.CallerGrowingChainTests.ops')
    words.numeral(value, allocator, 7)
    joint.app(value, meaning, TESTS + 'meaning')
    for term, path in ((source_term, (ITEM + 'RecursiveTests.Call.source',)),
                       (arguments, (words.INTERNER + 'Request.arguments', ITEM + 'RecursiveTests.Call.request'))):
        for component in path:
            term = joint.app(value, term, component)[-1]
        args = joint.app(value, term, TESTS + 'call')
        named(value, args[:2], context, ('safety', 'negate'))
        words.numeral(value, args[2], 1)
    args = joint.app(value, action, TESTS + 'action')
    named(value, args[:2] + args[3:], context, ('safety', 'negate', 'depth', 'permitted'))
    words.numeral(value, args[2], 1)
    args = joint.app(value, initial, TESTS + 'initial')
    named(value, args[:2], context, ('safety', 'negate'))
    words.numeral(value, args[2], 1)
    word_value = statements[TESTS + 'certified_words']
    _, _, word_root, word_context = telescope(word_value)
    word_post = joint.app(word_value, word_root, OWNED + 'Semantic.Ensures')[-1]
    for name in ('id', 'after'):
        node, word_node = value['nodes'][post], word_value['nodes'][word_post]
        if node[0] != 'lambda' or word_node[0] != 'lambda':
            raise ValueError('complete native fixture lost its returned-word postcondition')
        context, word_context = context + [name], word_context + [name]
        post, word_post = node[-1], word_node[-1]
    if gate.named(value, post, context) != gate.named(word_value, word_post, word_context):
        raise ValueError('complete native fixture changed its word postcondition')
    return {'sameNativeFindBodyAndInputBound': True, 'existingCallerAndSemanticPredicates': True,
            'noChildFrameOrCleanupPremise': True, 'fixtureInitialAdmissionDerived': True,
            'ordinarySourceAndScopePreserved': True, 'bodyResultAndGraphRetainedByCleanup': True,
            'composedProductionTheoremVerified': False}


def controls(output, env, lean):
    groups = (
        ('source', 'InternerNativeInsertionSource', (
            ('unrelated-retained-source', 'after.memory.memory.heap.lookup source.allocation = some cell)',
             'before.memory.memory.heap.lookup source.allocation = some cell)', 1),
            ('missing-item-domain', '(domain : (native.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)', '(domain : True)', 1),
            ('unrelated-key', '(aligned : key.arguments = normalized.items)', '(aligned : key.arguments = [])', 1),
        )),
        ('owned', 'InternerOwnedProofs', (
            ('unrelated-take', 'takeOwned normalizationOwnershipCode external allocator handle before.memory = (.ok (slice, remaining), memory)',
             'takeOwned normalizationOwnershipCode external allocator handle before.memory = (.ok (slice, remaining), before.memory)', 1),
            ('unrelated-key', 'Interner.makeKey request handle.values = .ok key → key.arguments = slice.items →',
             'Interner.makeKey request [] = .ok key → key.arguments = slice.items →', 1),
        )),
        ('prefix', 'InternerCallerProofs', (
            ('unrelated-initialization', '(.ok handle.values, ⟨world, {lookup := some handle}⟩) →',
             '(.ok request.arguments, ⟨world, {lookup := some handle}⟩) →', 1),
        )),
        ('native', 'InternerNativeFindCaller', (
            ('missing-source', '(represented : Represents before.memory.memory source request.arguments)', '(represented : True)', 1),
            ('missing-private-source', '(privateSource : Caller.SourcePrivate source before.memory.effects.keys)', '(privateSource : True)', 1),
            ('missing-array-source', '(array : ArraySource source before.memory.memory)', '(array : True)', 1),
            ('missing-host', '(admitted : Admitted ops.arguments)', '(admitted : True)', 1),
            ('missing-item-domain', '(domain : (native.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)', '(domain : True)', 1),
            ('missing-item-binding', '(sameItem : native.item = request.item)', '(sameItem : True)', 1),
            ('wrong-scratch', '(.array 2 word)', '(.array 3 word)', 1),
            ('unrelated-source-values', '(represented : Represents before.memory.memory source request.arguments)',
             '(represented : Represents before.memory.memory source [])', 1),
        )),
        ('production', 'InternerNativeFindProduction', (
            ('missing-item-domain', '(domain : (native.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)', '(domain : True)', 1),
            ('wrong-word', '(fun id after => after.read id = some expected) := by',
             '(fun id after => after.read id = some (expected + 1)) := by', 1),
        )),
        ('attachment', 'InternerNativeFindWordsTests', (
            ('omit-cleanup', 'Caller.invoke (Publication.external ops.arguments) 7 (action safety negate value depth permitted) (initial safety negate value)',
             '(action safety negate value depth permitted) ⟨initial safety negate value, {lookup := none}⟩', 1),
        )),
    )
    records = []
    for group, module, mutations in groups:
        code = source('Compiler.Extraction.' + module)
        prefix = 'native-find-caller-' + group + '-'
        records += checked_controls(output, [mutation_check(output, prefix + 'unchanged', code, True, env, lean)])
        for name, old, new, count in mutations:
            if code.count(old) != count:
                raise ValueError('ambiguous native caller mutation: ' + name + ': ' + str(code.count(old)))
            records += checked_controls(output, [mutation_check(output, prefix + name, code.replace(old, new), False, env, lean)])
    return records
