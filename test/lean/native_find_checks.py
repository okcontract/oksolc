"""Audit exact native find words, shared caller admission and existing fixtures.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
from native_miss_frame_checks import named
from native_resource_admission_checks import telescope
from native_checkpoint_constructor_checks import numeral, before_id
from native_step_builder_checks import native_base
from native_recursive_invocation_checks import audit_native_admission
from native_algebraic_dispatch_checks import source
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check

NS, OWNED, ITEM = gate.NS, gate.OWNED, gate.ITEM
TRACE = NS + 'AllocationTrace.'
ENTRY = OWNED + 'Caller.ProtocolTrace.Native.CheckpointEntry.'
CALLER = OWNED + 'Caller.'
NORMALIZATION = OWNED.removesuffix('OwnedCall.')
MEMORY = 'Compiler.ZigAir.Memory.'
INTERNER = 'Compiler.Extraction.Interner.'
TESTS = NS + 'FindWordsTests.'
MODULE = 'Compiler.Extraction.InternerNativeFindWordsTests'
CLAIMS = [ENTRY + 'caller_induction_from_sources']
CLAIMS += [TRACE + name for name in ('nativeInputGraphReplay_contracts', 'callerModel_safe', 'native_find_words')]
CLAIMS += [TESTS + name for name in ('prepared_words', 'certified_words', 'ordinary_failure', 'successful_word')]
INTERFACES = ()


def audit(claims):
    required = {
        ENTRY + 'caller_induction_from_sources': {OWNED + 'Insertion.Native.caller_input', NS + 'CallFrame.caller',
            OWNED + 'Caller.ProtocolTrace.initialized_taken_recorded', ENTRY + 'miss_from_recursive_sources'},
        TRACE + 'nativeInputGraphReplay_contracts': {TRACE + 'insertionReplay_safe', TRACE + 'publish_safe'},
        TRACE + 'callerModel_safe': {TRACE + 'nativeInputGraphReplay_contracts', INTERNER + 'Scoped.find_safe_for',
            'Compiler.Extraction.Dispatch.default_key_simplify_safe'},
        TRACE + 'native_find_words': {ENTRY + 'caller_induction_from_sources', ENTRY + 'find_projected',
            TRACE + 'recursive_sources', TRACE + 'recursive_words', TRACE + 'callerModel_safe',
            NS + 'ChildTrace.HostLift.hosts', NS + 'context_erases', TRACE + 'children_erases',
            ITEM + 'ProtocolTrace.EntryProjected.words', CALLER + 'ProtocolTrace.EffectTransport.find',
            CALLER + 'ProtocolTrace.find_erases'},
        TESTS + 'prepared_words': {TRACE + 'native_find_words', ITEM + 'ConstantFoldTests.prepared',
            ITEM + 'ConstantNegationTests.prepared', ITEM + 'ConstantFoldTests.established',
            ITEM + 'ConstantNegationTests.established'},
        TESTS + 'certified_words': {TESTS + 'certified_verified', 'Compiler.Extraction.Cache.put_valid'},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('native find lost shared composition: ' + name + ': ' + ', '.join(sorted(missing)))
    for name in CLAIMS[:4]:
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('native find depends on a fixture: ' + name)
    return {'checkedDependencies': sorted(required), 'exactNativeFindWordsVerified': True,
            'recordedHostsAndRecursiveWordsDerived': True, 'constructorEntrySpecializesCaller': True,
            'ordinaryOutcomesOnly': True, 'nativeFindBodyVerified': False,
            'composedProductionTheoremVerified': False}


def audit_find_geometry(value, lets, *, word_meaning=True):
    if word_meaning:
        native_base(value, *lets['nativeBase'])
    else:
        term, scope = lets['nativeBase']
        named(value, joint.app(value, term, NS + 'callerContext')[-7:], scope,
              ('ops', 'allocate', 'safety', 'owner', 'meaning', 'base', 'growth'))
    term, scope = lets['nativeChildren']
    named(value, joint.app(value, term, NS + 'unfold')[-4:], scope, ('nativeBase', 'owner', 'usizeBits', 'depth'))
    term, scope = lets['actual']
    primitives = joint.app(value, term, ITEM + 'ShiftInput.Context.primitives')
    named(value, primitives[-3:], scope, ('source', 'address', 'native'))
    named(value, joint.app(value, primitives[-4], NS + 'context')[-5:], scope,
          ('nativeBase', 'owner', 'usizeBits', 'nativeChildren', 'debug'))
    term, scope = lets['buffer']
    buffer = joint.app(value, term, MEMORY + 'WordArray.View.mk')
    before_id(value, buffer[-3], scope)
    numeral(value, buffer[-2], 0)
    numeral(value, buffer[-1], 2)
    term, scope = lets['input']
    world = joint.app(value, term, OWNED + 'World.mk')
    joint.path(value, world[-2], scope, (OWNED + 'World.graph',), 'before')
    previous = value['nodes'][world[-1]]
    if previous[0] != 'let':
        raise ValueError('native find changed its source memory update')
    joint.path(value, previous[3], scope, (OWNED + 'World.memory',), 'before')
    scope = scope + ['previousMemory']
    session = joint.app(value, previous[4], NORMALIZATION + 'Session.mk')
    for index, field in ((-3, 'heap'), (-1, 'effects')):
        joint.path(value, session[index], scope, (NORMALIZATION + 'Session.' + field,), 'previousMemory')
    named(value, session[-2:-1], scope, ('memory',))


def audit_find_action(value, body, scope):
    action = joint.app(value, body, CALLER + 'findBody')[-8:]
    joint.path(value, action[0], scope, (ITEM + 'ShiftInput.Context.external',), 'nativeBase')
    for index, field in ((1, 'budget'), (2, 'allocator'), (4, 'queries')):
        joint.path(value, action[index], scope, (ITEM + 'ShiftInput.Context.' + field,), 'base')
    named(value, [action[3], *action[5:]], scope, ('actual', 'source', 'buffer', 'request'))


def audit_item_and_scratch(value, fields):
    term, scope = fields['item']
    represented = joint.app(value, term, 'Compiler.Extraction.AssemblyClone.NativeFields.Represents')
    joint.path(value, represented[-3], scope, (NORMALIZATION + 'Session.memory', OWNED + 'World.memory'), 'before')
    named(value, represented[-2:], scope, ('address', 'native'))
    term, scope = fields['sameItem']
    equality = joint.app(value, term, 'Eq')
    joint.path(value, equality[-2], scope, ('Compiler.Extraction.AssemblyClone.Value.item',), 'native')
    joint.path(value, equality[-1], scope, (INTERNER + 'Request.item',), 'request')
    term, scope = fields['allocated']
    equality = joint.app(value, term, 'Eq')
    allocation = joint.app(value, equality[-2], MEMORY + 'allocate')
    joint.path(value, allocation[-2], scope, (NORMALIZATION + 'Session.memory', OWNED + 'World.memory'), 'before')
    array = joint.app(value, allocation[-1], MEMORY + 'Ty.array')
    numeral(value, array[-2], 2)
    named(value, array[-1:], scope, (MEMORY + 'WordArray.word',))
    returned = joint.app(value, equality[-1], 'Except.ok')[-1]
    named(value, joint.app(value, returned, 'Prod.mk')[-2:], scope, ('pointer', 'memory'))


def audit_statements(rows, interfaces=()):
    statements = {row['theorem']: row['statement'] for row in rows}
    value = statements[TRACE + 'native_find_words']
    fields, lets, root, context = telescope(value)
    expected = {'σ', 'ops', 'allocate', 'safety', 'owner', 'usizeBits', 'env', 'other', 'base', 'growth',
                'debug', 'seed', 'mismatch', 'admitted', 'typed', 'closedQuery', 'capacityQuery', 'classificationQuery',
                'pushes', 'pushValues', 'depth', 'rows', 'parent', 'stack', 'source', 'request', 'before', 'initial',
                'data', 'capacity', 'facts', 'represented', 'privateSource', 'array', 'address', 'native', 'item',
                'sameItem', 'memory', 'pointer', 'allocated', 'valid', 'expected', 'evaluated'}
    if set(fields) != expected or set(lets) != {'nativeBase', 'nativeChildren', 'actual', 'buffer', 'input', 'ran'}:
        raise ValueError('native find changed its exact premise boundary')
    forbidden = {TRACE + 'Words', TRACE + 'RecursiveSources', INTERNER + 'Safe', NS + 'InvocationPost',
                 OWNED + 'Semantic.Ensures', OWNED + 'Semantic.Verified', CALLER + 'Verified',
                 OWNED + 'Contracts', OWNED + 'GraphContracts', OWNED + 'Semantic.GraphContracts',
                 'Compiler.Extraction.Associative.ConstructorSound'}
    for name, (domain, _) in fields.items():
        if forbidden & gate.step.constants_below(value, domain):
            raise ValueError('native find assumes its preservation: ' + name)
    audit_native_admission(value, fields)
    audit_find_geometry(value, lets)
    term, scope = lets['ran']
    external, allocator, body, initial = joint.app(value, term, CALLER + 'invoke')[-4:]
    joint.path(value, external, scope, (ITEM + 'ShiftInput.Context.external',), 'nativeBase')
    joint.path(value, allocator, scope, (ITEM + 'ShiftInput.Context.allocator',), 'base')
    named(value, [initial], scope, ('input',))
    audit_find_action(value, body, scope)
    meaning, before, result, after, post = joint.app(value, root, OWNED + 'Semantic.Ensures')[-5:]
    named(value, joint.app(value, meaning, 'Compiler.Extraction.Dispatch.wordDispatchMeaning'), context, ('env', 'other'))
    joint.path(value, before, context, (OWNED + 'World.graph',), 'before')
    joint.path(value, result, context, ('Prod.fst',), 'ran')
    joint.path(value, after, context, (OWNED + 'World.graph', OWNED + 'State.world', 'Prod.snd'), 'ran')
    post_context = context[:]
    for name in ('id', 'after'):
        node = value['nodes'][post]
        if node[0] != 'lambda':
            raise ValueError('native find lost its returned-word postcondition')
        post_context.append(name)
        post = node[-1]
    equality = joint.app(value, post, 'Eq')
    named(value, joint.app(value, equality[-2], INTERNER + 'Heap.read'), post_context, ('after', 'id'))
    joint.path(value, equality[-1], post_context, ('Option.some',), 'expected')
    audit_item_and_scratch(value, fields)
    value = statements[TESTS + 'certified_words']
    fields, lets, root, context = telescope(value)
    if set(fields) != {'safety', 'negate', 'permitted', 'depth'} or lets:
        raise ValueError('native find fixture acquired an admission or preservation premise')
    meaning, before, result, after, _ = joint.app(value, root, OWNED + 'Semantic.Ensures')[-5:]
    joint.app(value, meaning, TESTS + 'meaning')
    graph = joint.app(value, before, OWNED + 'World.graph')[-1]
    call = joint.app(value, graph, ITEM + 'RecursiveTests.Call.constructed')[-1]
    arguments = joint.app(value, call, TESTS + 'call')
    named(value, arguments[:2], context, ('safety', 'negate'))
    numeral(value, arguments[-1], 1)
    result = joint.app(value, result, 'Prod.fst')[-1]
    after = joint.app(value, after, OWNED + 'World.graph')[-1]
    after = joint.app(value, after, OWNED + 'State.world')[-1]
    after = joint.app(value, after, 'Prod.snd')[-1]
    for execution in (result, after):
        arguments = joint.app(value, execution, TESTS + 'ran')
        named(value, arguments[:2] + arguments[3:], context, ('safety', 'negate', 'depth', 'permitted'))
        numeral(value, arguments[2], 1)
    return {'sameRawFindBodyAndCleanupBound': True, 'originalRepresentedItemAndScratchBound': True,
            'sameNativeResultAndGraphObserved': True, 'noChildOrFinalResultPremise': True,
            'fixtureInitialSemanticsDerived': True, 'fixturePermittedGrowthCovered': True,
            'nativeInitialAdmissionExplicit': True, 'callerOwnershipAndCleanupCorrespondenceVerified': False,
            'composedProductionTheoremVerified': False}


def controls(output, env, lean):
    groups = (
        ('caller', 'InternerCheckpointNativeCaller', (
            ('missing-item', '(item : AssemblyClone.NativeFields.Represents before.memory.memory address native)', '(item : True)', 1),
            ('missing-item-binding', '(sameItem : native.item = request.item)', '(sameItem : True)', 1),
            ('missing-source-privacy', '(privateSource : Caller.SourcePrivate source before.memory.effects.keys)', '(privateSource : True)', 1),
            ('wrong-scratch', '(.array 2 word)', '(.array 3 word)', 1),
            ('unrelated-history', 'actual.2.events ++ trailing = stream', 'actual.2.events ++ trailing = []', 1),
        )),
        ('model', 'InternerAllocationWordModels', (
            ('missing-item-binding', '(sameItem : native.item = request.item)', '(sameItem : True)', 2),
            ('wrong-input', '(sameItem : native.item = request.item)', '(sameItem : native.item = {request.item with data := 0})', 2),
        )),
        ('native', 'InternerNativeFindWords', (
            ('missing-source', '(represented : Represents before.memory.memory source request.arguments)', '(represented : True)', 1),
            ('missing-host', '(admitted : Admitted ops.arguments)', '(admitted : True)', 1),
            ('missing-item-binding', '(sameItem : native.item = request.item)', '(sameItem : True)', 1),
            ('wrong-evaluated-word', 'request.sequence = some expected)', 'request.sequence = some (expected + 1))', 1),
            ('wrong-result-word', '(fun id after => after.read id = some expected) := by', '(fun id after => after.read id = some (expected + 1)) := by', 1),
            ('wrong-native-address', '(item : AssemblyClone.NativeFields.Represents before.memory.memory address native)',
             '(item : AssemblyClone.NativeFields.Represents before.memory.memory ⟨0, 0⟩ native)', 1),
            ('wrong-scratch', '(.array 2 word)', '(.array 3 word)', 1),
        )),
        ('attachment', 'InternerNativeFindWordsTests', (
            ('wrong-result', '(.error (.language .outOfMemory), ⟨none, none, false⟩)', '(.ok 5, ⟨none, none, false⟩)', 1),
            ('wrong-initial-environment', 'def env : AddressMask.Environment := ⟨⟨0, 0⟩, 0, 0⟩',
             'def env : AddressMask.Environment := ⟨⟨1, 0⟩, 0, 0⟩', 1),
            ('wrong-success-word', '(.ok 5, some 0, ⟨none, some (call safety false 1).normalized, true⟩)',
             '(.ok 5, some 1, ⟨none, some (call safety false 1).normalized, true⟩)', 1),
            ('missing-source-operand', 'input.source ⟨input.constructed.memory.memory.nextId, 0, 2⟩ input.request',
             'input.source ⟨input.constructed.memory.memory.nextId, 0, 2⟩ {input.request with arguments := []}', 1),
        )),
    )
    records = []
    for group, module, mutations in groups:
        code = source('Compiler.Extraction.' + module)
        prefix = 'native-find-' + group + '-'
        records += checked_controls(output, [mutation_check(output, prefix + 'unchanged', code, True, env, lean)])
        for name, old, new, count in mutations:
            if code.count(old) != count:
                raise ValueError('ambiguous native find mutation: ' + name + ': ' + str(code.count(old)))
            records += checked_controls(output, [mutation_check(output, prefix + name, code.replace(old, new), False, env, lean)])
    return records
