"""Audit complete native invocation preservation from closed recursive replay.
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
ENTRY = ITEM + 'ProtocolTrace.'
INTERNER = 'Compiler.Extraction.Interner.'
CLAIMS = [ENTRY + 'EntryProjected.words', TRACE + 'recursive_invocation_verified']
INTERFACES = ()


def audit(claims):
    required = {
        ENTRY + 'EntryProjected.words': {OWNED + 'Recursive.safe_at', OWNED + 'Semantic.Ensures.cursor_iff'},
        TRACE + 'recursive_invocation_verified': {
            ENTRY + 'EntryProjected.words', ENTRY + 'CheckpointEntry.item_from_sources',
            TRACE + 'recursive_sources', TRACE + 'recursive_words', TRACE + 'requestModel_safe',
            TRACE + 'children_erases', TRACE + 'checkpoint_observations_traced', NS + 'context_erases',
            ENTRY + 'EffectTransport.item', ENTRY + 'item_erases', NS + 'Enclosing.unfold_invocation_frame'},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('complete invocation lost shared proof: ' + name + ': ' + ', '.join(sorted(missing)))
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('complete invocation depends on fixtures: ' + name)
    return {'checkedDependencies': sorted(required), 'completeNativeInvocationScopeAndWordsDerived': True,
            'properChildWordsAndReplayDerived': True, 'actualHistoryAdmissionDerived': True,
            'ordinaryOutcomesOnly': True, 'nativeInitialAdmissionDerived': False,
            'terminationVerified': False, 'composedProductionTheoremVerified': False}


def audit_native_admission(value, fields, *, semantic=True):
    initial, scope = fields['initial']
    named(value, local_call(value, initial, scope, 'parent'), scope, ('before',))
    facts, scope = fields['facts']
    facts = joint.app(value, facts, OWNED + 'NativeGraph.Facts')
    named(value, facts[1:2] + facts[3:], scope, ('safety', 'owner', 'data', 'capacity', 'before', 'rows'))
    joint.path(value, facts[2], scope, (ITEM + 'ShiftInput.Context.allocator',), 'base')
    if semantic:
        valid, scope = fields['valid']
        valid = joint.app(value, valid, INTERNER + 'Invariant')
        named(value, joint.app(value, valid[-2], 'Compiler.Extraction.Dispatch.wordDispatchMeaning'), scope, ('env', 'other'))
        joint.path(value, valid[-1], scope, (OWNED + 'World.graph',), 'before')
    memory_path = ('Compiler.Extraction.Memory.Arguments.Normalization.Session.memory', OWNED + 'World.memory')
    represented, scope = fields['represented']
    represented = joint.app(value, represented, 'Compiler.ZigAir.Memory.WordArray.Represents')
    joint.path(value, represented[0], scope, memory_path, 'before')
    named(value, represented[1:2], scope, ('source',))
    joint.path(value, represented[-1], scope, (INTERNER + 'Request.arguments',), 'request')
    private_source, scope = fields['privateSource']
    private_source = joint.app(value, private_source, OWNED + 'Caller.SourcePrivate')
    named(value, private_source[:1], scope, ('source',))
    joint.path(value, private_source[-1], scope, (OWNED + 'Publication.Effects.keys',
               'Compiler.Extraction.Memory.Arguments.Normalization.Session.effects', OWNED + 'World.memory'), 'before')
    array, scope = fields['array']
    array = joint.app(value, array, OWNED + 'ArraySource')
    named(value, array[:1], scope, ('source',))
    joint.path(value, array[-1], scope, memory_path, 'before')
    if semantic:
        evaluated, scope = fields['evaluated']
        equality = joint.app(value, evaluated, 'Eq')
        joint.path(value, equality[-1], scope, ('Option.some',), 'expected')
        evaluated = joint.app(value, equality[-2], 'Compiler.Extraction.Cache.Item.eval')
        named(value, joint.app(value, evaluated[0], 'Compiler.Extraction.Dispatch.wordDispatchMeaning'), scope, ('env', 'other'))
        joint.path(value, evaluated[1], scope, (INTERNER + 'Heap.read', OWNED + 'World.graph'), 'before')
        for term, field in zip(evaluated[2:], ('item', 'arguments', 'sequence')):
            joint.path(value, term, scope, (INTERNER + 'Request.' + field,), 'request')


def audit_invocation_statement(value, *, recorded_hosts=True):
    fields, lets, root, context = telescope(value)
    expected = {'σ', 'ops', 'allocate', 'safety', 'owner', 'usizeBits', 'env', 'other', 'base', 'growth',
                'outerOps', 'outerAllocate', 'outerBase', 'outerGrowth', 'hosts', 'allocators', 'budgets', 'queries',
                'debug', 'seed', 'mismatch', 'admitted', 'outerAdmitted', 'typed', 'closedQuery',
                'capacityQuery', 'classificationQuery', 'pushes', 'pushValues', 'depth', 'rows', 'parent', 'stack',
                'source', 'request', 'before', 'initial', 'data', 'capacity', 'facts', 'represented', 'privateSource',
                'array', 'domain', 'valid', 'expected', 'evaluated'}
    if not recorded_hosts:
        expected -= {'outerOps', 'outerAllocate', 'outerBase', 'outerGrowth', 'hosts',
                     'allocators', 'budgets', 'queries', 'outerAdmitted'}
    if set(fields) != expected or set(lets) != {'nativeBase', 'nativeChildren'}:
        raise ValueError('complete invocation changed its premise boundary: ' + str(sorted(fields)))
    forbidden = {TRACE + 'Words', TRACE + 'RecursiveSources', INTERNER + 'Safe', NS + 'InvocationPost',
                 OWNED + 'Semantic.Ensures', 'Compiler.Extraction.Associative.ConstructorSound',
                 'Compiler.Extraction.Dispatch.Effects.SourceConstructorsAt', NS + 'FramePost'}
    for name, (domain, _) in fields.items():
        if forbidden & gate.step.constants_below(value, domain):
            raise ValueError('complete invocation assumes recursive preservation: ' + name)
    base, scope = lets['nativeBase']
    base = joint.app(value, base, NS + 'callerContext')
    named(value, base[1:5] + base[-2:], scope, ('ops', 'allocate', 'safety', 'owner', 'base', 'growth'))
    named(value, joint.app(value, base[5], 'Compiler.Extraction.Dispatch.wordDispatchMeaning'), scope, ('env', 'other'))
    children, scope = lets['nativeChildren']
    named(value, joint.app(value, children, NS + 'unfold')[-4:], scope, ('nativeBase', 'owner', 'usizeBits', 'depth'))
    result = joint.app(value, root, NS + 'InvocationPost')
    named(value, joint.app(value, result[-5], 'Compiler.Extraction.Dispatch.wordDispatchMeaning'), context, ('env', 'other'))
    frame = joint.app(value, result[-4], NS + 'GraphFrame')
    named(value, frame[1:2] + frame[3:], context, ('safety', 'owner', 'rows', 'parent'))
    joint.path(value, frame[2], context, (ITEM + 'ShiftInput.Context.allocator',), 'base')
    joint.path(value, result[-3], context, (OWNED + 'World.graph',), 'before')
    named(value, result[-1:], context, ('expected',))
    actual = joint.app(value, result[-2], ITEM + 'invoke')
    joint.path(value, actual[1], context, (ITEM + 'ShiftInput.Context.external',), 'nativeBase')
    joint.path(value, actual[2], context, (ITEM + 'ShiftInput.Context.budget',), 'base')
    joint.path(value, actual[3], context, (ITEM + 'ShiftInput.Context.allocator',), 'base')
    primitives = joint.app(value, actual[4], ITEM + 'ShiftInput.Context.primitives')
    native_context = joint.app(value, primitives[-2], NS + 'context')
    named(value, native_context[1:], context, ('nativeBase', 'owner', 'usizeBits', 'nativeChildren', 'debug'))
    named(value, primitives[-1:], context, ('source',))
    joint.path(value, actual[5], context, (ITEM + 'ShiftInput.Context.queries',), 'base')
    named(value, actual[6:], context, ('source', 'request', 'debug', 'before'))
    audit_native_admission(value, fields)
    # This existing interface retains both scope closure and the same native world.
    # Its full compiled definition remains covered by the original invocation audit.
    return {'sameRawInvocationBound': True, 'exactRequestAndExpectedWordBound': True,
            'nativeScopeAndGraphFrameRetained': True, 'noChildOrFinalResultPremise': True,
            'nativeInitialAdmissionExplicit': True, 'composedProductionTheoremVerified': False}


def audit_statements(rows, interfaces):
    statements = {row['theorem']: row['statement'] for row in rows}
    return audit_invocation_statement(statements[TRACE + 'recursive_invocation_verified'])


def controls(output, env, lean):
    groups = (
        ('entry', 'InternerConstructorEntryWords', (
            ('wrong-entry-cursor', 'allocationCursor := leading.length', 'allocationCursor := trailing.length', 1),
            ('wrong-captured-history', 'resources (actual.2.events ++ trailing)', 'resources (leading ++ trailing)', 1),
            ('wrong-model-word', '(fun id after => after.read id = some expected))', '(fun id after => after.read id = some (expected + 1)))', 1),
        )),
        ('native', 'InternerAllocationInvocationWords', (
            ('wrong-expected-word', 'request.sequence = some expected)', 'request.sequence = some (expected + 1))', 1),
            ('missing-evaluated-operands', 'before.graph.read request.arguments request.sequence', 'before.graph.read [] request.sequence', 1),
            ('missing-initial-parent', '(initial : parent before)', '(initial : True)', 1),
            ('unrelated-source-values', '(represented : Represents before.memory.memory source request.arguments)',
             '(represented : Represents before.memory.memory source [])', 1),
            ('missing-source-privacy', '(privateSource : Caller.SourcePrivate source before.memory.effects.keys)',
             '(privateSource : Caller.SourcePrivate source [])', 1),
            ('missing-item-domain', '(domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)', '(domain : True)', 1),
            ('wrong-request-sequence', 'before.graph.read request.arguments request.sequence',
             'before.graph.read request.arguments 0', 1),
        )),
    )
    records = []
    for group, module, mutations in groups:
        code = source('Compiler.Extraction.' + module)
        prefix = 'recursive-invocation-' + group + '-'
        records += checked_controls(output, [mutation_check(output, prefix + 'unchanged', code, True, env, lean)])
        for name, old, new, count in mutations:
            if code.count(old) != count:
                raise ValueError('ambiguous invocation mutation: ' + name + ': ' + str(code.count(old)))
            records += checked_controls(output, [mutation_check(output, prefix + name, code.replace(old, new), False, env, lean)])
    return records
