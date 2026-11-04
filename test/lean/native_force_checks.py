"""Audit the exact native force caller and its retained equality precondition.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
from native_miss_frame_checks import named
from native_resource_admission_checks import telescope
from native_checkpoint_constructor_checks import numeral, before_id
from native_step_builder_checks import native_base
from native_algebraic_dispatch_checks import source
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check

NS, OWNED, ITEM = gate.NS, gate.OWNED, gate.ITEM
NORMALIZATION = OWNED.removesuffix('OwnedCall.')
MEMORY = 'Compiler.ZigAir.Memory.'
INTERNER = 'Compiler.Extraction.Interner.'
CALLER = OWNED + 'Caller.'
TESTS = NS + 'ForceTests.'
MODULE = 'Compiler.Extraction.InternerNativeForceProductionTests'
CLAIMS = [CALLER + 'forceBody_publish_congr', NS + 'production_force_verified']
CLAIMS += [TESTS + name for name in ('graph_valid', 'force_contract', 'matches_terminal', 'success', 'publication_failure')]
INTERFACES = ()


def audit(claims):
    required = {
        CALLER + 'forceBody_publish_congr': {CALLER + 'forceBody'},
        NS + 'production_force_verified': {CALLER + 'forceBody_publish_congr', NS + 'context_publishes',
            OWNED + 'Insertion.graph_contracts', OWNED + 'Terminal.contracts', OWNED + 'Semantic.force_verified',
            NORMALIZATION + 'caller_buffer', OWNED + 'Publication.external_admitted'},
        TESTS + 'force_contract': {NS + 'production_force_verified'},
        TESTS + 'matches_terminal': {CALLER + 'forceBody_publish_congr', OWNED + 'Query.forceBody'},
        TESTS + 'success': {TESTS + 'matches_terminal', OWNED + 'Terminal.Tests.force_publishes_without_recursion'},
        TESTS + 'publication_failure': {TESTS + 'matches_terminal', OWNED + 'Terminal.Tests.force_failure_cleanup'},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('native force lost shared composition: ' + name + ': ' + ', '.join(sorted(missing)))
    for name in CLAIMS[:2]:
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('native force depends on a fixture: ' + name)
    return {'checkedDependencies': sorted(required), 'exactNativeForceBodyVerified': True,
            'recursiveAndInsertionContractsNotRequiredForForce': True,
            'originalEqualityAndNativeAdmissionRetained': True,
            'nativeFindBodyVerified': False, 'composedProductionTheoremVerified': False}


def audit_statements(rows, interfaces=()):
    statements = {row['theorem']: row['statement'] for row in rows}
    value = statements[NS + 'production_force_verified']
    fields, lets, root, context = telescope(value)
    expected = {'σ', 'ops', 'allocate', 'safety', 'owner', 'usizeBits', 'env', 'other', 'base', 'growth',
                'debug', 'depth', 'source', 'address', 'native', 'item', 'values', 'id', 'before', 'memory',
                'pointer', 'expected', 'good', 'allocated', 'admitted', 'valid', 'evaluated', 'equal'}
    if set(fields) != expected or set(lets) != {'nativeBase', 'nativeChildren', 'actual', 'buffer', 'input'}:
        raise ValueError('native force changed its exact premise boundary')
    forbidden = {OWNED + 'Semantic.Verified', OWNED + 'Semantic.Ensures', OWNED + 'Contracts',
                 OWNED + 'GraphContracts', OWNED + 'Semantic.GraphContracts', NS + 'InvocationPost',
                 NS + 'AllocationTrace.RecursiveSources', 'Compiler.Extraction.Associative.ConstructorSound'}
    for name, (domain, _) in fields.items():
        if forbidden & gate.step.constants_below(value, domain):
            raise ValueError('native force assumes its preservation: ' + name)
    native_base(value, *lets['nativeBase'])
    term, scope = lets['nativeChildren']
    named(value, joint.app(value, term, NS + 'unfold')[-4:], scope, ('nativeBase', 'owner', 'usizeBits', 'depth'))
    term, scope = lets['actual']
    ports = joint.app(value, term, ITEM + 'ShiftInput.Context.primitives')
    named(value, ports[-3:], scope, ('source', 'address', 'native'))
    native_context = joint.app(value, ports[-4], NS + 'context')
    named(value, native_context[-5:], scope, ('nativeBase', 'owner', 'usizeBits', 'nativeChildren', 'debug'))
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
        raise ValueError('native force changed its source memory update')
    joint.path(value, previous[3], scope, (OWNED + 'World.memory',), 'before')
    scope = scope + ['previousMemory']
    session = joint.app(value, previous[4], NORMALIZATION + 'Session.mk')
    for index, field in ((-3, 'heap'), (-1, 'effects')):
        joint.path(value, session[index], scope, (NORMALIZATION + 'Session.' + field,), 'previousMemory')
    named(value, session[-2:-1], scope, ('memory',))
    external, allocator, source_term, values, meaning, action, initial, post = joint.app(value, root, OWNED + 'Semantic.Verified')[-8:]
    joint.path(value, external, context, (ITEM + 'ShiftInput.Context.external',), 'nativeBase')
    joint.path(value, allocator, context, (ITEM + 'ShiftInput.Context.allocator',), 'base')
    named(value, [source_term, values, initial], context, ('source', 'values', 'input'))
    named(value, joint.app(value, meaning, 'Compiler.Extraction.Dispatch.wordDispatchMeaning'), context, ('env', 'other'))
    post_node = value['nodes'][post]
    for _ in range(2):
        if post_node[0] != 'lambda':
            raise ValueError('native force changed its unit postcondition')
        post_node = value['nodes'][post_node[-1]]
    if post_node != ['const', 'True', []]:
        raise ValueError('native force changed its unit postcondition')
    actual = joint.app(value, action, CALLER + 'forceBody')[-10:]
    joint.path(value, actual[0], context, (ITEM + 'ShiftInput.Context.external',), 'nativeBase')
    for index, field in ((1, 'budget'), (2, 'allocator'), (4, 'queries')):
        joint.path(value, actual[index], context, (ITEM + 'ShiftInput.Context.' + field,), 'base')
    named(value, [actual[3], *actual[5:]], context, ('actual', 'source', 'buffer', 'id', 'item', 'values'))
    for name in ('equal', 'evaluated'):
        term, scope = fields[name]
        equality = joint.app(value, term, 'Eq')
        joint.path(value, equality[-1], scope, ('Option.some',), 'expected')
        if name == 'equal':
            read = joint.app(value, equality[-2], INTERNER + 'Heap.read')
            joint.path(value, read[-2], scope, (OWNED + 'World.graph',), 'before')
            named(value, read[-1:], scope, ('id',))
        else:
            evaluated = joint.app(value, equality[-2], 'Compiler.Extraction.Cache.Item.eval')
            named(value, joint.app(value, evaluated[0], 'Compiler.Extraction.Dispatch.wordDispatchMeaning'), scope, ('env', 'other'))
            joint.path(value, evaluated[1], scope, (INTERNER + 'Heap.read', OWNED + 'World.graph'), 'before')
            named(value, evaluated[2:4], scope, ('item', 'values'))
            numeral(value, evaluated[-1], 0)
    term, scope = fields['good']
    named(value, joint.app(value, term, OWNED + 'Good')[-3:], scope, ('source', 'values', 'before'))
    term, scope = fields['valid']
    invariant = joint.app(value, term, INTERNER + 'Invariant')
    named(value, joint.app(value, invariant[-2], 'Compiler.Extraction.Dispatch.wordDispatchMeaning'), scope, ('env', 'other'))
    joint.path(value, invariant[-1], scope, (OWNED + 'World.graph',), 'before')
    term, scope = fields['admitted']
    host = joint.app(value, term, NORMALIZATION + 'Admitted')[-1]
    joint.path(value, host, scope, (OWNED + 'Insertion.Operations.arguments',), 'ops')
    term, scope = fields['allocated']
    equality = joint.app(value, term, 'Eq')
    allocation = joint.app(value, equality[-2], MEMORY + 'allocate')
    joint.path(value, allocation[-2], scope, (NORMALIZATION + 'Session.memory', OWNED + 'World.memory'), 'before')
    array = joint.app(value, allocation[-1], MEMORY + 'Ty.array')
    numeral(value, array[-2], 2)
    named(value, array[-1:], scope, (MEMORY + 'WordArray.word',))
    result = joint.app(value, equality[-1], 'Except.ok')[-1]
    named(value, joint.app(value, result, 'Prod.mk')[-2:], scope, ('pointer', 'memory'))
    return {'sameRawForceBodyBound': True, 'originalSourceAndAllocatedScratchBound': True,
            'existingRepresentativeEqualityRequired': True, 'cleanupAndWordPredicate': OWNED + 'Semantic.Verified',
            'noChildOrGraphCorrectnessPremise': True, 'composedProductionTheoremVerified': False}


def controls(output, env, lean):
    groups = (
        ('proof', 'InternerNativeForceProduction', (
            ('missing-publication-equality', '(publish : left.publish = right.publish)', '(publish : True)', 1),
            ('missing-representative-equality', '(equal : before.graph.read id = some expected)', '(equal : True)', 1),
            ('unequal-representative', '(equal : before.graph.read id = some expected)', '(equal : before.graph.read id = some (expected + 1))', 1),
            ('unrelated-source-values', '(good : Good source values before)', '(good : Good source [] before)', 1),
            ('missing-host-admission', '(admitted : Admitted ops.arguments)', '(admitted : True)', 1),
            ('wrong-scratch-allocation', '(.array 2 word)', '(.array 3 word)', 1),
            ('wrong-forced-id', 'actual base.queries source buffer id item values)', 'actual base.queries source buffer (id + 1) item values)', 1),
            ('wrong-request-value', 'before.graph.read values 0 = some expected)', 'before.graph.read values 0 = some (expected + 1))', 1),
        )),
        ('attachment', 'InternerNativeForceProductionTests', (
            ('wrong-published-id', '⟨1, 1, 0, [1, 3], 0⟩ = some 4', '⟨1, 1, 0, [1, 3], 0⟩ = some 3', 1),
            ('failed-cleanup-retains-allocation', '.world.memory.heap 5 = none', '.world.memory.heap 5 ≠ none', 1),
            ('omit-cleanup', 'Caller.invoke (Publication.external (ops failure).arguments) 7 (body failure depth) world',
             '(body failure depth) ⟨world, { lookup := none }⟩', 1),
        )),
    )
    records = []
    for group, module, mutations in groups:
        code = source('Compiler.Extraction.' + module)
        prefix = 'native-force-' + group + '-'
        records += checked_controls(output, [mutation_check(output, prefix + 'unchanged', code, True, env, lean)])
        for name, old, new, count in mutations:
            if code.count(old) != count:
                raise ValueError('ambiguous native force mutation: ' + name + ': ' + str(code.count(old)))
            records += checked_controls(output, [mutation_check(output, prefix + name, code.replace(old, new), False, env, lean)])
    return records
