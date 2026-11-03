"""Audit joint constructor preservation on the actual finite recursive family.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
import constructor_joint_entry_checks as entries
from assembly_item_creation_checks import checked_controls
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NS, PNS, OWNED = gate.NS, joint.PNS, gate.OWNED
FNS = NS + 'ProtocolTrace.'
MODULE = 'Compiler.Extraction.InternerRecursiveJointEntries'
CLAIMS = [OWNED + 'NativeGraph.Facts.mapAllocator_iff', NS + 'GraphFrame.mapAllocator', PNS + 'JointPost.mapAllocator']
CLAIMS += [FNS + entry + '_joint' for entry in entries.ENTRIES]
INTERFACES = (PNS + 'JointEntry', OWNED + 'World.mapEffects', OWNED + 'Publication.Effects.mapAllocator', NS + 'ChildTrace.erase')
PARAMETERS = (entries.PARAMETERS - {'children', 'observations'}) | {
    'outerOps', 'outerAllocate', 'outerBase', 'outerGrowth', 'hosts', 'allocators', 'budgets', 'queries', 'depth'}


def applications(value, root, context, name):
    """Find complete applications while preserving the scopes of local binders."""
    node = value['nodes'][root]
    if node[0] in ('forall', 'lambda', 'let'):
        roots = (node[3],) if node[0] != 'let' else (node[2], node[3])
        for child in roots:
            yield from applications(value, child, context, name)
        yield from applications(value, node[4], context + [node[1]], name)
    elif node[0] == 'app':
        head, args = gate.applied(value, root)
        if head[:2] == ['const', name]:
            yield args, context
        for child in args:
            yield from applications(value, child, context, name)
    elif node[0] == 'projection':
        yield from applications(value, node[3], context, name)


def finite_inputs(value, root, context, successor):
    args = joint.app(value, root, FNS + 'unfold')
    names = [gate.named(value, x, context) for x in args[-9:]]
    if names[:4] != ['ops', 'allocate', 'safety', 'owner'] or names[5:8] != ['base', 'growth', 'usizeBits']:
        raise ValueError('finite joint proof replaced native recursion inputs')
    meaning = joint.app(value, args[-5], 'Compiler.Extraction.Dispatch.wordDispatchMeaning')
    if [gate.named(value, x, context) for x in meaning] != ['env', 'other']:
        raise ValueError('finite joint proof changed the word meaning')
    if successor:
        added = joint.app(value, args[-1], 'HAdd.hAdd')
        one = joint.app(value, added[-1], 'OfNat.ofNat')
        if gate.named(value, added[-2], context) != 'depth' or gate.named(value, one[-2], context) != ('natural', '1'):
            raise ValueError('finite joint conclusion lost the successor depth')
    elif names[-1] != 'depth':
        raise ValueError('finite joint observations lost the proper depth')


def audit_statements(rows, interfaces):
    statements = {row['theorem']: row['statement'] for row in rows}
    definitions = {row['name']: row for row in interfaces}
    value = definitions[OWNED + 'Publication.Effects.mapAllocator']['value']
    _, root, context = gate.domains(value)
    effects = joint.app(value, root, OWNED + 'Publication.Effects.mk')
    joint.path(value, effects[-2], context, (OWNED + 'Publication.Effects.keys',), 'before')
    head, args = gate.applied(value, effects[-1])
    if head[0] != 'bound' or context[-int(head[1]) - 1] != 'project':
        raise ValueError('effect transport no longer maps only allocator-private state')
    joint.path(value, args[-1], context, (OWNED + 'Publication.Effects.allocator',), 'before')
    value = definitions[OWNED + 'World.mapEffects']['value']
    _, root, context = gate.domains(value)
    world = joint.app(value, root, OWNED + 'World.mk')
    joint.path(value, world[-2], context, (OWNED + 'World.graph',), 'before')
    session = joint.app(value, world[-1], OWNED.removesuffix('OwnedCall.') + 'Session.mapEffects')
    if gate.named(value, session[-2], context) != 'project':
        raise ValueError('world effect transport replaced its private projection')
    joint.path(value, session[-1], context, (OWNED + 'World.memory',), 'before')
    value = definitions[NS + 'ChildTrace.erase']['value']
    _, root, context = gate.domains(value)
    erased = joint.app(value, root, OWNED + 'World.mapEffects')
    project = joint.app(value, erased[-2], OWNED + 'Publication.Effects.mapAllocator')
    if gate.applied(value, project[-1])[0][:2] != ['const', 'Prod.fst'] or gate.named(value, erased[-1], context) != 'world':
        raise ValueError('child erasure changed the native world or private-history projection')
    joint_fields = list(gate.domains(definitions[PNS + 'JointEntry']['type'])[0])
    forbidden = {PNS + 'JointPost', PNS + 'EntryProjected', NS + 'InvocationPost', NS + 'ConstructorPost', OWNED + 'Semantic.Ensures'}
    for entry in entries.ENTRIES:
        value = statements[FNS + entry + '_joint']
        fields, conclusion, context = gate.domains(value)
        if set(fields) != PARAMETERS | entries.ENTRY_EXTRAS[entry]:
            raise ValueError('finite joint entry changed its local premises: ' + entry)
        for name, (root, _) in fields.items():
            if forbidden & gate.step.constants_below(value, root):
                raise ValueError('finite joint entry assumes its result: ' + entry + '.' + name)
        root, local = fields['joint']
        calls = list(applications(value, root, local, PNS + 'JointEntry'))
        if len(calls) != 1 or len(calls[0][0]) != len(joint_fields):
            raise ValueError('finite joint entry lost its single shared witness: ' + entry)
        args, local = calls[0]
        bound = dict(zip(joint_fields, args))
        for field in ('ops', 'allocate', 'base', 'growth'):
            expected = {'ops': 'outerOps', 'allocate': 'outerAllocate', 'base': 'outerBase', 'growth': 'outerGrowth'}[field]
            if gate.named(value, bound[field], local) != expected:
                raise ValueError('finite joint entry replaced a recorded host input: ' + field)
        children = joint.app(value, bound['children'], NS + 'unfold')
        if [gate.named(value, x, local) for x in children[-3:]] != ['owner', 'usizeBits', 'depth']:
            raise ValueError('finite joint child is not the actual proper-depth native execution')
        caller = joint.app(value, children[-4], NS + 'callerContext')
        if [gate.named(value, x, local) for x in caller[-7:-3]] != ['ops', 'allocate', 'safety', 'owner']:
            raise ValueError('finite joint child replaced its native host calls')
        if [gate.named(value, x, local) for x in caller[-2:]] != ['base', 'growth']:
            raise ValueError('finite joint child replaced its native settings')
        observed = joint.app(value, bound['observations'], FNS + 'observe')
        finite_inputs(value, observed[-1], local, False)
        if gate.named(value, bound['model'], local) != 'model':
            raise ValueError('finite joint entry changed the bound replay model')
        parent = value['nodes'][bound['parent']]
        if parent[0] != 'lambda':
            raise ValueError('finite joint frame lost concrete parent transport')
        local_parent = local + [parent[1]]
        head, argument = gate.applied(value, parent[4])
        if head[0] != 'bound' or local_parent[-int(head[1]) - 1] != 'parent':
            raise ValueError('finite joint entry replaced its native parent')
        joint.path(value, argument[-1], local_parent, (NS + 'ChildTrace.erase',), parent[1])
        post = joint.app(value, conclusion, PNS + 'JointPost')
        joint.path(value, post[-7], context, (OWNED + 'World.graph',), 'before')
        if [gate.named(value, x, context) for x in (post[-9], post[-6], post[-5])] != ['model', 'leading', 'trailing']:
            raise ValueError('finite joint result changed model or stream boundaries')
        calls = list(applications(value, post[-2], context, FNS + 'unfold'))
        if len(calls) != 1:
            raise ValueError('finite joint result lost its actual execution')
        # Recover the unfold node from the complete constructor application.
        head, actual = gate.applied(value, post[-2])
        field = {'borrowed': 'borrowedOperation', 'local': 'localOperation'}.get(entry, entry)
        if head[:2] != ['const', 'Compiler.Extraction.Associative.Constructors.' + field]:
            raise ValueError('finite joint result changed constructor field: ' + entry)
        family = next(x for x in actual if gate.applied(value, x)[0][:2] == ['const', FNS + 'unfold'])
        finite_inputs(value, family, context, True)
        if [gate.named(value, x, context) for x in (actual[-3], actual[-1])] != ['debug', 'leading']:
            raise ValueError('finite joint result changed invocation inputs')
        joint.path(value, actual[-2], context, (NS + 'ChildTrace.erase',), 'before')
    value = statements[OWNED + 'NativeGraph.Facts.mapAllocator_iff']
    fields, root, context = gate.domains(value)
    if set(fields) != {'σ', 'τ', 'project', 'safety', 'allocator', 'owner', 'capacity', 'data', 'world', 'rows'}:
        raise ValueError('native graph erasure added a preservation premise')
    mapped, original = joint.app(value, root, 'Iff')
    left = joint.app(value, mapped, OWNED + 'NativeGraph.Facts')
    right = joint.app(value, original, OWNED + 'NativeGraph.Facts')
    if [gate.named(value, x, context) for x in left[-7:-2] + left[-1:]] != ['safety', 'allocator', 'owner', 'data', 'capacity', 'rows']:
        raise ValueError('native graph erasure changed graph identity or rows')
    joint.path(value, left[-2], context, (OWNED + 'World.mapEffects',), 'world')
    if gate.named(value, right[-2], context) != 'world':
        raise ValueError('native graph erasure changed its original world')
    return {'checkedEntries': list(entries.ENTRIES), 'properDepthChildrenAndComputedEvents': True,
            'sameNativeGraphAndParentFrame': True, 'actualFiniteExecution': True,
            'localModelBindingStillRequired': True, 'completeStreamCorrespondenceVerified': False,
            'recursiveInductionVerified': False, 'composedProductionTheoremVerified': False}


def audit(claims):
    required = {
        NS + 'GraphFrame.mapAllocator': {OWNED + 'NativeGraph.Facts.mapAllocator_iff'},
        PNS + 'JointPost.mapAllocator': {NS + 'GraphFrame.mapAllocator', PNS + 'mapReturn_outcome', PNS + 'EntryProjected.of_outcome'},
    }
    for entry in entries.ENTRIES:
        required[FNS + entry + '_joint'] = {PNS + 'step_' + entry + '_joint', PNS + 'JointPost.mapAllocator', FNS + 'unfold_step_traced'}
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('finite joint proof lost shared reasoning: ' + name + ': ' + ', '.join(sorted(missing)))
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('finite joint proof depends on a fixture: ' + name)
    return {'checkedDependencies': sorted(required), 'sharedNativeFrameTransport': True,
            'recursiveInductionVerified': False, 'composedProductionTheoremVerified': False}


def mutation_cases():
    directory = gate.harness.ROOT / 'lean/Compiler/Extraction'
    source = 'import Compiler.Extraction.InternerConstructorJointEntries\nimport Compiler.Extraction.InternerRecursiveProtocolEffects\n'
    source += 'set_option pp.maxSteps 8\nset_option pp.deepTerms false\n'
    source += '\n'.join(without_imports((directory / (name + '.lean')).read_text()) for name in (
        'InternerNativeFrameEffects', 'InternerConstructorJointEffects', 'InternerRecursiveJointEntries'))
    changes = (
        ('wrong-child-depth', 'base growth) owner usizeBits depth\n', 'base growth) owner usizeBits (depth + 1)\n', 1),
        ('wrong-observed-depth', 'base growth usizeBits depth)\n', 'base growth usizeBits (depth + 1))\n', 1),
        ('wrong-parent-depth', 'base growth usizeBits (depth + 1)', 'base growth usizeBits depth', 10),
        ('wrong-allocator-binding', '(allocators : outerBase.allocator = base.allocator)', '(allocators : outerBase.allocator = base.allocator + 1)', 1),
        ('wrong-budget-binding', '(budgets : outerBase.budget = base.budget)', '(budgets : outerBase.budget = base.budget + 1)', 1),
        ('missing-query-binding', '(queries : outerBase.queries = base.queries)', '(queries : outerBase.queries = outerBase.queries)', 1),
        ('wrong-leading-events', 'debug (ChildTrace.erase before) leading', 'debug (ChildTrace.erase before) trailing', 10),
        ('wrong-parent-cleanup', 'cleanup before.memory.memory.nextId world.memory.memory', 'cleanup (before.memory.memory.nextId + 1) world.memory.memory', 2),
        ('wrong-native-allocator', 'NativeGraph.Facts safety allocator owner data capacity (world.mapEffects',
         'NativeGraph.Facts safety (allocator + 1) owner data capacity (world.mapEffects', 1),
        ('wrong-returned-rows', 'GraphFrame safety allocator owner rows parent (world.mapEffects',
         'GraphFrame safety allocator owner (rows ++ rows) parent (world.mapEffects', 1),
        ('wrong-returned-word', '(mapReturn (Publication.Effects.mapAllocator project) actual) expected := by',
         '(mapReturn (Publication.Effects.mapAllocator project) actual) (expected + 1) := by', 1),
    )
    return source, changes


def controls(output, env, lean):
    source, changes = mutation_cases()
    records = checked_controls(output, [mutation_check(output, 'finite-joint-unchanged', source, True, env, lean)])
    for name, before, after, count in changes:
        if source.count(before) != count:
            raise ValueError('ambiguous finite joint mutation: ' + name)
        records += checked_controls(output, [mutation_check(output, 'finite-joint-' + name,
            source.replace(before, after), False, env, lean)])
    return records
