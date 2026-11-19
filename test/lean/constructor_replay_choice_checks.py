"""Audit pointwise replay construction from an actual constructor prefix.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
from recursive_joint_entry_checks import applications
from assembly_item_creation_checks import checked_controls
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NS, PNS, OWNED, TRACE = gate.NS, joint.PNS, gate.OWNED, joint.TRACE
MODULE = 'Compiler.Extraction.InternerConstructorReplayChoice'
CLAIMS = [PNS + name for name in ('TakenSite.Reached.unique', 'siteReplay_queries', 'siteReplay_taken',
                                 'JointEntry.exists_model', 'item_replay_joint')]
INTERFACES = tuple(PNS + name for name in ('TakenSite.Reached.mk', 'SiteChildren', 'sitePrefix', 'siteReplay'))
PARAMETERS = joint.PARAMETERS | {'leading', 'trailing', 'before', 'seed', 'mismatch', 'retained', 'localParent', 'laws'}


def one_call(value, root, context, name):
    calls = list(applications(value, root, context, name))
    if len(calls) != 1:
        raise ValueError('replay choice lost its single actual input: ' + name)
    return calls[0]


def existential(value, root, context):
    args = joint.app(value, root, 'Exists')
    node = value['nodes'][args[-1]]
    if node[:2] != ['lambda', 'model']:
        raise ValueError('entry model is no longer a derived witness')
    root, context = node[4], context + ['model']
    for field in ('atCapacity', 'deterministic'):
        equality, root = joint.app(value, root, 'And')
        args = joint.app(value, equality, 'Eq')
        for term, name in zip(args[-2:], ('model', 'seed')):
            joint.path(value, term, context, ('Compiler.Extraction.Interner.Primitives.' + field,), name)
    return root, context


def audit_statements(rows, interfaces):
    statements = {row['theorem']: row['statement'] for row in rows}
    definitions = {row['name']: row for row in interfaces}
    value = definitions[PNS + 'TakenSite.Reached.mk']['type']
    fields, _, _ = gate.domains(value)
    observations = {'made', 'room', 'allocated', 'initialized', 'classified', 'keyed', 'missed', 'transferred', 'input'}
    if set(fields) != {'σ', 'base', 'source', 'request', 'debug', 'before', 'site'} | observations:
        raise ValueError('reached prefix added an assumption or lost an observation')
    for name, operation in (('made', gate.ITEM + 'prepare'), ('allocated', 'Compiler.ZigAir.Memory.allocate'),
        ('initialized', OWNED + 'Caller.initLookup'), ('keyed', 'Compiler.Extraction.Interner.makeKey'),
        ('transferred', OWNED + 'take'), ('input', OWNED + 'Insertion.Native.CallerInput')):
        root, local = fields[name]
        one_call(value, root, local, operation)
    for name, field in (('room', 'atCapacity'), ('classified', 'deterministic')):
        root, local = fields[name]
        args, local = one_call(value, root, local, OWNED + 'Caller.Queries.' + field)
        joint.path(value, args[-2], local, (gate.ITEM + 'ShiftInput.Context.queries',), 'base')
    value = statements[PNS + 'TakenSite.Reached.unique']
    fields, root, context = gate.domains(value)
    if set(fields) != {'σ', 'base', 'source', 'request', 'debug', 'before', 'left', 'right', 'one', 'two'}:
        raise ValueError('prefix uniqueness added a determinacy premise')
    args = joint.app(value, root, 'Eq')
    if [gate.named(value, x, context) for x in args[-2:]] != ['left', 'right']:
        raise ValueError('prefix uniqueness no longer identifies complete sites')
    value = definitions[PNS + 'sitePrefix']['value']
    fields, root, context = gate.domains(value)
    if set(fields) != {'σ', 'ops', 'base', 'source', 'request', 'leading', 'site'}:
        raise ValueError('site recorder changed its actual inputs')
    args = joint.app(value, root, PNS + 'takenPrefix')
    for term, field in zip(args[-3:-1], ('constructed', 'memory')):
        joint.path(value, term, context, (PNS + 'TakenSite.' + field,), 'site')
    if gate.named(value, args[-1], context) != 'leading':
        raise ValueError('site recorder rewound history')
    forbidden = {PNS + 'JointPost', PNS + 'EntryProjected', NS + 'InvocationPost', NS + 'ConstructorPost',
                 OWNED + 'Semantic.Ensures', PNS + 'TakenModel', PNS + 'JointEntry', PNS + 'replayModel'}
    value = definitions[PNS + 'SiteChildren']['value']
    fields, root, context = gate.domains(value)
    if set(fields) != joint.PARAMETERS | {'leading', 'site'}:
        raise ValueError('local child laws added a premise or lost actual inputs')
    if forbidden & gate.step.constants_below(value, root):
        raise ValueError('local child laws assume a final result or fixed replay binding')
    for name in ('Compiler.Extraction.Dispatch.Effects.SourceConstructorsAt', NS + 'TakenFramesAt'):
        args, local = one_call(value, root, context, name)
        if 'childModel' not in [gate.named(value, x, local) for x in args]:
            raise ValueError('local child laws lost their shared model')
    value = definitions[PNS + 'siteReplay']['value']
    fields, root, context = gate.domains(value)
    if set(fields) != (joint.PARAMETERS - {'rows', 'parent'}) | {'leading', 'trailing', 'site', 'seed', 'childModel', 'mismatch'}:
        raise ValueError('replay selection changed its inputs')
    head, branches = gate.applied(value, root)
    if head[:2] != ['const', PNS + 'siteReplay.match_1'] or len(branches) != 4:
        raise ValueError('replay selection lost its actual token case split')
    joint.path(value, branches[1], context, ('Compiler.Extraction.Interner.Scoped.Scope.lookup',
        TRACE + 'Tokens.toScope', TRACE + 'Recorded.tokens'), 'recorded')
    absent = value['nodes'][branches[2]]
    if absent[0] != 'lambda' or gate.named(value, absent[4], context + [absent[1]]) != 'seed':
        raise ValueError('absent replay token no longer preserves the seed')
    args, local = one_call(value, root, context, PNS + 'replayModel')
    for term, field in zip(args[-11:-6], ('address', 'key', 'normalized', 'lookup', 'deterministic')):
        joint.path(value, term, local, (PNS + 'TakenSite.' + field,), 'site')
    if [gate.named(value, x, local) for x in args[-6:]] != ['recorded', 'token', 'trailing', 'seed', 'childModel', 'mismatch']:
        raise ValueError('replay selection replaced token, history or child model')
    for theorem in ('JointEntry.exists_model', 'item_replay_joint'):
        value = statements[PNS + theorem]
        fields, root, context = gate.domains(value)
        expected = PARAMETERS.copy()
        if theorem == 'item_replay_joint':
            expected |= {'capacity', 'data', 'facts', 'represented', 'privateSource', 'array', 'admitted', 'domain', 'typed',
                         'capacityQuery', 'classificationQuery', 'expected', 'valid', 'evaluated', 'pushes'}
        if set(fields) != expected:
            raise ValueError('replay construction added a premise or lost an input: ' + theorem)
        for name, (index, _) in fields.items():
            if forbidden & gate.step.constants_below(value, index):
                raise ValueError('replay construction assumes its result: ' + theorem + '.' + name)
        index, local = fields['laws']
        reached, reached_context = one_call(value, index, local, PNS + 'TakenSite.Reached')
        caller = joint.app(value, reached[-6], NS + 'callerContext')
        if [gate.named(value, x, reached_context) for x in caller[-7:-3] + caller[-2:]] != ['ops', 'allocate', 'safety', 'owner', 'base', 'growth']:
            raise ValueError('child laws no longer concern the actual native prefix')
        args, local = one_call(value, index, local, PNS + 'SiteChildren')
        if [gate.named(value, x, local) for x in args[-2:]] != ['leading', 'site']:
            raise ValueError('child laws changed the reached history or site')
        root, context = existential(value, root, context)
        if theorem == 'JointEntry.exists_model':
            args = joint.app(value, root, PNS + 'JointEntry')
            if [gate.named(value, x, context) for x in args[-4:]] != ['model', 'before', 'leading', 'trailing']:
                raise ValueError('constructed model does not serve the original entry')
        else:
            args = joint.app(value, root, PNS + 'JointPost')
            if [gate.named(value, x, context) for x in (args[-9], args[-8], args[-6], args[-5], args[-1])] != ['model', 'request', 'leading', 'trailing', 'expected']:
                raise ValueError('constructed model changed the promised result')
            joint.path(value, args[-7], context, (OWNED + 'World.graph',), 'before')
            capture = joint.app(value, args[-2], PNS + 'item')
            if [gate.named(value, x, context) for x in capture[-5:]] != ['source', 'request', 'debug', 'before', 'leading']:
                raise ValueError('constructed model describes a different item invocation')
    return {'actualPrefixDeterminesSite': True, 'entryModelConstructed': True, 'seedQueriesUnchanged': True,
            'jointItemConsumesDerivedModel': True, 'properChildAndNativeFrameLawsRequired': True,
            'uniformRecursiveModelVerified': False, 'recursiveInductionVerified': False,
            'composedProductionTheoremVerified': False}


def audit(claims):
    required = {
        PNS + 'TakenSite.Reached.unique': {OWNED + 'Caller.Origin.scope'},
        PNS + 'siteReplay_taken': {PNS + 'siteReplay', PNS + 'replayModel'},
        PNS + 'JointEntry.exists_model': {PNS + 'TakenSite.Reached.unique', PNS + 'siteReplay_taken', PNS + 'siteReplay_queries'},
        PNS + 'item_replay_joint': {PNS + 'JointEntry.exists_model', PNS + 'item_joint_verified'},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('replay choice lost shared reasoning: ' + name + ': ' + ', '.join(sorted(missing)))
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('replay choice depends on a fixture: ' + name)
    return {'checkedDependencies': sorted(required), 'pointwiseModelOnly': True,
            'recursiveInductionVerified': False, 'composedProductionTheoremVerified': False}


def mutation_cases():
    directory = gate.harness.ROOT / 'lean/Compiler/Extraction'
    source = 'import Compiler.Extraction.InternerRecursiveJointEntries\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n'
    source += '\n'.join(without_imports((directory / (name + '.lean')).read_text()) for name in (
        'InternerTakenSite', 'InternerConstructorReplayChoice'))
    # The reached-site record is now imported by the shared native step.
    # Keep the complete mutated record and its clients in one distinct namespace.
    source = source.replace('TakenSite', 'TakenSiteMutation')
    changes = (
        ('wrong-initialized-values', '(.ok site.values, site.prepared)', '(.ok [], site.prepared)', 1),
        ('wrong-take-state', 'site.prepared = (.ok (), site.taken)', 'site.taken = (.ok (), site.taken)', 1),
        ('missing-classifier', 'base.queries.deterministic request.item = .ok site.deterministic', 'base.queries.deterministic request.item = base.queries.deterministic request.item', 1),
        ('missing-key', 'Interner.makeKey request site.values = .ok site.key', 'Interner.makeKey request site.values = Interner.makeKey request site.values', 1),
        ('wrong-owner-slice', 'site.constructed site.taken site.normalized site.lookup', 'site.constructed site.taken ⟨0, []⟩ site.lookup', 1),
        ('wrong-prefix-history', 'site.constructed site.memory leading', 'site.constructed site.memory (leading ++ leading)', 1),
        ('wrong-child-cursor', 'MissStream.childCursor recorded.events.length recorded.native.world', 'MissStream.childCursor (recorded.events.length + 1) recorded.native.world', 1),
        ('wrong-replay-token', 'recorded token trailing seed childModel mismatch', 'recorded { token with invalid := true } trailing seed childModel mismatch', 1),
        ('wrong-replay-owner', 'site.address site.key site.normalized site.lookup site.deterministic recorded', 'site.address site.key site.normalized { site.lookup with values := [] } site.deterministic recorded', 1),
        ('wrong-trailing-history', 'recorded token trailing seed childModel mismatch', 'recorded token (trailing ++ trailing) seed childModel mismatch', 1),
        ('wrong-seed-queries', 'none => seed', 'none => { seed with atCapacity := fun _ => true }', 1),
        ('unbound-model', 'model before leading trailing := by', 'seed before leading trailing := by', 1),
        ('wrong-return-word', 'source request debug before leading) expected := by', 'source request debug before leading) (expected + 1) := by', 1),
    )
    return source, changes


def controls(output, env, lean):
    source, changes = mutation_cases()
    records = checked_controls(output, [mutation_check(output, 'replay-choice-unchanged', source, True, env, lean)])
    for name, before, after, count in changes:
        if source.count(before) != count:
            raise ValueError('ambiguous replay choice mutation: ' + name)
        records += checked_controls(output, [mutation_check(output, 'replay-choice-' + name,
            source.replace(before, after), False, env, lean)])
    return records
