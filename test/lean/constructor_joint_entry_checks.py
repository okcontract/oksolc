"""Audit joint recorded/native preservation through actual constructor wrappers.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
from assembly_item_creation_checks import checked_controls
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NS, PNS, OWNED = gate.NS, joint.PNS, gate.OWNED
MODULE = 'Compiler.Extraction.InternerConstructorJointEntries'
ENTRIES = ('borrowed', 'constant', 'materialize', 'operation', 'local')
CLAIMS = [NS + 'prepared_input_frame'] + [PNS + name for name in (
    'JointPost.rejected', 'JointPost.retire', 'prepared_item_joint', 'prepared_constructor_joint')]
CLAIMS += [PNS + 'step_' + entry + '_joint' for entry in ENTRIES]
INTERFACES = (PNS + 'JointPost', PNS + 'jointStep')
PARAMETERS = (joint.PARAMETERS - {'source', 'request'}) | {
    'model', 'before', 'leading', 'trailing', 'capacity', 'data', 'facts',
    'admitted', 'typed', 'valid', 'capacityQuery', 'classificationQuery', 'joint'}
ENTRY_EXTRAS = {
    'borrowed': {'slice', 'opcode', 'expected', 'represented', 'privateSource', 'array', 'evaluated'},
    'constant': {'value', 'pushes', 'literals'},
    'materialize': {'id', 'value', 'pushes', 'literals'},
    'operation': {'opcode', 'values', 'expected', 'evaluated', 'localParent'},
    'local': {'opcode', 'slice', 'selected', 'repeated', 'first', 'expected', 'represented', 'inside', 'evaluated', 'localParent'},
}


def audit_statements(rows, interfaces):
    statements = {row['theorem']: row['statement'] for row in rows}
    definitions = {row['name']: row for row in interfaces}
    value = definitions[PNS + 'JointPost']['value']
    _, root, context = gate.domains(value)
    recorded, native = joint.app(value, root, 'And')
    projected = joint.app(value, recorded, PNS + 'EntryProjected')
    if [gate.named(value, x, context) for x in projected[-6:]] != [
            'model', 'request', 'before', 'leading', 'trailing', 'actual']:
        raise ValueError('joint return lost its fixed model, entry graph or complete capture')
    post = joint.app(value, native, NS + 'InvocationPost')
    if [gate.named(value, x, context) for x in post[-5:-2]] != ['meaning', 'frame', 'before']:
        raise ValueError('joint return changed its native specification')
    if gate.named(value, post[-1], context) != 'expected':
        raise ValueError('joint return changed its expected word')
    pair = joint.app(value, post[-2], 'Prod.mk')
    joint.path(value, pair[-2], context, ('Prod.fst',), 'actual')
    joint.path(value, pair[-1], context, (joint.TRACE + 'Recorded.native', 'Prod.snd'), 'actual')

    value = definitions[PNS + 'jointStep']['value']
    _, root, context = gate.domains(value)
    args = joint.app(value, root, NS + 'ProtocolTrace.step')
    for argument, function in ((args[-2], 'constructors'), (args[-1], 'liftObservations')):
        bound = joint.app(value, argument, NS + 'ChildTrace.' + function)
        if gate.named(value, bound[-1], context) != 'observations':
            raise ValueError('joint constructor replaced its actual child observations')
        if function == 'constructors' and gate.named(value, bound[-2], context) != 'children':
            raise ValueError('joint constructor replaced its actual children')

    forbidden = {PNS + 'JointPost', PNS + 'EntryProjected', NS + 'InvocationPost', NS + 'ConstructorPost',
                 OWNED + 'Semantic.Ensures', NS + 'MissWords', OWNED + 'Insertion.Native.CandidateWords'}
    common = PARAMETERS | {'request', 'domain', 'expected', 'evaluated', 'pushes', 'ready'}
    for name, expected in (
            ('prepared_item_joint', common | {'source', 'prepared'}),
            ('prepared_constructor_joint', common | {'producer', 'action', 'retiring', 'forwarded', 'rejected', 'localParent'})):
        value = statements[PNS + name]
        fields, _, _ = gate.domains(value)
        if set(fields) != expected:
            raise ValueError('joint preparation changed its general premises: ' + name)
        for field, (root, _) in fields.items():
            if forbidden & gate.step.constants_below(value, root):
                raise ValueError('joint preparation assumes its result: ' + name + '.' + field)
    for entry in ENTRIES:
        value = statements[PNS + 'step_' + entry + '_joint']
        fields, root, context = gate.domains(value)
        if set(fields) != PARAMETERS | ENTRY_EXTRAS[entry]:
            raise ValueError('joint constructor changed entry premises: ' + entry)
        for name, (field, _) in fields.items():
            if forbidden & gate.step.constants_below(value, field):
                raise ValueError('joint constructor assumes its result: ' + entry + '.' + name)
        obligations = gate.step.constants_below(value, fields['joint'][0])
        needed = {PNS + 'JointEntry'}
        if entry in ('operation', 'local'):
            needed |= {gate.ITEM + 'Arguments.Prepared', gate.ITEM + 'Arguments.prepare'
                       if entry == 'operation' else OWNED + 'LocalArguments.zigLocal'}
        if not needed <= obligations:
            raise ValueError('joint constructor lost actual preparation or its shared entry witness: ' + entry)
        post = joint.app(value, root, PNS + 'JointPost')
        if gate.named(value, post[-9], context) != 'model':
            raise ValueError('joint constructor changed its entry model: ' + entry)
        joint.path(value, post[-7], context, (OWNED + 'World.graph',), 'before')
        if [gate.named(value, x, context) for x in post[-6:-4]] != ['leading', 'trailing']:
            raise ValueError('joint constructor changed its stream boundaries: ' + entry)
        execution, arguments = gate.applied(value, post[-2])
        field = {'borrowed': 'borrowedOperation', 'local': 'localOperation'}.get(entry, entry)
        if execution[:2] != ['const', 'Compiler.Extraction.Associative.Constructors.' + field]:
            raise ValueError('joint constructor proves a different entry: ' + entry)
        if [gate.named(value, x, context) for x in arguments[-3:]] != ['debug', 'before', 'leading']:
            raise ValueError('joint constructor changed the actual invocation inputs: ' + entry)
        if PNS + 'jointStep' not in gate.step.constants_below(value, post[-2]):
            raise ValueError('joint constructor lost the actual recorded step: ' + entry)
    value = statements[PNS + 'step_local_joint']
    fields, _, _ = gate.domains(value)
    root, context = fields['inside']
    args = joint.app(value, value['nodes'][root][3], 'Eq')
    if [gate.named(value, x, context) for x in args[-2:]] != ['first', 'Bool.true']:
        raise ValueError('joint local bound lost its actual overwrite guard')
    return {'checkedEntries': list(ENTRIES), 'sameCompleteCapture': True, 'actualPreparationSelected': True,
            'localModelBindingStillRequired': True, 'completeStreamCorrespondenceVerified': False,
            'recursiveInductionVerified': False, 'composedProductionTheoremVerified': False}


def audit(claims):
    required = {
        NS + 'prepared_input_frame': {OWNED + 'NativeGraph.Facts.frame', gate.ITEM + 'Arguments.Prepared.key_apart'},
        PNS + 'JointPost.retire': {PNS + 'retire_outcome', NS + 'InvocationPost.unwind', PNS + 'retire_native'},
        PNS + 'prepared_item_joint': {NS + 'prepared_input_frame', PNS + 'item_joint_verified'},
        PNS + 'prepared_constructor_joint': {PNS + 'prepared_item_joint', PNS + 'JointPost.retire', PNS + 'JointPost.rejected'},
        PNS + 'step_borrowed_joint': {PNS + 'item_joint_verified'},
        PNS + 'step_constant_joint': {PNS + 'item_joint_verified'},
        PNS + 'step_materialize_joint': {PNS + 'step_constant_joint'},
        PNS + 'step_operation_joint': {PNS + 'prepared_constructor_joint', gate.ITEM + 'Arguments.prepare_success', gate.ITEM + 'Arguments.error_nonordinary'},
        PNS + 'step_local_joint': {PNS + 'prepared_constructor_joint', gate.ITEM + 'ViewInput.local_input_optional', OWNED + 'LocalArguments.error_nonordinary'},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('joint constructor lost shared reasoning: ' + name + ': ' + ', '.join(sorted(missing)))
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('joint constructor depends on fixtures: ' + name)
    if NS + 'prepared_input_frame' not in claims[NS + 'prepared_invocation_verified_observed']:
        raise ValueError('old native preparation no longer shares the joint input proof')
    return {'checkedDependencies': sorted(required), 'sharedPreparationAndReturn': True,
            'recursiveInductionVerified': False, 'composedProductionTheoremVerified': False}


def mutation_cases():
    directory = gate.harness.ROOT / 'lean/Compiler/Extraction'
    raw = [(directory / ('InternerConstructorJoint' + name + '.lean')).read_text() for name in ('Return', 'Entries')]
    source = 'import Compiler.Extraction.InternerConstructorJointInduction\nimport Compiler.Extraction.InternerRecursiveProtocolTrace\n'
    source += 'set_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + '\n'.join(map(without_imports, raw))
    changes = (
        ('wrong-entry-table', 'EntryProjected model request before leading trailing actual ∧',
         'EntryProjected model request { before with table := fun _ => none } leading trailing actual ∧', 1),
        ('wrong-native-word', 'InvocationPost meaning frame before (actual.1, actual.2.native) expected',
         'InvocationPost meaning frame before (actual.1, actual.2.native) (expected + 1)', 1),
        ('wrong-return-mark', '(ProtocolTrace.retire mark actual) expected', '(ProtocolTrace.retire (mark + 1) actual) expected', 1),
        ('cleanup-live-owner', '(mark : Nat) (older : owner < mark)', '(mark : Nat) (older : owner ≤ mark)', 1),
        ('ordinary-producer-rejection', 'ordinary (.error fault : Except Fault NodeId) = false)',
         'ordinary (.error fault : Except Fault NodeId) = true)', 1),
        ('wrong-prepared-arguments', '(ready : Arguments.Prepared request.arguments before source prepared)',
         '(ready : Arguments.Prepared [] before source prepared)', 1),
        ('wrong-prepared-history', 'source request debug prepared leading) expected', 'source request debug prepared []) expected', 1),
        ('wrong-borrowed-address', '.borrowedOperation\n        slice.address opcode', '.borrowedOperation\n        (slice.address + 1) opcode', 1),
        ('wrong-constant-value', '.constant value debug before leading) value', '.constant value debug before leading) (value + 1)', 1),
        ('wrong-materialized-value', '.materialize id value debug before leading) value', '.materialize id value debug before leading) (value + 1)', 1),
        ('wrong-literal-producer', 'Arguments.prepare values before = (.ok source, prepared) →',
         'Arguments.prepare [] before = (.ok source, prepared) →', 1),
        ('wrong-local-producer', 'LocalArguments.zigLocal (view slice) selected repeated first before = (.ok source, prepared) →',
         'LocalArguments.zigLocal (view slice) selected repeated (!first) before = (.ok source, prepared) →', 1),
        ('wrong-local-index-guard', '(inside : first = true → selected < slice.items.length)',
         '(inside : first = false → selected < slice.items.length)', 1),
        ('wrong-parent-cleanup', 'memory := Compiler.ZigAir.Memory.cleanup before.memory.memory.nextId world.memory.memory } })',
         'memory := Compiler.ZigAir.Memory.cleanup (before.memory.memory.nextId + 1) world.memory.memory } })', 3),
    )
    return source, changes


def controls(output, env, lean):
    source, changes = mutation_cases()
    records = checked_controls(output, [mutation_check(output, 'joint-entries-unchanged', source, True, env, lean)])
    for name, before, after, count in changes:
        if source.count(before) != count:
            raise ValueError('ambiguous joint constructor mutation: ' + name)
        records += checked_controls(output, [mutation_check(output, 'joint-entries-' + name,
            source.replace(before, after), False, env, lean)])
    return records
