"""Audit shared native miss frames derived from actual caller provenance.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
import constructor_replay_choice_checks as choice
from native_algebraic_dispatch_checks import source
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check

NS, OWNED = gate.NS, gate.OWNED
CLAIMS = [NS + 'CallFrame.publication_action', NS + 'Enclosing.native_miss_frames']
INTERFACES = (NS + 'Enclosing.insertion_prepared', NS + 'CallFrame.publication')


def audit(claims):
    required = {
        NS + 'CallFrame.publication_action': {OWNED + 'NativeGraph.Facts.finish_publication', OWNED + 'Publication.publish_projection'},
        NS + 'Enclosing.native_miss_frames': {NS + 'Enclosing.missFrames', NS + 'Enclosing.insertion_prepared',
            NS + 'CallFrame.publication_action'},
        NS + 'miss_signextend_unfold_verified': {NS + 'Enclosing.native_miss_frames'},
        gate.ITEM + 'ProtocolTrace.item_enclosing_replay_joint': {NS + 'Enclosing.native_miss_frames'},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('native miss lost shared frame derivation: ' + name + ': ' + ', '.join(sorted(missing)))
    for name in CLAIMS:
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('native miss frame depends on a fixture: ' + name)
    return {'checkedDependencies': sorted(required), 'sameNativeReducerInJointAndRecursiveConsumers': True,
            'logicalSeedRemovedFromFrameDerivation': True, 'completeMissFrameDerived': True,
            'uncoveredInsertionFramesDerived': True, 'resourceAdmissionDerived': False, 'recursiveInductionVerified': False}


def named(value, terms, context, expected):
    if [gate.named(value, term, context) for term in terms] != list(expected):
        raise ValueError('native miss changed source inputs: ' + str(expected))


def reached_obligation(value, field):
    """Retain the exact residual body after its reached world and call frame."""
    root, context = field
    for _ in range(2):
        node = value['nodes'][root]
        if node[0] != 'forall':
            raise ValueError('native miss lost its reached frame')
        context = context + [node[1]]
        root = node[4]
    return root, context


def replace_names(value, replacements):
    if isinstance(value, tuple):
        return tuple(replace_names(part, replacements) for part in value)
    return replacements.get(value, value) if isinstance(value, str) else value


def audit_statements(rows, interfaces):
    from native_constructor_checks import expression
    statements = {row['theorem']: row['statement'] for row in rows}
    definitions = {row['name']: row for row in interfaces}
    value = statements[NS + 'Enclosing.native_miss_frames']
    fields, root, context = gate.domains(value)
    expected = {'σ', 'safety', 'allocator', 'owner', 'parent', 'stack', 'before', 'initial', 'source', 'request', 'values',
                'taken', 'owned', 'lookup', 'origin', 'rows', 'address', 'native', 'ops', 'allocate', 'growth', 'meaning',
                'p', 'published', 'inserted', 'key', 'deterministic', 'simplifying', 'admitted', 'aligned', 'domain'}
    if set(fields) != expected:
        raise ValueError('native miss gained a frame/model premise or lost source inputs')
    origin, local = fields['origin']
    args = joint.app(value, origin, OWNED + 'Caller.Origin')
    named(value, args[-8:], local, ('allocator', 'source', 'request', 'values', 'before', 'taken', 'owned', 'lookup'))
    args = joint.app(value, root, NS + 'MissFrames')
    named(value, args[-5:], context, ('key', 'owned', 'lookup', 'deterministic', 'simplifying'))
    args, local = choice.one_call(value, fields['inserted'][0], fields['inserted'][1], OWNED + 'Insertion.Native.insert')
    named(value, args[-13:], local, ('ops', 'allocate', 'safety', 'allocator', 'owner', 'source', 'address', 'meaning',
                                   'native', 'key', 'slice', 'deterministic', 'growth'))
    args, local = choice.one_call(value, fields['published'][0], fields['published'][1], OWNED + 'Publication.publish')
    named(value, args[-2:], local, ('allocator', 'source'))
    joint.path(value, args[-4], local, (OWNED + 'Insertion.Operations.probe',), 'ops')
    joint.path(value, args[-3], local, (OWNED + 'Insertion.Operations.arguments',), 'ops')
    reference = statements[NS + 'Enclosing.insertion_covered']
    reference_fields, _, _ = gate.domains(reference)
    if expression(value, *fields['domain']) != expression(reference, *reference_fields['domain']):
        raise ValueError('native miss changed the admitted native item domain')

    consumer = statements[NS + 'miss_signextend_unfold_verified']
    entries, _, _ = gate.domains(consumer)
    equality, local = entries['sourceArguments']
    args = joint.app(consumer, equality, 'Eq')
    joint.path(consumer, args[-2], local, ('Compiler.Extraction.Interner.Request.arguments',), 'request')
    named(consumer, args[-1:], local, ('values',))
    origin, local = entries['origin']
    args = joint.app(consumer, origin, OWNED + 'Caller.Origin')
    allocator = expression(consumer, args[-8], local)
    joint.path(consumer, args[-8], local, (gate.ITEM + 'ShiftInput.Context.allocator',), 'base')
    named(consumer, args[-7:], local, ('source', 'request', 'originValues', 'originBefore', 'originTaken', 'normalized', 'lookup'))
    initial, local = entries['originInitial']
    head, args = gate.applied(consumer, initial)
    if head[0] != 'bound' or local[-int(head[1])-1] != 'parent':
        raise ValueError('native miss lost the original enclosing parent')
    named(consumer, args, local, ('originBefore',))
    if {'remaining', 'domain'} & entries.keys():
        raise ValueError('SIGNEXTEND miss must derive insertion coverage and its item tag from the actual key')
    for name in (NS + 'Enclosing.missFrames', NS + 'Enclosing.native_miss_frames', NS + 'miss_signextend_unfold_verified'):
        fields, _, _ = gate.domains(statements[name])
        if {'seed', 'model', 'frames', 'publicationParent', 'releaseParent'} & fields.keys():
            raise ValueError('native miss regained a logical seed or derived parent law')
    return {'sourceOriginAndOriginalParentBound': True, 'actualNativeCallbacksBound': True,
            'residualInsertionPremiseRemoved': True, 'noLogicalSeedOrCompleteMissFramePremise': True,
            'resourceAdmissionDerived': False, 'recursiveInductionVerified': False}


def controls(output, env, lean):
    groups = (
        ('native-publication-action', 'Compiler.Extraction.InternerNativeStep', (
            ('wrong-publish-result', 'let logical := (do let _ ← publish key id; pure id : Interner.Action NodeId)',
             'let logical := (do let _ ← publish key id; pure (id + 1) : Interner.Action NodeId)', 1),
        )),
        ('derived-native-miss', 'Compiler.Extraction.InternerEnclosingNativeMiss', (
            ('missing-original-parent', '(initial : parent before)', '(initial : True)', 1),
            ('wrong-publication-allocator', 'p.publish = Publication.publish ops.probe ops.arguments allocator source',
             'p.publish = Publication.publish ops.probe ops.arguments (allocator + 1) source', 1),
            ('wrong-insertion-owner', 'Insertion.Native.insert ops allocate safety allocator owner source address meaning native key slice deterministic growth)',
             'Insertion.Native.insert ops allocate safety allocator (owner + 1) source address meaning native key slice deterministic growth)', 1),
            ('missing-item-domain', '(domain : (native.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)',
             '(domain : True)', 1),
        )),
        ('derived-recursive-miss', 'Compiler.Extraction.InternerNativeStepDispatch', (
            ('wrong-source-arguments', 'request.arguments = values', 'request.arguments = normalized.items', 1),
            ('rebase-parent-origin', '(originInitial : parent originBefore)', '(originInitial : parent before)', 1),
        )),
    )
    records = []
    for label, module, changes in groups:
        original = source(module)
        records += checked_controls(output, [mutation_check(output, label + '-unchanged', original, True, env, lean)])
        for name, before, after, count in changes:
            if original.count(before) != count:
                raise ValueError('ambiguous derived miss mutation: ' + name + ': ' + str(original.count(before)))
            records += checked_controls(output, [mutation_check(output, label + '-' + name, original.replace(before, after), False, env, lean)])
    return records
