"""Audit derived parent laws for finite nesting of existing native call frames.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as gate
import constructor_joint_checks as joint
import constructor_replay_choice_checks as choice
import enclosing_publication_checks as publication
import enclosing_rollback_checks as rollback
import native_transferred_preparation_checks as transferred
import native_backing_mode_checks as backing
import native_transferred_success_checks as success
from assembly_item_creation_checks import checked_controls
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NS, PNS, OWNED = gate.NS, joint.PNS, gate.OWNED
MODULE = 'Compiler.Extraction.InternerConstructorEnclosingInduction'
CLAIMS = [NS + 'Enclosing.' + name for name in ('retained', 'locals', 'release', 'publish', 'missFrames')]
CLAIMS += [PNS + 'item_enclosing_replay_joint']
INSERTION_CLAIMS = [OWNED + 'NativeGraph.Facts.graph', NS + 'CallFrame.backing_oom_execution']
INSERTION_CLAIMS += [NS + 'Enclosing.' + name for name in ('logical_fields', 'private_frame', 'insertion_unpublished', 'insertion_frame')]
CLAIMS += INSERTION_CLAIMS + publication.CLAIMS + rollback.CLAIMS + transferred.CLAIMS + backing.CLAIMS + success.CLAIMS
INTERFACES = tuple(NS + 'Enclosing' + suffix for suffix in ('', '.root', '.call')) + (PNS + 'item_replay_joint',) + publication.INTERFACES + rollback.INTERFACES + transferred.INTERFACES + backing.INTERFACES + success.INTERFACES
COMMON = {'σ', 'safety', 'allocator', 'owner', 'parent', 'stack', 'before', 'initial'}
ORIGIN = {'source', 'request', 'values', 'taken', 'owned', 'lookup', 'origin'}


def parent_at(value, root, context):
    head, args = gate.applied(value, root)
    if head[0] != 'bound' or context[-int(head[1]) - 1] != 'parent' or len(args) != 1:
        raise ValueError('enclosing frame lost its original parent predicate')
    return args[0]


def audit_statements(rows, interfaces):
    from native_constructor_checks import expression
    statements = {row['theorem']: row['statement'] for row in rows}
    definitions = {row['name']: row for row in interfaces}
    enclosing = definitions[NS + 'Enclosing']
    if enclosing['kind'] != 'inductive' or enclosing['constructors'] != [NS + 'Enclosing.root', NS + 'Enclosing.call']:
        raise ValueError('enclosing frames admit an arbitrary predicate or final-state law')
    value = definitions[NS + 'Enclosing.root']['type']
    fields, root, context = gate.domains(value)
    if len(fields) != 4 or list(fields)[:3] != ['safety', 'allocator', 'owner']:
        raise ValueError('enclosing root added an admission premise')
    args = joint.app(value, root, NS + 'Enclosing')
    predicate = value['nodes'][args[-1]]
    if predicate[0] != 'lambda' or gate.named(value, predicate[4], context + [predicate[1]]) != 'True':
        raise ValueError('enclosing root is not the empty live frame')
    value = definitions[NS + 'Enclosing.call']['type']
    fields, root, context = gate.domains(value)
    if set(fields) != {'σ', 'safety', 'allocator', 'owner', 'rows', 'source', 'values', 'normalized', 'address', 'native', 'parent', 'outer'}:
        raise ValueError('enclosing call added a preservation premise')
    args = joint.app(value, root, NS + 'Enclosing')
    if [gate.named(value, x, context) for x in args[:-1]] != ['safety', 'allocator', 'owner', 'σ']:
        raise ValueError('enclosing call changed allocator or owner identity')
    frame = joint.app(value, args[-1], NS + 'CallFrame')
    if [gate.named(value, x, context) for x in frame] != ['σ', 'safety', 'allocator', 'owner', 'rows', 'source', 'values', 'normalized', 'address', 'native', 'parent']:
        raise ValueError('enclosing call replaced existing native geometry or outer frame')
    index, local = fields['outer']
    args = joint.app(value, index, NS + 'Enclosing')
    if [gate.named(value, x, local) for x in args] != ['safety', 'allocator', 'owner', 'σ', 'parent']:
        raise ValueError('enclosing call no longer requires a finite outer chain')
    expected = {
        'retained': COMMON | {'after', 'valid', 'graph', 'kept'},
        'locals': COMMON | {'itemMark', 'scratchMark', 'itemOrdered', 'scratchOrdered', 'world'},
        'release': COMMON | ORIGIN | {'world', 'reached', 'host', 'rows', 'projected', 'custody', 'after', 'freed'},
        'publish': COMMON | ORIGIN | {'world', 'rows', 'address', 'native', 'frame', 'hostProbe', 'host', 'key', 'id', 'aligned'},
        'missFrames': COMMON | ORIGIN | {'rows', 'address', 'native', 'hostProbe', 'host', 'p', 'published', 'key',
            'deterministic', 'simplifying', 'aligned', 'insertion'},
    }
    forbidden = {NS + 'Returns', NS + 'InvocationPost', PNS + 'JointPost', PNS + 'JointEntry', PNS + 'SiteChildren',
                 NS + 'MissFrames', OWNED + 'Semantic.Ensures'}
    for name, wanted in expected.items():
        value = statements[NS + 'Enclosing.' + name]
        fields, root, context = gate.domains(value)
        actual = set(fields)
        if name == 'locals':
            index, local = list(fields.values())[-1]
            if gate.named(value, parent_at(value, index, local), local) != 'world':
                raise ValueError('enclosing cleanup lost the reached parent')
            actual.remove(list(fields)[-1])
        if actual != wanted:
            raise ValueError('enclosing proof added an outer law or lost a source observation: ' + name)
        for field, (index, _) in fields.items():
            if forbidden & gate.step.constants_below(value, index):
                raise ValueError('enclosing proof assumes a final preservation result: ' + name + '.' + field)
        if name == 'missFrames':
            args = joint.app(value, root, NS + 'MissFrames')
            if [gate.named(value, x, context) for x in args[-5:]] != ['key', 'owned', 'lookup', 'deterministic', 'simplifying']:
                raise ValueError('derived suffix frames changed the actual scope or branch')
            continue
        index = parent_at(value, root, context)
        if name == 'retained' and gate.named(value, index, context) != 'after':
            raise ValueError('enclosing retention rewinds the reached world')
        if name == 'locals':
            args = joint.app(value, index, gate.ITEM + 'returnWorld')
            if [gate.named(value, x, context) for x in args[-3:]] != ['itemMark', 'scratchMark', 'world']:
                raise ValueError('enclosing cleanup changed its marks or reached state')
        if name == 'release':
            args = joint.app(value, index, OWNED + 'World.mk')
            joint.path(value, args[-2], context, (OWNED + 'World.graph',), 'world')
            if gate.named(value, args[-1], context) != 'after':
                raise ValueError('enclosing release lost its actual session')
        if name == 'publish':
            args = joint.app(value, index, 'Prod.snd')
            call = joint.app(value, args[-1], OWNED + 'Publication.publish')
            if [gate.named(value, x, context) for x in call[-8:]] != ['hostProbe', 'host', 'allocator', 'source', 'key', 'owned', 'id', 'world']:
                raise ValueError('enclosing publication changed its native invocation')
    value = statements[PNS + 'item_enclosing_replay_joint']
    fields, root, context = gate.domains(value)
    wanted = (choice.PARAMETERS - {'retained', 'localParent', 'laws'}) | {'capacity', 'data', 'stack', 'initial',
        'facts', 'represented', 'privateSource', 'admitted', 'domain', 'typed', 'capacityQuery', 'classificationQuery',
        'expected', 'valid', 'evaluated', 'pushes', 'proper', 'array'}
    if set(fields) != wanted:
        raise ValueError('enclosing item added a premise or lost its general inputs')
    for field, (index, _) in fields.items():
        constants = gate.step.constants_below(value, index)
        if forbidden & constants or NS + 'FramePost' in constants:
            raise ValueError('enclosing item assumes a derived result: ' + field)
    for field in ('proper',):
        index, local = fields[field]
        choice.one_call(value, index, local, PNS + 'TakenSite.Reached')
    needed = {'Compiler.Extraction.Dispatch.Effects.SourceConstructorsAt', 'Compiler.Extraction.Associative.ConstructorSound',
              'Compiler.Extraction.AddressMask.Constructs', 'Compiler.Extraction.ArithmeticShift.Constructs'}
    if not needed <= gate.step.constants_below(value, fields['proper'][0]):
        raise ValueError('enclosing item lost a proper-child contract')
    original = definitions[PNS + 'item_replay_joint']['type']
    _, old_root, old_context = gate.domains(original)
    if expression(value, root, context) != expression(original, old_root, old_context):
        raise ValueError('enclosing item weakened or rebound the shared joint conclusion')
    audit_insertion(statements)
    publication.audit_statements(statements, definitions)
    rollback.audit_statements(statements, definitions)
    transferred.audit_statements(statements, definitions)
    backing.audit_statements(statements, definitions)
    success.audit_statements(statements, definitions)
    return {'finiteExistingCallFrames': True, 'retainedAndLocalParentLawsDerived': True,
            'publicationAndFailureFramesDerived': True, 'sameJointItemConclusion': True,
            'properChildrenAndInsertionFramesRequired': True, 'successfulInsertionFramesDerived': True,
            'sourceProvenanceCarried': True, 'publicationRollbackFramesDerived': True, 'bothPreparationFramesDerived': True, 'bothBackingFramesDerived': True, 'transferredGrowthFramesDerived': True, 'transferredFirstAndSpareFramesDerived': True, 'initialArrayProvenanceRequired': True, 'earlyInsertionFailureFramesDerived': True, 'uniformRecursiveModelVerified': False,
            'recursiveInductionVerified': False, 'composedProductionTheoremVerified': False}


def insertion_gates(value, index, context, deterministic, published=False, refused=False, transferred=False):
    """Check exactly the reached capacity and guarded native refusal exclusions."""
    nodes = value['nodes']
    conditions = []
    for _ in range(3 + int(published) + int(refused) + int(transferred)):
        node = nodes[index]
        if node[0] != 'forall':
            raise ValueError('residual insertion lost a required branch exclusion')
        conditions.append((node[3], context[:]))
        context = context + [node[1]]
        index = node[4]
    room, local = conditions[0]
    args = joint.app(value, room, 'LT.lt')
    sub = joint.app(value, args[-1], 'HSub.hSub')
    power = joint.app(value, sub[-2], 'HPow.hPow')
    for term, number in ((sub[-1], '1'), (power[-2], '2'), (power[-1], '32')):
        literal = joint.app(value, term, 'OfNat.ofNat')
        if nodes[literal[-2]] != ['natural', number]:
            raise ValueError('residual insertion changed the native capacity bound')
    selected, reached = choice.one_call(value, args[-2], local, 'Compiler.Extraction.Interner.Heap.representatives')
    joint.path(value, selected[-1], reached, (OWNED + 'World.graph',), 'world')
    preparation, local = conditions[1]
    negated = joint.app(value, preparation, 'Not')
    args = joint.app(value, negated[-1], OWNED + 'Insertion.Native.PreparationOOMAt')
    if deterministic is None:
        joint.path(value, args[-2], local, (PNS + 'TakenSite.deterministic',), 'site')
    elif gate.named(value, args[-2], local) != deterministic:
        raise ValueError('preparation exclusion changed its source branch')
    joint.path(value, args[-1], local, (OWNED + 'World.memory',), 'world')
    condition, local = conditions[2]
    negated = joint.app(value, condition, 'Not')
    args = joint.app(value, negated[-1], OWNED + 'Insertion.Native.BackingAllocationOOMAt')
    if deterministic is None:
        joint.path(value, args[-3], local, (PNS + 'TakenSite.deterministic',), 'site')
    elif gate.named(value, args[-3], local) != deterministic:
        raise ValueError('backing exclusion changed its source branch')
    if gate.named(value, args[-1], local) != 'world':
        raise ValueError('backing exclusion changed its reached world')
    names = (('PublishedObservation',) if published else ()) + (('RefusedObservation',) if refused else ()) + (('TransferredObservation',) if transferred else ())
    publication = None
    for (condition, local), name in zip(conditions[3:], names):
        guard = nodes[condition]
        if guard[0] != 'forall':
            raise ValueError('insertion refusal exclusion lost its deterministic guard')
        equal = joint.app(value, guard[3], 'Eq')
        if deterministic is None:
            joint.path(value, equal[-2], local, (PNS + 'TakenSite.deterministic',), 'site')
        elif gate.named(value, equal[-2], local) != deterministic:
            raise ValueError('insertion refusal exclusion uses a different branch')
        if gate.named(value, equal[-1], local) != ('Bool.false' if name == 'TransferredObservation' else 'Bool.true'):
            raise ValueError('insertion refusal exclusion inverted its deterministic guard')
        negated = joint.app(value, guard[4], 'Not')
        args = joint.app(value, negated[-1], OWNED + 'Insertion.Native.' + name)
        if name == 'TransferredObservation':
            names_expected = ['σ', 'ops', 'allocate', 'allocator', 'owner', 'native', 'growth', 'world']
            if deterministic is not None:
                if [gate.named(value, x, local + [guard[1]]) for x in args] != names_expected:
                    raise ValueError('transfer exclusion changed its reached input')
            else:
                if gate.named(value, args[-1], local + [guard[1]]) != 'world':
                    raise ValueError('item transfer exclusion changed its reached world')
                call, scope = choice.one_call(value, args[-3], local + [guard[1]], gate.ITEM + 'input')
                if gate.named(value, call[-1], scope) != 'debug':
                    raise ValueError('item transfer exclusion changed its actual input')
        if name in ('PublishedObservation', 'RefusedObservation'):
            from native_constructor_checks import expression
            bound = [expression(value, term, local + [guard[1]]) for term in args]
            if name == 'PublishedObservation':
                publication = bound
            elif bound != publication:
                raise ValueError('rollback exclusion describes a different publication call')
    return index, context


def audit_insertion(statements):
    from native_constructor_checks import expression
    native = COMMON | ORIGIN | {'world', 'rows', 'address', 'native', 'frame', 'ops', 'allocate', 'growth', 'meaning', 'key', 'deterministic'}
    expected = {
        OWNED + 'NativeGraph.Facts.graph': {'σ', 'safety', 'allocator', 'owner', 'capacity', 'data', 'rows', 'world', 'facts', 'graph', 'representatives', 'table'},
        NS + 'Enclosing.logical_fields': {'σ', 'safety', 'allocator', 'owner', 'parent', 'stack', 'world', 'held', 'graph', 'representatives', 'table'},
        NS + 'Enclosing.private_frame': COMMON | ORIGIN | {'world', 'reached', 'rows', 'projected', 'custody', 'after', 'valid', 'frame'},
        NS + 'Enclosing.insertion_unpublished': native | {'outcome', 'closed', 'after', 'executed', 'unappended', 'unpublished', 'valid', 'retained'},
        NS + 'Enclosing.insertion_frame': native | {'admitted', 'remaining'},
        NS + 'CallFrame.backing_oom_execution': {'σ', 'safety', 'allocator', 'owner', 'rows', 'source', 'values', 'normalized',
            'address', 'native', 'parent', 'world', 'frame', 'ops', 'allocate', 'growth', 'meaning', 'key', 'room', 'admitted', 'failed'},
    }
    forbidden = {NS + 'Returns', NS + 'InvocationPost', NS + 'MissFrames', PNS + 'JointPost', PNS + 'JointEntry',
                 PNS + 'SiteChildren', OWNED + 'Semantic.Ensures', 'Compiler.Extraction.Interner.Represented'}
    for name, wanted in expected.items():
        value = statements[name]
        fields, root, context = gate.domains(value)
        if set(fields) != wanted:
            raise ValueError('private insertion added a law or lost a source observation: ' + name)
        for field, (index, _) in fields.items():
            constants = gate.step.constants_below(value, index)
            if forbidden & constants or (field != 'remaining' and NS + 'FramePost' in constants):
                raise ValueError('private insertion assumes a final result: ' + name + '.' + field)
        if name.endswith('.insertion_frame'):
            index, local = fields['remaining']
            index, local = insertion_gates(value, index, local, 'deterministic')
            # Strip the shared local ran binding without changing its value.
            node = value['nodes'][index]
            if node[0] != 'let':
                raise ValueError('residual insertion changed the native handoff binding')
            final = value['root']
            while value['nodes'][final][0] == 'forall':
                final = value['nodes'][final][4]
            if expression(value, index, local) != expression(value, final, context[:-1]):
                raise ValueError('residual insertion and derived frame concern different native runs')
        if name.endswith('.insertion_unpublished') or name.endswith('.insertion_frame'):
            args = joint.app(value, root, NS + 'FramePost')
            choice.one_call(value, args[-1], context, OWNED + 'finish')
            final, local = value['root'], []
            while value['nodes'][final][0] == 'forall':
                node = value['nodes'][final]
                local, final = local + [node[1]], node[4]
            choice.one_call(value, value['nodes'][final][3], local, OWNED + 'Insertion.Native.insert')
    fields, _, _ = gate.domains(statements[PNS + 'item_enclosing_replay_joint'])
    if 'insertion' in fields:
        raise ValueError('joint item regained a residual insertion frame premise')



def audit(claims):
    required = {
        OWNED + 'NativeGraph.Facts.graph': {OWNED + 'NativeGraph.Facts'},
        NS + 'Enclosing.logical_fields': {OWNED + 'NativeGraph.Facts.graph', NS + 'Enclosing.rec'},
        NS + 'Enclosing.private_frame': {NS + 'CallFrame.private_frame', NS + 'Enclosing.rec'},
        NS + 'CallFrame.backing_oom_execution': {NS + 'CallFrame.backing_oom_execution_at'},
        NS + 'Enclosing.insertion_unpublished': {NS + 'Enclosing.private_frame', NS + 'Enclosing.logical_fields',
            OWNED + 'NativeGraph.Facts.frame_private', OWNED + 'Insertion.Native.insert_unpublished_projected', OWNED + 'finish_handoff'},
        NS + 'Enclosing.insertion_frame': {NS + 'Enclosing.insertion_unpublished', NS + 'CallFrame.backing_oom_execution_at',
            OWNED + 'Insertion.Native.preparation_oom_execution_at', OWNED + 'Insertion.Native.capacity_execution'},
        NS + 'Enclosing.retained': {NS + 'CallFrame.frame', NS + 'Enclosing.rec'},
        NS + 'Enclosing.locals': {NS + 'CallFrame.locals', NS + 'Enclosing.rec'},
        NS + 'Enclosing.release': {NS + 'CallFrame.release', NS + 'Enclosing.rec'},
        NS + 'Enclosing.publish': {NS + 'CallFrame.publish_parent', NS + 'Enclosing.rec'},
        NS + 'Enclosing.missFrames': {NS + 'Enclosing.release', NS + 'Enclosing.publish', NS + 'CallFrame.failure', NS + 'CallFrame.publication_action'},
        PNS + 'item_enclosing_replay_joint': {NS + 'Enclosing.retained', NS + 'Enclosing.locals', NS + 'Enclosing.missFrames',
            PNS + 'item_replay_joint', gate.ITEM + 'prepare_success', NS + 'Enclosing.insertion_rollback_derived', NS + 'Enclosing.native_miss_frames'},
    }
    required.update(publication.dependencies())
    required.update(rollback.dependencies())
    required.update(transferred.dependencies())
    required.update(backing.dependencies())
    required.update(success.dependencies())
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError('enclosing proof lost shared reasoning: ' + name + ': ' + ', '.join(sorted(missing)))
        if any(part.endswith('Tests') for dep in claims[name] for part in dep.split('.')):
            raise ValueError('enclosing proof depends on a fixture: ' + name)
    return {'checkedDependencies': sorted(required), 'structuralInductionOverEnclosingCalls': True,
            'recursiveInductionVerified': False, 'composedProductionTheoremVerified': False}


def mutation_cases():
    directory = gate.harness.ROOT / 'lean/Compiler/Extraction'
    source = 'import Compiler.Extraction.InternerConstructorReplayChoice\nimport Compiler.Extraction.InternerNativeUnrelocatedTransferred\nimport Compiler.Extraction.InternerInsertionOutcomeCoverage\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n'
    source += '\n'.join(without_imports((directory / (name + '.lean')).read_text()) for name in (
        'InternerEnclosingFrames', 'InternerEnclosingMissFrames', 'InternerEnclosingPrivateFrames',
        'InternerEnclosingInsertionFailure',
        'InternerEnclosingPublishedFrames', 'InternerEnclosingTransferredFrames', 'InternerEnclosingRollbackFrames',
        'InternerEnclosingPreparationCoverage', 'InternerEnclosingInsertionCoverage', 'InternerEnclosingNativeMiss', 'InternerConstructorEnclosingInduction'))
    source += '\nopen ' + NS.rstrip('.') + '\nexample (safety : Bool) (allocator owner : Nat) : Enclosing (σ := Unit) safety allocator owner (fun _ => True) := .root\n'
    changes = (
        ('wrong-root', '| root : Enclosing safety allocator owner (fun _ => True)', '| root : Enclosing safety allocator owner (fun _ => False)', 1),
        ('wrong-call-allocator', 'Enclosing safety allocator owner (CallFrame safety allocator owner rows', 'Enclosing safety allocator owner (CallFrame safety (allocator + 1) owner rows', 1),
        ('missing-retention', '(kept : Retains before after)', '(kept : Retains before before)', 1),
        ('wrong-item-order', 'before.memory.memory.nextId ≤ itemMark', 'itemMark ≤ before.memory.memory.nextId', 1),
        ('wrong-scratch-order', 'before.memory.memory.nextId ≤ scratchMark', 'scratchMark ≤ before.memory.memory.nextId', 1),
        ('wrong-local-mark', 'parent (returnWorld itemMark scratchMark world)', 'parent (returnWorld 0 scratchMark world)', 1),
        ('rebase-origin', 'Caller.Origin allocator source request values before taken owned lookup)\n    (host : External σ) {rows', 'Caller.Origin allocator source request values world taken owned lookup)\n    (host : External σ) {rows', 1),
        ('wrong-free-allocator', 'allocator owned world.memory = (.ok (), after)', '(allocator + 1) owned world.memory = (.ok (), after)', 1),
        ('missing-publication-key', '(aligned : key.arguments = owned.items)', '(aligned : key.arguments = key.arguments)', 9),
        ('rewind-outer-publication', '(ih initial.parent ⟨frame.1, frame.2.1, frame.parent.parent, frame.arraySource⟩)', 'initial.parent', 1),
        ('wrong-publication-binding', 'p.publish = Publication.publish hostProbe host allocator source', 'p.publish = Publication.publish hostProbe host (allocator + 1) source', 1),
        ('wrong-probe-decision', 'Interner.publish (hostProbe key (Publication.forget world.memory)).1', 'Interner.publish (!(hostProbe key (Publication.forget world.memory)).1)', 1),
        ('missing-initial-parent', '(stack : Enclosing safety base.allocator owner parent) (initial : parent before)', '(stack : Enclosing safety base.allocator owner parent) (initial : True)', 1),
        ('missing-covered-domain', '(domain : (native.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)', '(domain : True)', 2),
        ('wrong-child-guard', '((site.deterministic && (request.item.kind == 1)) = true →', '((!site.deterministic && (request.item.kind == 1)) = true →', 4),
        ('wrong-final-word', 'source request debug before leading) expected := by', 'source request debug before leading) (expected + 1) := by', 1),
        ('wrong-native-rows', '(representatives : graph.representatives = world.graph.representatives)', '(representatives : graph.representatives = graph.representatives)', 2),
        ('wrong-native-table', '(table : graph.table = world.graph.table)', '(table : graph.table = graph.table)', 2),
        ('wrong-private-frame', '(frame : Insertion.Native.PrivateFrame owned world.memory after)', '(frame : Insertion.Native.PrivateFrame owned after after)', 1),
        ('missing-unappended', '(unappended : closed.appended = false)', '(unappended : closed.appended = true)', 1),
        ('missing-unpublished', '(unpublished : closed.published = false)', '(unpublished : closed.published = true)', 1),
        ('wrong-cleanup-validity', '(valid : Valid (Insertion.memory after))', '(valid : Valid world.memory)', 1),
        ('wrong-residual-capacity', '(remaining : (world.graph.representatives.getD []).length < 2 ^ 32 - 1', '(remaining : (world.graph.representatives.getD []).length < 2 ^ 32 - 2', 4),
        ('wrong-preparation-branch', 'PreparationOOMAt ops allocator native owned deterministic world.memory',
         'PreparationOOMAt ops allocator native owned (!deterministic) world.memory', 5),

        ('wrong-backing-branch', 'BackingAllocationOOMAt ops allocate allocator owner native owned deterministic growth world',
         'BackingAllocationOOMAt ops allocate allocator owner native owned (!deterministic) growth world', 5),

        ('wrong-capacity-rows', 'deterministic (world.graph.representatives.getD []) world growth released', 'deterministic [] world growth released', 1),
    )
    changes += (
        ('wrong-transfer-exclusion', '(deterministic = false → ¬ Insertion.Native.TransferredObservation',
         '(deterministic = true → ¬ Insertion.Native.TransferredObservation', 2),

    )
    return source, changes + publication.mutations() + rollback.mutations()


def controls(output, env, lean):
    source, changes = mutation_cases()
    records = checked_controls(output, [mutation_check(output, 'enclosing-unchanged', source, True, env, lean)])
    for name, before, after, count in changes:
        if source.count(before) != count:
            raise ValueError('ambiguous enclosing frame mutation: ' + name)
        records += checked_controls(output, [mutation_check(output, 'enclosing-' + name,
            source.replace(before, after), False, env, lean)])
    return records + publication.controls(output, env, lean) + rollback.controls(output, env, lean) + transferred.controls(output, env, lean) + backing.controls(output, env, lean) + success.controls(output, env, lean)
