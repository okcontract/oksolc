#!/usr/bin/env python3
"""Audit the proper-child taken-miss step and its remaining local obligations.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
from build_toolchain import digest
import constructor_argument_checks as arguments
import native_recursion_checks as recursion
import native_frame_checks as frames
import native_word_checks as words

NS = recursion.NS
INTERNER = 'Compiler.Extraction.Interner.'
CLAIMS = [NS + name for name in ('GraphFrame.locals', 'CallFrame.failure', 'CallFrame.failure_parent', 'CallFrame.publication', 'CallFrame.publication_parent', 'miss_step', 'CallFrame.caller',
    'CallFrame.preparation', 'CallFrame.prepare_native', 'Returns.locals', 'invoke_step', 'invoke_direct',
    'invoke_step_verified', 'invoke_direct_verified', 'step_taken_verified')]
CLAIMS += [INTERNER + 'miss_safe_branches', INTERNER + 'miss_safe_at', INTERNER + 'miss_safe']
CLAIMS += [recursion.FACTS + 'cleanup_post']
CLAIMS += [arguments.OWNED + 'Publication.publish_projection']
CLAIMS += [arguments.OWNED + 'Insertion.Native.prepare_reached']
CLAIMS += frames.CLAIMS
CLAIMS += words.CLAIMS

def publication_union():
    """Bind the observed-case union to its exact reviewed source definition."""
    path = ROOT / 'lean/Compiler/Extraction/InternerNativePublishedCompletion.lean'
    source = path.read_text()
    marker = 'def PublishedObservation '
    if source.count(marker) != 1:
        raise ValueError('missing or ambiguous publication union')
    definition = source.split(marker, 1)[1].split('\nend ', 1)[0]
    body = ' '.join(definition.split(': Prop :=', 1)[1].split())
    prefix = 'ops allocate safety allocator owner meaning input key normalized '
    expected = ' ∨ '.join((name + ' ' + prefix + suffix for name, suffix in (
        ('FirstPublished', 'world'), ('SparePublished', 'world'), ('RelocatedPublished', 'growth world'))))
    if body != expected:
        raise ValueError('publication union lost or changed a source-observed case')
    return {'source': str(path.relative_to(ROOT)), 'sourceSha256': digest(path),
            'cases': ['first', 'spare', 'relocated'], 'finalFrameAssumed': False}


def refusal_union():
    """Bind each actual refusal, including its allocation adapter, to the union."""
    path = ROOT / 'lean/Compiler/Extraction/InternerNativePublicationRollback.lean'
    source = path.read_text()
    marker = 'def RefusedObservation '
    if source.count(marker) != 1:
        raise ValueError('missing or ambiguous refusal union')
    body = ' '.join(source.split(marker, 1)[1].split('\nend ', 1)[0].split(': Prop :=', 1)[1].split())
    prefix = 'ops allocate safety allocator owner meaning input key normalized '
    expected = ' ∨ '.join(name + ' ' + prefix + suffix for name, suffix in (
        ('FirstPublication', 'false world'), ('SparePublication', 'false world'), ('RelocatedPublication', 'growth false world')))
    if body != expected:
        raise ValueError('refusal union lost a case, probe decision or growth identity')
    return {'source': str(path.relative_to(ROOT)), 'sourceSha256': digest(path),
            'cases': ['first', 'spare', 'relocated'], 'finalFrameAssumed': False}


def constants_below(statement, root):
    nodes, pending, seen, constants = statement['nodes'], [root], set(), set()
    while pending:
        index = pending.pop()
        if index in seen:
            continue
        seen.add(index)
        node = nodes[index]
        if node[0] == 'const':
            constants.add(node[1])
        elif node[0] == 'app':
            pending.extend(node[1:3])
        elif node[0] in ('forall', 'lambda'):
            pending.extend(node[3:5])
        elif node[0] == 'let':
            pending.extend(node[2:5])
        elif node[0] == 'projection':
            pending.append(node[3])
    return constants


def remaining_guards(statement, binder):
    """Inspect the remaining obligation's own premises, not its enclosing type."""
    if statement.get('encoding') != 'kernelExprDag-v1':
        raise ValueError('unsupported insertion model statement encoding')
    selected = [node for node in statement['nodes'] if node[0] == 'forall' and node[1] == binder]
    if len(selected) != 1:
        raise ValueError('missing or ambiguous remaining insertion binder: ' + binder)
    index, domains = selected[0][3], []
    while statement['nodes'][index][0] in ('forall', 'let'):
        node = statement['nodes'][index]
        if node[0] == 'let':
            index = node[4]
            continue
        domain = node[3]
        head = statement['nodes'][domain]
        while head[0] == 'app':
            head = statement['nodes'][head[1]]
        domains.append((head[1] if head[0] == 'const' else None, constants_below(statement, domain)))
        index = node[4]
    if not any(head == 'Not' and arguments.OWNED + 'Insertion.Native.PreparationOOM' in constants for head, constants in domains):
        raise ValueError('remaining insertion does not exclude actual preparation OOM')
    if not any(head == 'Not' and arguments.OWNED + 'Insertion.Native.BackingAllocationOOM' in constants for head, constants in domains):
        raise ValueError('remaining insertion does not exclude actual backing-allocation OOM')
    if not any(head == 'Not' and arguments.OWNED + 'Insertion.Native.PublishedObservation' in constants for head, constants in domains):
        raise ValueError('remaining insertion does not exclude the actual publication union')
    if not any(head == 'Not' and arguments.OWNED + 'Insertion.Native.RefusedObservation' in constants
               for head, constants in domains):
        raise ValueError('remaining insertion does not exclude actual first/spare/relocated publication refusal')
    if not any(head == 'LT.lt' and 'Option.getD' in constants for head, constants in domains):
        raise ValueError('remaining insertion lost its reached room premise')
    conclusion = statement['nodes'][index]
    while conclusion[0] == 'app':
        conclusion = statement['nodes'][conclusion[1]]
    local_constants = constants_below(statement, selected[0][3])
    if (conclusion[:2] != ['const', NS + 'GraphFrame'] or
            {NS + 'Returns', 'Compiler.Extraction.Interner.observedInsert'} & local_constants):
        raise ValueError('remaining insertion assumes logical correspondence instead of its native frame')
    if not any(arguments.OWNED + 'ordinary' in constants for _, constants in domains):
        raise ValueError('remaining native frame lost ordinary-completion guard')


def insertion_parent(statement, binder, observation, accepted=None):
    """Require only the enclosing parent predicate at the actual insert result."""
    nodes, index, context = statement['nodes'], statement['root'], []
    while nodes[index][0] in ('forall', 'let'):
        node = nodes[index]
        if node[0] == 'forall' and node[1] == binder:
            index = node[3]
            break
        context.append(node[1])
        index = node[4]
    else:
        raise ValueError('missing separate published parent obligation')
    domains = []
    while nodes[index][0] in ('forall', 'let'):
        node = nodes[index]
        if node[0] == 'forall':
            domain, head = node[3], nodes[node[3]]
            while head[0] == 'app':
                head = nodes[head[1]]
            domains.append((head[1] if head[0] == 'const' else None, constants_below(statement, domain)))
        context.append(node[1])
        index = node[4]
    head = nodes[index]
    while head[0] == 'app':
        head = nodes[head[1]]
    conclusion = constants_below(statement, index)
    obligation_constants = conclusion | set().union(*(constants for _, constants in domains))
    native = arguments.OWNED + 'Insertion.Native.'
    insert = {native + 'insert', arguments.OWNED + 'Primitives.insert'}
    if (head[0] != 'bound' or context[-int(head[1]) - 1] != 'parent' or not (insert & conclusion) or
            {NS + 'GraphFrame', NS + 'Returns', recursion.FACTS.rstrip('.')} & obligation_constants):
        raise ValueError('published parent obligation assumes more than the enclosing parent at actual insertion')
    if not any(head == native + observation and native + observation in constants
               and (accepted is None or accepted in constants) for head, constants in domains):
        raise ValueError('published parent obligation lost actual success observations')
    if not any(head == 'Not' and native + 'PreparationOOM' in constants for head, constants in domains):
        raise ValueError('published parent obligation lost its preparation guard')
    if not any(head == 'LT.lt' and 'Option.getD' in constants for head, constants in domains):
        raise ValueError('published parent obligation lost reached room')


def published_parent(statement):
    insertion_parent(statement, 'publishedParent', 'PublishedObservation')


def rollback_parent(statement):
    insertion_parent(statement, 'rollbackParent', 'RefusedObservation')


def preparation_candidate(statement, binder):
    """The local candidate obligation binds preparation, never the final cell."""
    selected = [node for node in statement['nodes'] if node[0] == 'forall' and node[1] == binder]
    if len(selected) != 1:
        raise ValueError('missing or ambiguous candidate binder: ' + binder)
    constants = constants_below(statement, selected[0][3])
    native = arguments.OWNED + 'Insertion.Native.'
    if native + 'observedCandidate' not in constants or arguments.OWNED + 'Insertion.cell' in constants:
        raise ValueError('candidate obligation lost preparation or assumes the final cell')


def release_parent_guard(statement, world_name, binder='releaseParent', predicate='parent'):
    """The law protects a private owner in the same actual reached graph."""
    nodes, index, context = statement['nodes'], statement['root'], []
    while nodes[index][0] in ('forall', 'let'):
        node = nodes[index]
        if node[0] == 'forall' and node[1] == binder:
            index = node[3]
            break
        context.append(node[1])
        index = node[4]
    else:
        raise ValueError('missing guarded release-parent law')

    def applied(root):
        args = []
        while nodes[root][0] == 'app':
            args.append(nodes[root][2])
            root = nodes[root][1]
        return nodes[root], list(reversed(args))

    def bound(root, name):
        node = nodes[root]
        return node[0] == 'bound' and context[-int(node[1]) - 1] == name

    def contains(root, name):
        node = nodes[root]
        if node[0] == 'bound':
            return bound(root, name)
        if node[0] == 'app':
            return contains(node[1], name) or contains(node[2], name)
        if node[0] == 'projection':
            return contains(node[3], name)
        return False

    guarded, projected = False, False
    while nodes[index][0] in ('forall', 'let'):
        node = nodes[index]
        if node[0] == 'forall':
            head, args = applied(node[3])
            if head[:2] == ['const', arguments.OWNED + 'Caller.GraphCustody']:
                guarded = (len(args) >= 3 and bound(args[-3], 'normalized') and
                           bound(args[-2], 'currentRows') and contains(args[-1], world_name))
            if head[:2] == ['const', 'Eq'] and len(args) == 3:
                right, right_args = applied(args[-1])
                if right[:2] == ['const', 'Option.some'] and right_args and bound(right_args[-1], 'currentRows'):
                    projected = contains(args[-2], world_name)
        context.append(node[1])
        index = node[4]
    head, _ = applied(index)
    if not guarded or not projected or head[0] != 'bound' or context[-int(head[1]) - 1] != predicate:
        raise ValueError('release-parent law lost same-owner custody, reached projection or separate parent conclusion')


def branch_interfaces(rows):
    """Bind dispatch and direct-entry assumptions to the actual classifier guard."""
    def domains(statement):
        if statement.get('encoding') != 'kernelExprDag-v1':
            raise ValueError('unsupported branch statement encoding')
        nodes, index, context, result = statement['nodes'], statement['root'], [], {}
        while nodes[index][0] in ('forall', 'let'):
            node = nodes[index]
            if node[0] == 'forall':
                result[node[1]] = (node[3], context[:])
            context.append(node[1])
            index = node[4]
        return nodes, result

    def applied(nodes, root):
        args = []
        while nodes[root][0] == 'app':
            args.append(nodes[root][2])
            root = nodes[root][1]
        return nodes[root], list(reversed(args))

    def named(nodes, root, context):
        node = nodes[root]
        if node[0] == 'bound':
            return context[-int(node[1]) - 1]
        if node[0] == 'const':
            return node[1]
        head, args = applied(nodes, root)
        if head[0] == 'const':
            return (head[1], *(named(nodes, arg, context) for arg in args))
        return tuple(node)

    def guard(nodes, root, context):
        head, args = applied(nodes, root)
        if head[:2] != ['const', 'Bool.and'] or len(args) != 2 or named(nodes, args[0], context) != 'deterministic':
            raise ValueError('dispatch guard lost actual classifier result')
        head, args = applied(nodes, args[1])
        if (head[:2] != ['const', 'BEq.beq'] or len(args) != 4 or
                named(nodes, args[-2], context) != ('Compiler.Extraction.Cache.Item.kind',
                    (INTERNER + 'Request.item', 'request'))):
            raise ValueError('dispatch guard lost actual request kind')
        head, args = applied(nodes, args[-1])
        if head[:2] != ['const', 'OfNat.ofNat'] or len(args) != 3 or nodes[args[-2]] != ['natural', '1']:
            raise ValueError('dispatch guard changed operation kind')

    def guard_equality(nodes, root, context, outcome):
        head, args = applied(nodes, root)
        if (head[:2] != ['const', 'Eq'] or len(args) != 3 or
                named(nodes, args[0], context) != 'Bool' or named(nodes, args[-1], context) != 'Bool.' + outcome):
            raise ValueError('dispatch guard changed branch polarity')
        guard(nodes, args[1], context)

    for name, binder in (('miss_step', 'simplifies'), ('invoke_step', 'dispatchCoupled'), ('invoke_direct', 'skipped'),
                         ('invoke_step_verified', 'dispatchCoupled'), ('invoke_direct_verified', 'skipped')):
        statement = next(row['statement'] for row in rows if row['theorem'] == NS + name)
        nodes, entries = domains(statement)
        root, context = entries[binder]
        direct = name.startswith('invoke_direct')
        if not direct:
            if nodes[root][0] != 'forall':
                raise ValueError('dispatch premise is no longer branch-conditional')
            root = nodes[root][3]
        guard_equality(nodes, root, context, 'false' if direct else 'true')
        if not direct:
            root, context = entries['steps']
            head, args = applied(nodes, root)
            if head[:2] != ['const', NS + 'MissSteps'] or named(nodes, args[-2], context) != 'deterministic':
                raise ValueError('miss suffixes lost actual classifier result')
            guard(nodes, args[-1], context)
        else:
            forbidden = {NS + 'MissSteps', NS + 'MissCompletions',
                         'Compiler.Extraction.Dispatch.Effects.Constructors', 'Compiler.Extraction.Dispatch.Effects.SourceConstructors', 'Compiler.Extraction.Dispatch.Effects.SourceConstructorsAt',
                         'Compiler.Extraction.Associative.ConstructorSound',
                         'Compiler.Extraction.AddressMask.Constructs', 'Compiler.Extraction.ArithmeticShift.Constructs'}
            if any(constants_below(statement, root) & forbidden for root, _ in entries.values()):
                raise ValueError('direct insertion regained child or unused suffix contracts')
            insertion = constants_below(statement, entries['insertion'][0])
            if NS + 'Returns' not in insertion or arguments.ITEM + 'invoke' in insertion:
                raise ValueError('direct insertion lost its local suffix boundary')
        if name != 'miss_step':
            if not {'made', 'room', 'allocated', 'initialized', 'keyed', 'transferred', 'entry', 'facts', 'locals'} <= entries.keys():
                raise ValueError('invocation lost actual prefix or return obligations')
            root, context = entries['classifiedAs']
            head, args = applied(nodes, root)
            rhs, values = applied(nodes, args[-1])
            if head[:2] != ['const', 'Eq'] or rhs[:2] != ['const', 'Except.ok'] or named(nodes, values[-1], context) != 'deterministic':
                raise ValueError('invocation lost classifier binding')
            root, context = entries['missedIf']
            if nodes[root][0] != 'forall' or named(nodes, nodes[root][3], context) != ('Eq', 'Bool', 'deterministic', 'Bool.true'):
                raise ValueError('cache miss lost deterministic guard')
        if name.endswith('_verified'):
            if not {'item', 'valid', 'evaluated', 'insertWords'} <= entries.keys():
                raise ValueError('semantic invocation lost native preparation or requested-word premises')
        if name == 'invoke_step_verified':
            for premise in ('correct', 'addresses', 'shifts', 'publishWords'):
                root, context = entries[premise]
                if nodes[root][0] != 'forall':
                    raise ValueError('semantic branch premise is no longer guarded: ' + premise)
                guard_equality(nodes, nodes[root][3], context, 'true')
        if name == 'invoke_direct_verified' and {'dispatchCoupled', 'correct', 'addresses', 'shifts', 'publishWords'} & entries.keys():
            raise ValueError('direct semantic step regained unused recursive/publication assumptions')
    semantic = next(row['statement'] for row in rows if row['theorem'] == INTERNER + 'miss_safe_branches')
    nodes, entries = domains(semantic)
    for premise in ('simplify', 'publish'):
        root, context = entries[premise]
        if nodes[root][0] != 'forall':
            raise ValueError('logical miss lost its semantic branch guard: ' + premise)
        guard_equality(nodes, nodes[root][3], context, 'true')
    return {'actualClassifierAndOperationGuard': True, 'directInsertionNeedsChildSimulation': False,
            'directInsertionNeedsFailureOrPublicationCompletion': False,
            'bothClassifierResultsPreserveRequestedWord': True,
            'directInsertionNeedsChildWordOrPublicationSemantics': False,
            'directInsertionLocalModelAndFrameRemainPremises': True,
            'allEntryInductionVerified': False}


def audit_statements(rows):
    statement = next(row['statement'] for row in rows if row['theorem'] == NS + 'step_taken_verified')
    if statement.get('encoding') != 'kernelExprDag-v1':
        raise ValueError('unsupported native step statement encoding')
    constants = {node[1] for node in statement['nodes'] if node[0] == 'const'}
    binders = {node[1] for node in statement['nodes'] if node[0] == 'forall'}
    if ({NS + 'MissCompletions', NS + 'MissSteps'} & constants or
            'nativeInsertion' in binders or
            not {'rollbackParent', 'publishedParent', 'laterInsertion', 'inserts', 'insertionModel', 'insertionRepresented', 'insertionPolicy', 'insertionParent', 'laterPolicy', 'laterCandidate',
                 'publishes', 'publicationModel', 'publicationParent',
                 'releaseParent', 'localParent', 'coupled'} <= binders):
        raise ValueError('native step completion premise boundary changed')
    remaining_guards(statement, 'laterInsertion')
    published_parent(statement)
    rollback_parent(statement)
    release_parent_guard(statement, 'world')
    release_parent_guard(next(row['statement'] for row in rows if row['theorem'] == NS + 'CallFrame.publication'), 'before')
    preparation_candidate(statement, 'laterCandidate')
    for name in (NS + 'CallFrame.prepare_native', arguments.OWNED + 'Insertion.Native.prepare_reached'):
        prepared = next(row['statement'] for row in rows if row['theorem'] == name)
        if prepared.get('encoding') != 'kernelExprDag-v1':
            raise ValueError('unsupported reached preparation statement encoding')
        constants = {node[1] for node in prepared['nodes'] if node[0] == 'const'}
        binders = {node[1] for node in prepared['nodes'] if node[0] == 'forall'}
        if ({arguments.OWNED + 'Insertion.Native.CallerInput', arguments.OWNED + 'Caller.Origin'} & constants or
                not {'duplicateCall', 'createCall', 'cloneCall', 'admitted'} <= binders):
            raise ValueError('reached preparation restored an origin or lost actual callback inputs')
    return {'branchComposition': branch_interfaces(rows), 'nativeFrame': frames.audit_statements(rows), 'nativeWords': words.audit_statements(rows),
            'assumedFailureCleanup': False, 'assumedPublicationCompletion': False,
            'publicationUnion': publication_union(), 'refusalUnion': refusal_union(), 'successfulFirstNativeFrameDerived': True,
            'reachedPreparationWithoutRebasedOrigin': True,
            'nativeInsertionRemainsPremise': False,
            'laterNativeFrameAndLocalBindingsRemainPremises': True,
            'successfulSpareNativeFrameDerived': True, 'successfulRelocatedNativeFrameDerived': True,
            'sharedPublishedParentLawExplicit': True, 'relocatedPublicationOomNativeFrameDerived': True,
            'sharedRollbackParentLawExplicit': True, 'firstAndSparePublicationOomNativeFramesDerived': True,
            'assumedLaterInsertionResultAndGraph': False, 'candidateBindsPreparation': True,
            'advancingAllocationStreamCouplingVerified': False,
            'publicationBodyAndMatchingProbeDecisionRemainPremises': True,
            'parentFrameLawsAndProperChildrenRemainPremises': True,
            'releaseParentRequiresSameReachedPrivateOwner': True}


def audit(claims):
    required = {
        NS + 'GraphFrame.locals': {recursion.FACTS + 'cleanup'},
        recursion.FACTS + 'cleanup_post': {recursion.FACTS + 'release',
            arguments.OWNED + 'CleanupPost.handedOff', arguments.OWNED + 'CleanupPost.freed',
            'Compiler.Extraction.Memory.Arguments.Normalization.free_empty',
            'Compiler.Extraction.Memory.Arguments.Normalization.free_valid'},
        NS + 'CallFrame.failure': {recursion.FACTS + 'cleanup_post', arguments.OWNED + 'finish_taken',
            arguments.OWNED + 'CleanupPost.graph', arguments.OWNED + 'CleanupPost.closed'},
        arguments.OWNED + 'Publication.publish_projection': {arguments.OWNED + 'Publication.publish_success',
            arguments.OWNED + 'Publication.publish_oom', INTERNER + 'publish'},
        NS + 'CallFrame.failure_parent': {NS + 'CallFrame.failure', NS + 'CallFrame.release', arguments.OWNED + 'Caller.Origin.detached'},
        NS + 'CallFrame.publication_parent': {NS + 'CallFrame.publication', NS + 'CallFrame.publish_parent', NS + 'CallFrame.release'},
        NS + 'CallFrame.publication': {recursion.FACTS + 'finish_publication',
            arguments.OWNED + 'Publication.publish_projection', arguments.OWNED + 'Caller.GraphCustody.publication',
            arguments.OWNED + 'CleanupPost.handedOff', arguments.OWNED + 'CleanupPost.freed',
            arguments.OWNED + 'CleanupPost.graph', arguments.OWNED + 'CleanupPost.closed'},
        NS + 'miss_step': {INTERNER + 'FindCode.controlMiss', INTERNER + 'FindCode.miss',
            arguments.OWNED + 'finish', NS + 'MissSteps.failure', NS + 'MissCompletions.insertion', NS + 'MissCompletions.publication'},
        NS + 'CallFrame.caller': {NS + 'InputFrame.caller', arguments.OWNED + 'Insertion.Native.CallerInput.item'},
        NS + 'CallFrame.preparation': {arguments.OWNED + 'Caller.GraphCustody.publication',
            recursion.FACTS + 'live', recursion.FACTS + 'unique'},
        arguments.OWNED + 'Insertion.Native.prepare_reached': {arguments.OWNED + 'Insertion.Native.prepare_owned',
            arguments.OWNED + 'Insertion.Native.arguments_retained', arguments.OWNED + 'Publication.Input.frame'},
        NS + 'CallFrame.prepare_native': {NS + 'CallFrame.preparation',
            arguments.OWNED + 'Insertion.Native.prepare_reached', recursion.FACTS + 'frame',
            'Compiler.Extraction.AssemblyClone.NativeFields.Installed.valid'},
        NS + 'Returns.locals': {arguments.ITEM + 'returnWorld', NS + 'FramePost.locals'},
        NS + 'invoke_step': {NS + 'CallFrame.dispatch_at', NS + 'dispatcher_snapshot',
            NS + 'CallFrame.caller', NS + 'miss_step', NS + 'Returns.locals', arguments.ITEM + 'invoke_after_take'},
        NS + 'invoke_direct': {NS + 'invoke_step', INTERNER + 'FindCode.miss'},
        NS + 'invoke_step_verified': {NS + 'invoke_step', NS + 'step', NS + 'invoke_step_verified_cursor',
            INTERNER + 'makeKey_sound', 'Compiler.Extraction.InsertionSort.normalize_word',
            'Compiler.Extraction.Dispatch.default_key_simplify_safe'},
        NS + 'invoke_direct_verified': {NS + 'invoke_step_verified', INTERNER + 'FindCode.miss'},
        NS + 'step_taken_verified': {NS + 'invoke_step_verified', NS + 'invoke_step', NS + 'step', NS + 'GraphFrame.locals',
            NS + 'insertion_model',
            NS + 'CallFrame.failure', NS + 'CallFrame.publication', arguments.OWNED + 'Caller.Origin.detached',
            NS + 'invoke_step_verified_cursor', INTERNER + 'makeKey_sound',
            'Compiler.Extraction.InsertionSort.normalize_word', 'Compiler.Extraction.Dispatch.default_key_simplify_safe'},
        INTERNER + 'miss_safe_branches': {INTERNER + 'Safe.bind', INTERNER + 'Safe.pure'},
        INTERNER + 'miss_safe_at': {INTERNER + 'miss_safe_branches'},
        INTERNER + 'miss_safe': {INTERNER + 'miss_safe_at'},
    }
    required.update(frames.dependencies())
    required.update(words.dependencies())
    required[NS + 'invoke_step_verified'] |= {NS + 'MissSteps.words', NS + 'invoke_step_verified_cursor'}
    required[NS + 'miss_step'] |= {NS + name for name in ('miss_frame', 'MissSteps.frames', 'Returns.of_framePost')}
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError('native step lost dependencies: ' + name + ': ' + ', '.join(sorted(missing)))
        fixtures = {dependency for dependency in claims[name]
                    if any(part.endswith('Tests') for part in dependency.split('.'))}
        if fixtures:
            raise ValueError('native step depends on fixtures: ' + name + ': ' + ', '.join(sorted(fixtures)))
    return {'checkedDependencies': sorted(required), 'conditionalTakenStepVerified': True,
            'scope': 'both taken classifier results retain frame, closed locals, exact result/graph and requested word under guarded proper-child and local suffix contracts; direct insertion needs no child or publication semantics; deterministic native step derives its existing suffixes and specializes the shared semantic result',
            'reachedSimplifierFailureCleanupVerified': True,
            'reachedPublicationCompletionVerified': True,
            'reachedSuccessfulPreparationVerified': True,
            'reachedCapacityAndPreparationOomModelConnection': True,
            'remainingLocalObligations': ['native frame outside capacity/preparation OOM, first/no-remap backing OOM and first/spare/no-remap publication success or refusal', 'insertion callback/model binding and reached policy/candidate equations',
                'publication callback body binding', 'parent prefix/insertion/publication/release/return frames',
                'whole-invocation allocation coupling', 'proper-child simulation and word contracts'],
            'allEntryPrefixesVerified': False, 'recursiveInductionVerified': False,
            'composedProductionTheoremVerified': False}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / (name + '.lean')).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)

    return (
        ('step', source('InternerNativeStep'), (
            ('rewind-observed-child-cursor', '(projectionAt (cursorGraph cursor) (CallFrame',
             '(projectionAt (cursorGraph (fun _ => cursor taken.world)) (CallFrame', 3),
            ('rewind-observed-word-result',
             'FramePost frame actual ∧\n      Semantic.Ensures (Dispatch.wordDispatchMeaning env other) before.graph actual.1 actual.2.world.graph',
             'FramePost frame actual ∧\n      Semantic.Ensures (Dispatch.wordDispatchMeaning env other) before.graph actual.1 before.graph', 1),
            ('rewind-child-observer', '(projectionAt observe (CallFrame',
             '(projectionAt (fun _ => observe taken.world) (CallFrame', 2),
            ('incorrect-dispatch-guard',
             '(dispatchCoupled : (deterministic && (request.item.kind == 1)) = true →',
             '(dispatchCoupled : (deterministic && (request.item.kind == 2)) = true →', 5),
            ('incorrect-child-word-guard',
             '(correct : (deterministic && (request.item.kind == 1)) = true →',
             '(correct : (deterministic && (request.item.kind == 1)) = false →', 3),
            ('incorrect-address-word-guard',
             '(addresses : (deterministic && (request.item.kind == 1)) = true →',
             '(addresses : (deterministic && (request.item.kind == 1)) = false →', 3),
            ('incorrect-shift-word-guard',
             '(shifts : (deterministic && (request.item.kind == 1)) = true →',
             '(shifts : (deterministic && (request.item.kind == 1)) = false →', 3),
            ('incorrect-publication-word-guard',
             '(publishWords : (deterministic && (request.item.kind == 1)) = true →',
             '(publishWords : (deterministic && (request.item.kind == 1)) = false →', 1),
            ('wrong-word-insertion-classifier',
             '(modelSeed.insert key deterministic) heap', '(modelSeed.insert key (!deterministic)) heap', 2),
            ('incorrect-simplifier-guard',
             '(simplifies : (deterministic && (request.item.kind == 1)) = true →',
             '(simplifies : (deterministic && (request.item.kind == 1)) = false →', 1),
            ('incorrect-failure-guard', '  failure : simplifying = true →', '  failure : simplifying = false →', 1),
            ('incorrect-publication-guard', '  publication : simplifying = true →', '  publication : simplifying = false →', 1),
            ('force-classifier-true',
             '(classifiedAs : base.queries.deterministic request.item = .ok deterministic)',
             '(classifiedAs : base.queries.deterministic request.item = .ok true)', 7),
            ('skip-deterministic-cache-check',
             '(missedIf : deterministic = true → constructed.graph.table key = none)',
             '(missedIf : deterministic = false → constructed.graph.table key = none)', 7),
            ('force-model-deterministic',
             'let logical := Interner.findCode.miss model request key deterministic taken.world.graph',
             'let logical := Interner.findCode.miss model request key true taken.world.graph', 2),
            ('allow-direct-simplification',
             '(skipped : (deterministic && (request.item.kind == 1)) = false)',
             '(skipped : (deterministic && (request.item.kind == 1)) = true)', 2),
            ('flip-direct-insertion-flag', 'let logical := modelSeed.insert key deterministic world.graph',
             'let logical := modelSeed.insert key (!deterministic) world.graph', 2),
            ('rewind-direct-model', 'let logical := modelSeed.insert key deterministic taken.world.graph',
             'let logical := modelSeed.insert key deterministic before.graph', 2),
            ('exclude-later-insertion', '¬ Insertion.Native.PreparationOOM', 'Insertion.Native.PreparationOOM', 5),
            ('omit-backing-exclusion', '¬ Insertion.Native.BackingAllocationOOM', 'Insertion.Native.BackingAllocationOOM', 1),
            ('omit-publication-exclusion', '¬ Insertion.Native.PublishedObservation', 'Insertion.Native.PublishedObservation', 1),
            ('omit-rollback-exclusion', '¬ Insertion.Native.RefusedObservation', 'Insertion.Native.RefusedObservation', 1),
            ('rewind-insertion-policy', 'normalized world.memory (succeeds key world.graph))',
             'normalized before.memory (succeeds key world.graph))', 1),
            ('rewind-insertion', 'steps.insertion middle checked.1', 'steps.insertion before initial', 1),
            ('rewind-publication', 'steps.publication branch middle id checked.1', 'steps.publication branch before id initial', 1),
            ('rewind-child-failure', 'steps.failure branch middle fault checked.1', 'steps.failure branch before fault initial', 1),
            ('failure-undetached-lookup', '(detached : lookup.owned = none) (fault : Fault)',
             '(detached : True) (fault : Fault)', 1),
            ('failure-discard-parent', 'reached ▸ parentKept', 'True.intro', 1),
            ('failure-change-result',
             '⟨world, ⟨some lookup, some normalized, false⟩⟩) (.error fault) world.graph := by',
             '⟨world, ⟨some lookup, some normalized, false⟩⟩) (.error (.language .outOfMemory)) world.graph := by', 2),
            ('omit-parent-item',
             '(coupled : (projection (CallFrame safety base.allocator owner rows source request.arguments normalized\n      address (input request.item debug) parent)).SourceConstructorsAt (Nested.storageReads rows) debug children modelChildren)',
             '(coupled : (projection (InputFrame safety base.allocator owner rows source request.arguments normalized)).SourceConstructorsAt (Nested.storageReads rows) debug children modelChildren)', 1),
            ('invent-final-word',
             'Semantic.Ensures (Dispatch.wordDispatchMeaning env other) before.graph actual.1 actual.2.world.graph\n        (fun id after => after.read id = some expected) ∧',
             'Semantic.Ensures (Dispatch.wordDispatchMeaning env other) before.graph actual.1 actual.2.world.graph\n        (fun id after => after.read id = some (expected + 1)) ∧', 3),
            ('rewind-final-graph', 'ran.2.graph = logical.2 ∧', 'ran.2.graph = before.graph ∧', 3),
            ('publication-undetached-lookup', '(detached : lookup.owned = none) (aligned : key.arguments = normalized.items)',
             '(detached : True) (aligned : key.arguments = normalized.items)', 2),
            ('publication-opposite-decision',
             '(matched : model.publish key id world.graph =\n      Interner.publish (hostProbe key (Publication.forget world.memory)).1 key id world.graph)',
             '(matched : model.publish key id world.graph =\n      Interner.publish (!(hostProbe key (Publication.forget world.memory)).1) key id world.graph)', 2),
            ('publication-rewind-parent', 'using publicationParent', 'using frame.parent', 1),
            ('publication-rewind-graph', 'post.graph.trans graphEqual', 'post.graph', 1),
            ('preparation-wrong-clone-input',
             '(cloneCall : AssemblyClone.Physical.run (Insertion.observe ops.copy) allocator native allocated',
             '(cloneCall : AssemblyClone.Physical.run (Insertion.observe ops.copy) allocator copied allocated', 1),
            ('preparation-rewind-native-memory',
             'NativeGraph.Facts safety allocator owner data capacity { world with memory := installed } (rows ++ added) := by',
             'NativeGraph.Facts safety allocator owner data capacity world (rows ++ added) := by', 1),
        )),
        ('frames', source('InternerNativeFrames'), (
            ('live-container-at-return-mark', '(ownerOlder : owner < itemMark)', '(ownerOlder : owner ≤ itemMark)', 1),
            ('discard-parent-frame', 'localParent world frame.2', 'localParent world True.intro', 1),
        )),
        ('publication', source('InternerPublicationSuccess'), (
            ('hide-probe-oom', 'let logical := Interner.publish accepted key id before.graph',
             'let logical := Interner.publish true key id before.graph', 1),
            ('wrong-published-id', 'let logical := Interner.publish accepted key id before.graph',
             'let logical := Interner.publish accepted key (id + 1) before.graph', 1),
        )),
        ('cleanup', source('InternerNativeGraphCleanup'), (
            ('alias-key-owner', '(fun address => owned.items ≠ [] ∧ address = owned.address)',
             '(fun _ => False)', 1),
            ('alias-representative-operand', 'row.arguments ≠ [] → owned.address ≠ row.argumentsAddress',
             'row.arguments ≠ [] → True', 1),
            ('lose-key-table',
             '    Facts safety allocator owner data capacity after.world rows ∧\n      after.world.memory.effects.keys = before.world.memory.effects.keys := by',
             '    Facts safety allocator owner data capacity after.world rows ∧\n      after.world.memory.effects.keys = (fun _ => none) := by', 1),
        )),
        ('word', source('InternerProofs'), (
            ('incorrect-publication-guard',
             '(publish : (deterministic && (request.item.kind == 1)) = true →',
             '(publish : (deterministic && (request.item.kind == 1)) = false →', 1),
            ('skip-simplifier-value', 'have actual := fact id rfl', 'have actual : middle.read id = some value := by exact True.intro', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    records = []
    for group, text, changes in mutation_cases():
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous native step mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'native-step-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'native-step-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records + frames.controls(output, env, lean) + words.controls(output, env, lean)
