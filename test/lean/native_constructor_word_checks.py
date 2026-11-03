"""Audit derived native suffix words through the complete constructor family.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import check_native_invocation as invocation
from assembly_item_creation_checks import checked_controls
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check

NS, ITEM, OWNED = invocation.NS, invocation.ITEM, invocation.OWNED
MODULE = 'Compiler.Extraction.InternerNativeConstructorWords'
ENTRIES = ('borrowed', 'constant', 'materialize', 'operation', 'local')
CLAIMS = [NS + name for name in ('TakenFramesAt.native', 'EntryFrames.native', 'EntryFrames.native_verified')]
CLAIMS += [NS + 'step_' + entry + '_native_verified' for entry in ENTRIES]


def audit_statements(rows, interfaces):
    from native_constructor_checks import expression
    claims = {row['theorem']: row['statement'] for row in rows}
    definitions = {row['name']: row for row in interfaces}
    for actual, original, names in (
        ('TakenFramesAt', 'TakenObligationsAt', ('coupled', 'frames', 'correct', 'addresses', 'shifts')),
        ('EntryFrames', 'ObservedEntryObligations', ('retained', 'localParent')),
    ):
        new = definitions[NS + actual + '.mk']['type']
        old = definitions[NS + original + '.mk']['type']
        fields, _, _ = invocation.domains(new)
        previous, _, _ = invocation.domains(old)
        removed = {'expected', 'words'} if actual == 'TakenFramesAt' else {'expected'}
        if set(fields) != set(previous) - removed:
            raise ValueError('native frame inputs added a premise or lost an existing field')
        for name in names:
            root, context = fields[name]
            prior, prior_context = previous[name]
            if expression(new, root, context) != expression(old, prior, prior_context):
                raise ValueError('native entry changed the existing child/frame law: ' + actual + '.' + name)
        forbidden = {NS + 'MissWords', OWNED + 'Insertion.Native.CandidateWords',
                     NS + 'TakenObligationsAt', NS + 'ObservedEntryObligations',
                     OWNED + 'Semantic.Ensures', NS + 'InvocationPost', NS + 'ConstructorPost'}
        for name, (root, _) in fields.items():
            if forbidden & invocation.step.constants_below(new, root):
                raise ValueError('native frame input assumes derived semantics: ' + actual + '.' + name)
    # Compare every observation and binder of the reached-entry obligation.
    # Only its final local package changes, removing the expected-word argument.
    new = definitions[NS + 'EntryFrames.mk']['type']
    old = definitions[NS + 'ObservedEntryObligations.mk']['type']
    fields, _, _ = invocation.domains(new)
    previous, _, _ = invocation.domains(old)
    def frame_only(term):
        if not isinstance(term, tuple):
            return term
        if len(term) == 3 and term[0] == 'app' and term[-1] == 'expected':
            head = term[1]
            while isinstance(head, tuple) and head[0] == 'app':
                head = head[1]
            if head == NS + 'TakenObligationsAt':
                return replace_head(term[1])
        return tuple(frame_only(child) for child in term)
    def replace_head(term):
        if isinstance(term, tuple):
            return tuple(replace_head(child) for child in term)
        return NS + 'TakenFramesAt' if term == NS + 'TakenObligationsAt' else term
    if expression(new, *fields['taken']) != frame_only(expression(old, *previous['taken'])):
        raise ValueError('native entry lost an actual reached-prefix observation')
    for name in CLAIMS:
        statement = claims[name]
        fields, conclusion, _ = invocation.domains(statement)
        forbidden = {NS + 'MissWords', OWNED + 'Insertion.Native.CandidateWords',
                     NS + 'TakenObligationsAt', NS + 'ObservedEntryObligations',
                     OWNED + 'Semantic.Ensures', NS + 'InvocationPost', NS + 'ConstructorPost'}
        for field, (root, _) in fields.items():
            if forbidden & invocation.step.constants_below(statement, root):
                raise ValueError('native entry assumes suffix or final semantics: ' + name + '.' + field)
        if name.endswith('_native_verified'):
            required = {'ops', 'allocate', 'growth', 'base', 'children', 'before', 'debug',
                        'facts', 'admitted', 'typed', 'valid', 'obligations'}
            if not required <= fields.keys() or {'cursor', 'modelChildren', 'modelSeed', 'completed', 'initialized'} & fields.keys():
                raise ValueError('native constructor lost actual inputs or assumes a completed prefix')
            root = fields['obligations'][0]
            if not {NS + 'EntryFrames', NS + 'callerContext'} <= invocation.step.constants_below(statement, root):
                raise ValueError('native entry is not bound to the actual callbacks')
            if not {NS + 'ConstructorPost', NS + 'step', NS + 'callerContext'} <= invocation.step.constants_below(statement, conclusion):
                raise ValueError('native constructor lost actual-step attachment')
            if not any(name.endswith('step_' + entry + '_native_verified') for entry in ('constant', 'materialize')) and 'literals' in fields:
                raise ValueError('operation route unexpectedly requires PUSH interpretation')
    return {'checkedNativeEntries': list(ENTRIES), 'unchangedChildAndFrameContracts': True,
            'unchangedReachedEntryObservations': True, 'nativeSuffixWordsDerivedAtAllEntries': True,
            'expectedWordAbsentFromFrameInputs': True, 'nativeFrameLawsRequired': True,
            'completeStreamCorrespondenceVerified': False, 'recursiveInductionVerified': False,
            'composedProductionTheoremVerified': False}


def audit(claims):
    required = {
        'TakenFramesAt.native': {NS + 'native_miss_words', NS + 'TakenObligationsAt'},
        'EntryFrames.native': {NS + 'TakenFramesAt.native', OWNED + 'Insertion.Native.CallerInput.keyed'},
        'EntryFrames.native_verified': {NS + 'EntryFrames.native', NS + 'ObservedEntryObligations.verified'},
    }
    for entry in ENTRIES:
        required['step_' + entry + '_native_verified'] = {NS + 'EntryFrames.native', NS + 'step_' + entry + '_verified_observed'}
    for name, needed in required.items():
        if missing := needed - claims[NS + name]:
            raise ValueError('native constructor lost shared derivation: ' + name + ': ' + ', '.join(sorted(missing)))
        if any(part.endswith('Tests') for dep in claims[NS + name] for part in dep.split('.')):
            raise ValueError('native constructor depends on a fixture: ' + name)
    return {'checkedDependencies': [NS + name for name in required], 'nativeSuffixWordsDerivedAtAllEntries': True,
            'recursiveInductionVerified': False, 'composedProductionTheoremVerified': False}


def mutation_cases():
    raw = (invocation.harness.ROOT / 'lean/Compiler/Extraction/InternerNativeConstructorWords.lean').read_text()
    imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
    source = imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)
    changes = (
        ('wrong-child-guard', 'coupled : (deterministic &&', 'coupled : (!deterministic &&', 1),
        ('rewind-child-cursor', 'TakenObligationsAt cursor safety', 'TakenObligationsAt (fun _ => 0) safety', 1),
        ('wrong-push-guard', 'request.item.kind = 2#32 →', 'request.item.kind = 1#32 →', 3),
        ('wrong-normalized-key', 'keyCode.run request.item normalized.items request.sequence', 'keyCode.run request.item [] request.sequence', 1),
        ('wrong-native-growth', 'base growth usizeBits children debug\n    source address', 'base none usizeBits children debug\n    source address', 1),
        ('wrong-source-observation', 'Caller.initLookup base.external base.budget base.allocator source ⟨', 'Caller.initLookup base.external base.budget base.allocator ⟨0, 0, 0⟩ ⟨', 1),
        ('wrong-borrowed-address', '.borrowedOperation slice.address opcode slice.items debug before)', '.borrowedOperation (slice.address + 1) opcode slice.items debug before)', 1),
        ('wrong-constant-word', '.constant value debug before) value', '.constant value debug before) (value + 1)', 1),
        ('wrong-materialized-word', '.materialize id value debug before) value', '.materialize id value debug before) (value + 1)', 1),
        ('wrong-operation-word', '.operation opcode values debug before) expected', '.operation opcode values debug before) (expected + 1)', 1),
        ('wrong-local-word', '.localOperation opcode slice selected repeated first debug before) expected', '.localOperation opcode slice selected repeated first debug before) (expected + 1)', 1),
        ('wrong-local-observation', 'LocalArguments.zigLocal (view slice) selected repeated first before =', 'LocalArguments.zigLocal (view slice) selected repeated (!first) before =', 1),
        ('wrong-literal-observation', 'Arguments.prepare values before =', 'Arguments.prepare [] before =', 1),
        ('wrong-return-mark', 'cleanup before.memory.memory.nextId world.memory.memory', 'cleanup (before.memory.memory.nextId + 1) world.memory.memory', 2),
    )
    return source, changes


def controls(output, env, lean):
    source, changes = mutation_cases()
    records = checked_controls(output, [mutation_check(output, 'native-entries-unchanged', source, True, env, lean)])
    for name, before, after, count in changes:
        if source.count(before) != count:
            raise ValueError('ambiguous native entry mutation: ' + name)
        records += checked_controls(output, [mutation_check(output, 'native-entries-' + name,
            source.replace(before, after), False, env, lean)])
    return records
