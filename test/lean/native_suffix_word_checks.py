"""Audit actual native suffix word preservation and its invocation consumer.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
from assembly_item_creation_checks import checked_controls
from native_word_checks import NS, OWNED, RECURSIVE

INSERTION = OWNED + 'Insertion.Native.'
CLAIMS = [OWNED + name for name in ('deinit_graph', 'cleanup_graph', 'Semantic.Ensures.finish', 'Semantic.publish_return_safe_at')]
CLAIMS += [INSERTION + name for name in ('insert_ordinary_execution', 'insert_replayed_ensures')]
CLAIMS += [NS + name for name in ('native_miss_words', 'invoke_step_native_verified')]


def audit(rows, interfaces):
    import check_native_invocation as gate
    claims = {row['theorem']: row for row in rows}
    required = {
        OWNED + 'cleanup_graph': {OWNED + 'deinit_graph', OWNED + 'cleanup'},
        OWNED + 'Semantic.Ensures.finish': {OWNED + 'cleanup_graph', OWNED + 'finish'},
        INSERTION + 'insert_ordinary_execution': {INSERTION + 'checkedExecution_read', INSERTION + 'execution', OWNED + 'ordinary'},
        INSERTION + 'insert_replayed_ensures': {INSERTION + 'insert_ordinary_execution', INSERTION + 'insert_replayed_verified', INSERTION + 'CandidateWords'},
        NS + 'native_miss_words': {INSERTION + 'candidate_words', INSERTION + 'insert_replayed_ensures', OWNED + 'Publication.publish_projection',
            'Compiler.Extraction.Interner.publish_safe', RECURSIVE + 'safe_at', OWNED + 'Semantic.publish_return_safe_at',
            OWNED + 'Semantic.Ensures.finish', OWNED + 'Semantic.Ensures.error'},
        NS + 'invoke_step_native_verified': {NS + 'native_miss_words', NS + 'invoke_step_verified_cursor'},
    }
    for name, needed in required.items():
        if missing := needed - set(claims[name]['dependencies']):
            raise ValueError('native suffix lost shared proof: ' + name + ': ' + ', '.join(sorted(missing)))
    for name in CLAIMS:
        if any(part.endswith('Tests') for dep in claims[name]['dependencies'] for part in dep.split('.')):
            raise ValueError('native suffix depends on a fixture: ' + name)
    statement = claims[NS + 'invoke_step_native_verified']['statement']
    fields, conclusion, _ = gate.domains(statement)
    if not {'ops', 'allocate', 'growth', 'pushes', 'cursor', 'dispatchCoupled', 'frames', 'item',
            'valid', 'evaluated', 'classifiedAs', 'missedIf', 'facts', 'entry'} <= fields.keys():
        raise ValueError('native invocation lost actual inputs or remaining local obligations')
    forbidden = {INSERTION + 'CandidateWords', NS + 'MissWords', NS + 'MissSteps', NS + 'Returns', NS + 'FramePost',
                 OWNED + 'Semantic.Ensures', RECURSIVE + 'projection', gate.ITEM + 'invoke'}
    for name, (root, _) in fields.items():
        if forbidden & gate.step.constants_below(statement, root):
            raise ValueError('native invocation assumes suffix or final preservation: ' + name)
    if {'modelSeed', 'suffixWords', 'candidate'} & fields.keys():
        raise ValueError('native invocation regained an abstract suffix model')
    result = statement['root']
    while statement['nodes'][result][0] == 'forall':
        result = statement['nodes'][result][4]
    if not {NS + 'FramePost', OWNED + 'Semantic.Ensures', gate.ITEM + 'invoke', NS + 'callerContext'} <= gate.step.constants_below(statement, result):
        raise ValueError('native invocation lost actual callback binding or result')
    observations = gate.step.frames.projection_observers(statement, *fields['dispatchCoupled'])
    if len(observations) != 1:
        raise ValueError('native invocation lost proper-child observation')
    root, context = observations[0]
    head, args = gate.applied(statement, root)
    if head[:2] != ['const', RECURSIVE + 'cursorGraph'] or gate.named(statement, args[-1], context) != 'cursor':
        raise ValueError('native invocation changed the proper-child cursor')
    root, context = fields['dispatchCoupled']
    guard = gate.named(statement, statement['nodes'][root][3], context)
    for name in ('correct', 'addresses', 'shifts'):
        root, context = fields[name]
        if statement['nodes'][root][0] != 'forall' or gate.named(statement, statement['nodes'][root][3], context) != guard:
            raise ValueError('native child contract lost source guard: ' + name)
    fields, _, _ = gate.domains(claims[INSERTION + 'insert_replayed_ensures']['statement'])
    if {'completed', 'executed', 'outcome'} & fields.keys():
        raise ValueError('native insertion assumes successful execution')
    definition = next(row for row in interfaces if row['name'] == INSERTION + 'CandidateWords')
    value = definition['value']
    constants = gate.step.constants_below(value, value['root'])
    needed = {INSERTION + 'execution', INSERTION + 'recordExecution', OWNED + 'Insertion.cell',
              'Compiler.Extraction.Cache.KeyCode.run', 'Compiler.Extraction.Storage.Cell.value', 'Except.ok'}
    if not needed <= constants or {OWNED + 'Semantic.Ensures', NS + 'FramePost', 'Compiler.Extraction.Interner.Invariant'} & constants:
        raise ValueError('candidate fields lost actual execution binding or assume preservation')
    audit_candidate(value, gate)
    return {'checkedDependencies': sorted(required), 'checkedDefinitions': [definition['name']],
            'nativeSuffixSemanticsDerived': True, 'successfulExecutionAssumed': False,
            'candidateFieldCorrespondenceRequired': False, 'pushInterpretationLawRequired': True, 'nativeFrameLawsRequired': True,
            'recursiveInductionVerified': False, 'composedProductionTheoremVerified': False}


def audit_candidate(value, gate):
    fields, body, context = gate.domains(value)
    expected = ['σ', 'ops', 'allocate', 'safety', 'allocator', 'owner', 'source', 'address',
                'meaning', 'input', 'key', 'slice', 'deterministic', 'rows', 'before', 'growth']
    head, clauses = gate.applied(value, body)
    if head[:2] != ['const', 'And'] or len(clauses) != 2:
        raise ValueError('candidate obligation is not a key/value conjunction')
    def equality(root):
        head, args = gate.applied(value, root)
        if head[:2] != ['const', 'Eq'] or len(args) != 3:
            raise ValueError('candidate obligation lost equality')
        return args[-2:]
    key, key_result = equality(clauses[0])
    head, args = gate.applied(value, key)
    if head[:2] != ['const', 'Compiler.Extraction.Cache.KeyCode.run'] or [gate.named(value, x, context) for x in args] != [
        'Compiler.Extraction.Cache.keyCode', *[('app', 'Compiler.Extraction.Storage.Cell.' + name, 'candidate')
                                             for name in ('item', 'arguments', 'sequence')]]:
        raise ValueError('candidate key does not use actual recorded fields')
    head, args = gate.applied(value, key_result)
    word, expected_word = equality(clauses[1])
    if (head[:2] != ['const', 'Option.some'] or gate.named(value, args[-1], context) != 'key'
            or gate.named(value, word, context) != ('app', 'Compiler.Extraction.Storage.Cell.value', 'candidate')
            or gate.named(value, expected_word, context) != 'expected'):
        raise ValueError('candidate obligation changed the requested key or word')
    guard = [field for name, field in fields.items() if name not in expected + ['expected', 'outcome']]
    if len(guard) != 1:
        raise ValueError('candidate obligation changed its execution guard')
    (root, guard_context), = guard
    ran, accepted = equality(root)
    for _ in range(2):
        head, args = gate.applied(value, ran)
        if head[:2] != ['const', 'Prod.fst']:
            raise ValueError('candidate guard lost the actual native execution result')
        ran = args[-1]
    head, args = gate.applied(value, ran)
    if head[:2] != ['const', INSERTION + 'execution'] or [gate.named(value, x, guard_context) for x in args] != expected:
        raise ValueError('candidate guard changed native execution inputs')
    head, args = gate.applied(value, accepted)
    if head[:2] != ['const', 'Except.ok'] or gate.named(value, args[-1], guard_context) != 'outcome':
        raise ValueError('candidate guard excludes ordinary internal outcomes')


def mutation_cases():
    raw = (ROOT / 'lean/Compiler/Extraction/InternerNativeSuffixWords.lean').read_text()
    imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
    source = imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)
    changes = (
        ('wrong-push-kind', 'meaning.atom 2#32 value sequence values', 'meaning.atom 3#32 value sequence values'),
        ('wrong-push-guard', '(pushes : request.item.kind = 2#32 →', '(pushes : request.item.kind = 1#32 →'),
        ('wrong-candidate-key', 'candidate.sequence = some key ∧ candidate.value', 'candidate.sequence = none ∧ candidate.value'),
        ('wrong-candidate-value', 'candidate.value = expected\n', 'candidate.value = expected + 1\n'),
        ('admit-native-rejection', 'growth before).1 = true)', 'growth before).1 = false)'),
        ('wrong-representative-rows', '(represented : before.graph.representatives = some rows)', '(represented : before.graph.representatives = some [])'),
        ('wrong-publication-word', 'meaning key slice lookup id world expected actual words', 'meaning key slice lookup id world (expected + 1) actual words'),
        ('wrong-native-result-word', '(fun id after => after.read id = some expected) := by\n  exact invoke_step_verified_cursor',
         '(fun id after => after.read id = some (expected + 1)) := by\n  exact invoke_step_verified_cursor'),
        ('wrong-child-cursor', '(projectionAt (cursorGraph cursor) (CallFrame', '(projectionAt (cursorGraph (fun _ => 0)) (CallFrame'),
        ('wrong-candidate-classifier', 'input key slice deterministic\n        (rows ++ added)',
         'input key slice (!deterministic)\n        (rows ++ added)'),
        ('wrong-native-publication-guard', 'lookup deterministic\n      (deterministic &&', 'lookup deterministic\n      (!deterministic &&'),
        ('invent-cleanup-graph', '(cleanup external allocator before).2.world.graph = before.world.graph',
         '(cleanup external allocator before).2.world.graph = { before.world.graph with allocationCursor := before.world.graph.allocationCursor + 1 }'),
    )
    return source, changes


def controls(output, env, lean):
    source, changes = mutation_cases()
    records = checked_controls(output, [mutation_check(output, 'native-suffix-word-unchanged', source, True, env, lean)])
    for name, before, after in changes:
        count = 2 if name == 'wrong-representative-rows' else 1
        if source.count(before) != count:
            raise ValueError('ambiguous native suffix word mutation: ' + name)
        records += checked_controls(output, [mutation_check(output, 'native-suffix-word-' + name,
            source.replace(before, after), False, env, lean)])
    return records
