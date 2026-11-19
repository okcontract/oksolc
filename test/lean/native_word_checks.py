"""Audit native frame and word composition under observed proper children.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import re

import native_frame_checks as frames
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
from assembly_item_creation_checks import checked_controls

NS, OWNED = frames.NS, frames.OWNED
RECURSIVE = OWNED + 'Recursive.'
CLAIMS = [RECURSIVE + 'safe_at', RECURSIVE + 'ProjectsAt.safe']
CLAIMS += [NS + name for name in ('MissSteps.words', 'miss_words', 'CallFrame.dispatch_verified_cursor', 'invoke_step_verified_cursor')]


def dependencies():
    return {
        RECURSIVE + 'safe_at': {OWNED + 'Semantic.Ensures', 'Compiler.Extraction.Interner.Safe'},
        RECURSIVE + 'ProjectsAt.safe': {RECURSIVE + 'safe_at'},
        NS + 'MissSteps.words': {RECURSIVE + 'safe_at', 'Compiler.Extraction.Interner.Safe.bind', NS + 'MissWords',
                               NS + 'MissSteps.failure', NS + 'MissCompletions.insertion', NS + 'MissCompletions.publication'},
        NS + 'miss_words': {OWNED + 'Semantic.Ensures.extend', 'Compiler.Extraction.Cache.key_stable',
                           NS + 'MissWords.insertion', NS + 'MissWords.publication', NS + 'MissWords.failure'},
        NS + 'CallFrame.dispatch_verified_cursor': {NS + 'CallFrame.dispatch_at', RECURSIVE + 'safe_at',
            'Compiler.Extraction.Dispatch.default_key_simplify_safe', OWNED + 'Semantic.Ensures.cursor_iff'},
        NS + 'invoke_step_verified_cursor': {NS + 'taken_miss_verified_cursor', frames.arguments.ITEM + 'ProtocolTrace.TakenSite.Reached.return_verified', NS + 'CallFrame.dispatch_verified_cursor', NS + 'miss_words',
            'Compiler.Extraction.InsertionSort.normalize_word', 'Compiler.Extraction.Interner.makeKey_sound', frames.arguments.ITEM + 'invoke_after_take'},
    }


def audit_statements(rows):
    import check_native_invocation as interface
    statements = {row['theorem']: row['statement'] for row in rows}
    checked = ('CallFrame.dispatch_verified_cursor', 'invoke_step_verified_cursor')
    for name in checked:
        statement = statements[NS + name]
        domains, conclusion, _ = interface.domains(statement)
        required = {'cursor', 'children', 'modelChildren', 'facts', 'entry', 'privateSource', 'parent', 'kept',
                    'dispatchCoupled', 'valid', 'evaluated', 'correct', 'addresses', 'shifts'}
        if not required <= domains.keys() or 'modelSeed' in domains:
            raise ValueError('observed word step lost local inputs or regained a suffix model')
        observed = frames.projection_observers(statement, *domains['dispatchCoupled'])
        if len(observed) != 1:
            raise ValueError('missing observed child projection')
        root, context = observed[0]
        head, args = interface.applied(statement, root)
        if head[:2] != ['const', RECURSIVE + 'cursorGraph'] or interface.named(statement, args[-1], context) != 'cursor':
            raise ValueError('child projection does not bind the actual resource observer')
        forbidden = {RECURSIVE + 'projection', NS + 'Returns', NS + 'MissSteps', NS + 'FramePost',
                     OWNED + 'Semantic.Ensures', frames.arguments.ITEM + 'invoke'}
        for field, (root, _) in domains.items():
            if forbidden & interface.step.constants_below(statement, root):
                raise ValueError('observed word step assumes raw or final invocation preservation: ' + field)
        if OWNED + 'Semantic.Ensures' not in interface.step.constants_below(statement, conclusion):
            raise ValueError('native word conclusion missing')
        if name == 'invoke_step_verified_cursor':
            if not {'frames', 'suffixWords', 'item', 'classifiedAs', 'missedIf'} <= domains.keys():
                raise ValueError('observed invocation lost actual suffix or prefix obligations')
            if NS + 'FramePost' not in interface.step.constants_below(statement, conclusion):
                raise ValueError('native frame not joined with word preservation')
            root, context = domains['dispatchCoupled']
            guard = interface.named(statement, statement['nodes'][root][3], context)
            for field in ('correct', 'addresses', 'shifts'):
                root, context = domains[field]
                if statement['nodes'][root][0] != 'forall' or interface.named(statement, statement['nodes'][root][3], context) != guard:
                    raise ValueError('child word contract lost source guard: ' + field)
    return {'checkedStatements': [NS + name for name in checked], 'nativeFrameAndWordsJoined': True,
            'rawChildProjectionRequired': False, 'nativeSuffixSemanticsRemainRequired': True,
            'recursiveInductionVerified': False}


def audit_definitions(interfaces):
    import check_native_invocation as interface
    definition = next(row for row in interfaces if row['name'] == NS + 'MissWords.mk')
    fields, _, _ = interface.domains(definition['type'])
    for name in ('insertion', 'publication', 'failure'):
        root, context = fields[name]
        constants = interface.step.constants_below(definition['type'], root)
        if not {OWNED + 'finish', OWNED + 'Semantic.Ensures', 'Compiler.Extraction.Interner.Invariant'} <= constants:
            raise ValueError('suffix words lost actual completion or invariant: ' + name)
        if {NS + 'Returns', NS + 'MissSteps', frames.arguments.ITEM + 'invoke', RECURSIVE + 'Projects'} & constants:
            raise ValueError('suffix words assume raw correspondence or a whole invocation')
        if name != 'insertion':
            guard = definition['type']['nodes'][root][3]
            head, args = interface.applied(definition['type'], guard)
            if (head[:2] != ['const', 'Eq'] or interface.named(definition['type'], args[-2], context) != 'simplifying'
                    or interface.named(definition['type'], args[-1], context) != 'Bool.true'):
                raise ValueError('suffix words lost source simplification guard: ' + name)
    return {'checkedDefinitions': [NS + 'MissWords.mk'], 'actualCompletedSuffixes': True, 'finalInvocationAssumed': False}


def mutation_cases():
    source = 'import Compiler.Extraction.InternerNativeStep\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n'
    source += without_imports((ROOT / 'lean/Compiler/Extraction/InternerNativeMissWords.lean').read_text())
    for name in ('MissWords', 'miss_words'):
        source = re.sub(r'\b' + name + r'\b', name + 'Mutation', source)
    changes = [
        ('wrong-insertion-flag', 'p.insert key slice deterministic', 'p.insert key slice (!deterministic)', 1),
        ('wrong-publication-guard', 'publication : simplifying = true →', 'publication : simplifying = false →', 1),
        ('wrong-failure-guard', 'failure : simplifying = true →', 'failure : simplifying = false →', 1),
        ('wrong-child-frame-guard', '(childFrame : (deterministic && (request.item.kind == 1)) = true →',
         '(childFrame : (deterministic && (request.item.kind == 1)) = false →', 1),
        ('wrong-child-word-guard', '(childWords : (deterministic && (request.item.kind == 1)) = true →',
         '(childWords : (deterministic && (request.item.kind == 1)) = false →', 1),
        ('rewind-child-words', 'before.graph (p.simplify key slice before).1 (p.simplify key slice before).2.graph',
         'before.graph (p.simplify key slice before).1 before.graph', 1),
        ('wrong-entry-word', '(evaluated : key.eval meaning before.graph.read = some expected)',
         '(evaluated : key.eval meaning before.graph.read = some (expected + 1))', 1),
        ('rewind-key-stability', 'semantic.2.1 key expected evaluated', '(fun _ _ found => found) key expected evaluated', 1),
        ('invent-result-word', 'Semantic.Ensures meaning before.graph actual.1 actual.2.world.graph (fun id after => after.read id = some expected) := by',
         'Semantic.Ensures meaning before.graph actual.1 actual.2.world.graph (fun id after => after.read id = some (expected + 1)) := by', 1),
    ]
    return source, changes


def controls(output, env, lean):
    source, changes = mutation_cases()
    records = checked_controls(output, [mutation_check(output, 'native-word-unchanged', source, True, env, lean)])
    for name, before, after, count in changes:
        if source.count(before) != count:
            raise ValueError('ambiguous native word mutation: ' + name)
        records += checked_controls(output, [mutation_check(output, 'native-word-' + name,
            source.replace(before, after), False, env, lean)])
    source, changes = transfer_mutations()
    records += checked_controls(output, [mutation_check(output, 'native-word-transfer-unchanged', source, True, env, lean)])
    for name, before, after in changes:
        if source.count(before) != 1:
            raise ValueError('ambiguous word transfer mutation: ' + name)
        records += checked_controls(output, [mutation_check(output, 'native-word-transfer-' + name,
            source.replace(before, after), False, env, lean)])
    return records


def transfer_mutations():
    raw = (ROOT / 'lean/Compiler/Extraction/InternerPhysicalDispatchPreservation.lean').read_text()
    raw = raw[raw.index('theorem safe_at '):raw.index('theorem ProjectsAt.safe ')]
    source = 'import Compiler.Extraction.InternerNativeStep\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n'
    source += 'namespace ' + RECURSIVE[:-1] + '\nopen Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul\n'
    source += raw.replace('theorem safe_at ', 'theorem safe_atMutation ') + '\nend ' + RECURSIVE[:-1] + '\n'
    return source, (
        ('wrong-model-input', 'result = (logical before).1.mapError Fault.language', 'result = (logical after).1.mapError Fault.language'),
        ('rewind-result-graph', 'after = (logical before).2', 'before = (logical before).2'),
        ('admit-rejection', 'ordinary result = true → result', 'ordinary result = false → result'),
    )
