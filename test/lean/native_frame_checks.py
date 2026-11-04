"""Audit native scope/frame preservation under observed proper children.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import re

from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
from assembly_item_creation_checks import checked_controls
import constructor_argument_checks as arguments
import native_recursion_checks as recursion

NS, OWNED = recursion.NS, arguments.OWNED
CLAIMS = [NS + name for name in ('Returns.framePost', 'Returns.of_framePost', 'FramePost.locals',
    'MissSteps.frames', 'miss_frame', 'CallFrame.dispatch_at', 'invoke_step_frame_at')]


def dependencies():
    return {
        NS + 'Returns.framePost': {NS + 'Returns', NS + 'FramePost'},
        NS + 'Returns.of_framePost': {NS + 'Returns', NS + 'FramePost'},
        NS + 'FramePost.locals': {NS + 'FramePost', arguments.ITEM + 'returnWorld'},
        NS + 'MissSteps.frames': {NS + 'Returns.framePost', NS + 'MissFrames'},
        NS + 'miss_frame': {'Compiler.Extraction.Interner.FindCode.controlMiss', OWNED + 'finish',
                           NS + 'MissFrames.insertion', NS + 'MissFrames.publication', NS + 'MissFrames.failure'},
        NS + 'CallFrame.dispatch_at': {NS + 'CallFrame.caller', NS + 'dispatcher_snapshot', NS + 'dispatch_projects_framed_at'},
        NS + 'invoke_step_frame_at': {NS + 'invoke_step_frame', NS + 'source_constructors_keep', NS + 'miss_frame', NS + 'FramePost.locals',
                                     arguments.ITEM + 'invoke_after_take'},
    }


def projection_observers(statement, index, context):
    import check_native_invocation as interface
    node = statement['nodes'][index]
    if node[0] == 'app':
        head, args = interface.applied(statement, index)
        if head[:2] == ['const', OWNED + 'Recursive.projectionAt'] and len(args) == 3:
            return [(args[1], context)]
        return projection_observers(statement, node[1], context) + projection_observers(statement, node[2], context)
    if node[0] in ('forall', 'lambda'):
        return projection_observers(statement, node[3], context) + projection_observers(statement, node[4], context + [node[1]])
    return []


def audit_statements(rows):
    import check_native_invocation as interface
    statements = {row['theorem']: row['statement'] for row in rows}
    for name in ('CallFrame.dispatch_at', 'invoke_step_frame_at'):
        statement = statements[NS + name]
        domains, _, _ = interface.domains(statement)
        required = {'observe', 'children', 'modelChildren', 'facts', 'entry', 'privateSource', 'parent', 'kept', 'dispatchCoupled'}
        if not required <= domains.keys() or 'modelSeed' in domains:
            raise ValueError('observed native frame lost local inputs or regained a suffix model')
        constants = interface.step.constants_below(statement, domains['dispatchCoupled'][0])
        if OWNED + 'Recursive.projectionAt' not in constants or OWNED + 'Recursive.projection' in constants:
            raise ValueError('native frame requires raw child projection')
        root, context = domains['dispatchCoupled']
        observed = [interface.named(statement, index, bound) for index, bound in projection_observers(statement, root, context)]
        if observed != ['observe']:
            raise ValueError('proper-child relation does not use the invocation observer')
        for field, (root, _) in domains.items():
            if {NS + 'FramePost', NS + 'Returns', OWNED + 'Semantic.Ensures', arguments.ITEM + 'invoke'} & interface.step.constants_below(statement, root):
                raise ValueError('native frame assumes its final invocation result: ' + field)
    return {'checkedStatements': [NS + name for name in ('CallFrame.dispatch_at', 'invoke_step_frame_at')],
            'observedChildRelationAccepted': True, 'nativeSuffixAndReturnLawsRemainRequired': True,
            'recursiveInductionVerified': False}


def audit_definitions(interfaces):
    import check_native_invocation as interface
    definitions = {row['name']: row for row in interfaces}
    post = definitions[NS + 'FramePost']
    if post['kind'] != 'definition':
        raise ValueError('native frame post is no longer inspectable')
    domains, body, _ = interface.domains(post['value'])
    guard, context = next(reversed(domains.values()))
    head, args = interface.applied(post['value'], guard)
    if head[:2] != ['const', 'Eq'] or interface.named(post['value'], args[-1], context) != 'Bool.true':
        raise ValueError('native frame lost ordinary-return guard')
    if OWNED + 'ordinary' not in interface.step.constants_below(post['value'], args[-2]):
        raise ValueError('native frame does not guard the actual result')
    if OWNED + 'Closed' not in interface.step.constants_below(post['value'], body):
        raise ValueError('native frame lost scope closure')
    fields, _, _ = interface.domains(definitions[NS + 'MissFrames.mk']['type'])
    forbidden = {NS + 'Returns', OWNED + 'Recursive.Projects', OWNED + 'Recursive.ProjectsAt',
                 'Compiler.Extraction.Interner.Primitives'}
    for name in ('insertion', 'publication', 'failure'):
        constants = interface.step.constants_below(definitions[NS + 'MissFrames.mk']['type'], fields[name][0])
        if not {NS + 'FramePost', OWNED + 'finish'} <= constants or constants & forbidden:
            raise ValueError('native suffix lost actual close or regained logical projection: ' + name)
    return {'checkedDefinitions': [NS + 'FramePost', NS + 'MissFrames.mk'], 'rawLogicalHeapEqualityRequired': False}


def mutation_cases():
    directory = ROOT / 'lean/Compiler/Extraction'
    frames = (directory / 'InternerNativeFrames.lean').read_text()
    frames = frames[frames.index('/-- Native scope and frame preservation'):frames.rindex('\nend ')]
    source = 'import Compiler.Extraction.InternerNativeStep\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n'
    source += 'namespace ' + NS[:-1] + '\nopen Compiler.Algebraic\n' + frames + '\nend ' + NS[:-1] + '\n'
    source += without_imports((directory / 'InternerNativeMissFrame.lean').read_text())
    for name in ('FramePost', 'framePost', 'of_framePost', 'MissFrames', 'miss_frame'):
        source = re.sub(r'\b' + name + r'\b', name + 'Mutation', source)
    mutations = [
        ('admit-rejection', 'ordinary actual.1 = true → Closed', 'ordinary actual.1 = false → Closed', 1),
        ('open-scope', 'ordinary actual.1 = true → Closed', 'ordinary actual.1 = true → ¬Closed', 1),
        ('lost-frame', 'Closed actual.2.scope ∧ frame actual.2.world', 'Closed actual.2.scope ∧ ¬frame actual.2.world', 1),
        ('wrong-retirement-mark', 'world := returnWorld itemMark scratchMark actual.2.world',
         'world := returnWorld scratchMark itemMark actual.2.world', 1),
        ('wrong-insertion-flag', 'p.insert key slice deterministic', 'p.insert key slice (!deterministic)', 1),
        ('wrong-publication-guard', 'publication : simplifying = true →', 'publication : simplifying = false →', 1),
        ('wrong-failure-guard', 'failure : simplifying = true →', 'failure : simplifying = false →', 1),
        ('wrong-child-guard', '(simplifies : (deterministic && (request.item.kind == 1)) = true →',
         '(simplifies : (deterministic && (request.item.kind == 1)) = false →', 1),
        ('rewind-child-frame', '→ ready (p.simplify key slice before).2', '→ ready before', 1),
        ('wrong-insertion-owner', '⟨world, ⟨some lookup, some slice, false⟩⟩',
         '⟨world, ⟨some lookup, some slice, true⟩⟩', 3),
    ]
    return source, mutations


def controls(output, env, lean):
    source, mutations = mutation_cases()
    records = checked_controls(output, [mutation_check(output, 'native-frame-unchanged', source, True, env, lean)])
    for name, before, after, count in mutations:
        if source.count(before) != count:
            raise ValueError('ambiguous native frame mutation: ' + name + ': ' + str(source.count(before)))
        records += checked_controls(output, [mutation_check(output, 'native-frame-' + name,
            source.replace(before, after), False, env, lean)])
    return records
