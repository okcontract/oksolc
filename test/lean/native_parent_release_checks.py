#!/usr/bin/env python3
"""Audit parent preservation under actual child-private cleanup.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
from assembly_item_creation_checks import checked_controls
import native_step_checks as step
import recursive_child_checks as child

NS = step.NS
CALLER = step.arguments.OWNED + 'Caller.'
NATIVE = step.arguments.OWNED + 'Insertion.Native.'
MEMORY = 'Compiler.Extraction.Memory.Arguments.Normalization.'
CORE = [CALLER + 'Origin.release_frame', NS + 'CallFrame.private_frame', NS + 'CallFrame.release',
        NS + 'CallFrame.failure_parent']
CLAIMS = CORE + [step.recursion.FACTS + 'finish_publication', child.TESTS + 'Call.simplifier_oom',
                NS + 'CallFrame.publication', NS + 'step_taken_verified']
MODULE = 'Compiler.Extraction.InternerNativeParentReleaseProofTests'


def audit(claims):
    required = {
        CORE[0]: {MEMORY + 'free_valid', CALLER + 'Origin.fresh', CALLER + 'Origin.freshNative'},
        CORE[1]: {step.recursion.FACTS + 'frame_private', NATIVE + 'PrivateFrame.allocations',
                  NATIVE + 'PrivateFrame.keys', CALLER + 'Origin.fresh', CALLER + 'Origin.freshNative',
                  step.arguments.OWNED + 'Good.backed',
                  'Compiler.Extraction.AssemblyClone.NativeFields.Represents.frame'},
        CORE[2]: {CORE[0], CORE[1], NATIVE + 'free_private_frame'},
        CORE[3]: {CORE[2], NS + 'CallFrame.failure', CALLER + 'Origin.detached'},
        child.TESTS + 'Call.simplifier_oom': {CORE[0], child.TESTS + 'Call.route',
                                            step.arguments.OWNED + 'finish_taken'},
        step.recursion.FACTS + 'finish_publication': {step.recursion.FACTS + 'publish',
            step.recursion.FACTS + 'cleanup_post', CALLER + 'Custody.apart', CALLER + 'GraphCustody.operands'},
        NS + 'CallFrame.publication': {step.recursion.FACTS + 'finish_publication'},
        NS + 'step_taken_verified': {NS + 'CallFrame.failure', NS + 'CallFrame.publication'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('parent release lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
        if name in CORE and any(any(part.endswith('Tests') for part in dep.split('.')) for dep in claims[name]):
            raise ValueError('general parent release depends on fixtures: ' + name)
    return {'checkedDependencies': sorted(required), 'actualOriginSeparatesParentAllocations': True,
            'privateInsertionCleanupAndReleaseShareParentFrame': True,
            'failedChildCompletionDerivesNativeParentRelease': True,
            'legacySimplifierOomSharesOriginReleaseFrame': True,
            'publicationRefusalDerivesPrivateReleaseGuard': True,
            'releaseOuterAndChildEntryFrameRemainExplicit': True,
            'publicationAndSuccessfulInsertionParentLawsVerified': False,
            'recursiveInductionVerified': False, 'composedProductionTheoremVerified': False}


def audit_statements(rows):
    expected = {
        CORE[0]: {'before', 'world', 'origin', 'valid', 'live'},
        CORE[1]: {'before', 'world', 'origin', 'initial', 'reached', 'projected', 'custody', 'valid', 'frame', 'outer'},
        CORE[2]: {'before', 'world', 'origin', 'initial', 'reached', 'projected', 'custody', 'localOuter'},
        CORE[3]: {'before', 'world', 'origin', 'initial', 'frame', 'releaseOuter'},
    }
    forbidden = {'Compiler.Extraction.Interner.Represented', NS + 'Returns'}
    native_facts = {NS + 'CallFrame', NS + 'InputFrame', NS + 'GraphFrame', step.recursion.FACTS.rstrip('.')}
    for name, wanted in expected.items():
        statement = next(row['statement'] for row in rows if row['theorem'] == name)
        if statement.get('encoding') != 'kernelExprDag-v1':
            raise ValueError('unsupported parent release statement encoding')
        nodes, index, binders = statement['nodes'], statement['root'], set()
        while nodes[index][0] in ('forall', 'let'):
            node = nodes[index]
            if node[0] == 'forall':
                binders.add(node[1])
                constants = step.constants_below(statement, node[3])
                if forbidden & constants:
                    raise ValueError('parent release assumes completed execution or semantic correspondence')
                if node[1] in ('outer', 'localOuter', 'releaseOuter') and native_facts & constants:
                    raise ValueError('outer law hides native parent preservation')
            index = node[4]
        if not wanted <= binders:
            raise ValueError('parent release lost provenance, current custody or separate outer law: ' + name)
    step.release_parent_guard(next(r['statement'] for r in rows if r['theorem'] == NS + 'step_taken_verified'), 'world')
    step.release_parent_guard(next(r['statement'] for r in rows if r['theorem'] == NS + 'CallFrame.publication'), 'before')
    return {'checkedGeneralInterfaces': sorted(expected), 'actualOriginAndReachedWorldSeparate': True,
            'privateOwnerGuardBindsSameBufferAndReachedRows': True, 'noFinalNativeFrameAssumed': True,
            'outerPredicateRemainsSeparate': True}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / (name + '.lean')).read_text()
        return '\n'.join(line for line in raw.splitlines() if line.startswith('import ')) + '\n' + (
            'set_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw))

    installed = '''import Compiler.Extraction.InternerNativeParentRelease
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
example (allocator : Nat) (owned : ArgumentSlice) (rows : List Compiler.Extraction.Storage.Cell)
    (world : World (Publication.Effects Nat)) (key : Key) (id : NodeId)
    (aligned : key.arguments = owned.items) (nonempty : owned.items ≠ [])
    (published : world.memory.effects.keys key = some ⟨owned.address, id⟩) :
    ¬ Caller.GraphCustody allocator owned rows world.memory :=
  fun (custody : Caller.GraphCustody allocator owned rows world.memory) =>
    custody.apart key ⟨owned.address, id⟩ published
    (aligned.symm ▸ nonempty) ⟨nonempty, rfl⟩
'''
    return (
        ('origin', source('InternerCallerReleaseFrame'), (
            ('rebase-origin', 'before.memory.memory.heap.lookup id = some cell →', 'world.memory.memory.heap.lookup id = some cell →', 1),
            ('return-entry-native', 'after.memory.heap.lookup id = world.memory.memory.heap.lookup id',
             'after.memory.heap.lookup id = before.memory.memory.heap.lookup id', 1),
            ('return-entry-registry', 'after.heap id = world.memory.heap id', 'after.heap id = before.memory.heap id', 1),
            ('lose-allocator-effects', 'after.effects = (if owned.items.isEmpty then world.memory.effects else external.free owned world.memory)',
             'after.effects = world.memory.effects', 1),
        )),
        ('parent', source('InternerNativeParentRelease'), (
            ('wrong-current-rows', 'world.graph.representatives = some currentRows',
             'world.graph.representatives = some []', 2),
            ('wrong-owned-buffer', 'Caller.GraphCustody allocator owned currentRows world.memory',
             'Caller.GraphCustody allocator normalized currentRows world.memory', 2),
            ('lose-reached-source', 'source values reached.1.2.1.2', 'source values initial.1.2.1.2', 1),
            ('lose-reached-item', 'reached.2.1.frame', 'initial.2.1.frame', 1),
            ('rebase-source-provenance', 'origin.freshNative _ old originalFound', 'origin.freshNative _ cell found', 1),
            ('lose-outer-release', '(localOuter after freed)', 'reached.parent', 1),
        )),
        ('publication', source('InternerNativeGraphPublicationCleanup'), (
            ('release-published-owner', 'accepted = false → Caller.GraphCustody',
             'accepted = true → Caller.GraphCustody', 1),
            ('stale-private-world', 'Caller.GraphCustody allocator owned rows published.memory',
             'Caller.GraphCustody allocator owned rows after.world.memory', 1),
        )),
        ('guard', source('InternerNativeStep'), (
            ('wrong-release-owner', 'Caller.GraphCustody base.allocator normalized currentRows world.memory',
             'Caller.GraphCustody base.allocator { normalized with address := normalized.address + 1 } currentRows world.memory', 1),
            ('wrong-release-rows', 'Caller.GraphCustody base.allocator normalized currentRows world.memory',
             'Caller.GraphCustody base.allocator normalized [] world.memory', 1),
        )),
        ('legacy', source('InternerRecursiveCallFailureTests'), (
            ('rewind-release-world', 'origin.release_frame (Publication.external ops.arguments) world',
             'origin.release_frame (Publication.external ops.arguments) call.taken.2.world', 1),
            ('lose-child-frame', '(native id cell (origin.memory id cell constructed))',
             '(origin.memory id cell constructed)', 1),
        )),
        ('installed-owner', installed, (
            ('permit-installed-owner', '¬ Caller.GraphCustody allocator owned rows world.memory',
             'Caller.GraphCustody allocator owned rows world.memory', 1),
        )),
    )


def controls(output, env, lean):
    records = []
    for group, source, changes in mutation_cases():
        records += checked_controls(output, [mutation_check(output,
            'parent-release-' + group + '-unchanged', source, True, env, lean)])
        for name, before, after, count in changes:
            if source.count(before) != count:
                raise ValueError('ambiguous parent release control: ' + name)
            records += checked_controls(output, [mutation_check(output,
                'parent-release-' + group + '-' + name, source.replace(before, after), False, env, lean)])
    return records
