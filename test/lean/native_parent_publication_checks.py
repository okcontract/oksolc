#!/usr/bin/env python3
"""Audit derived parent publication, replacement and refused-publication return.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
from assembly_item_creation_checks import checked_controls
import native_step_checks as step

NS = step.NS
OWNED = step.arguments.OWNED
CALLER = OWNED + 'Caller.'
NATIVE = OWNED + 'Insertion.Native.'
FIELDS = 'Compiler.Extraction.AssemblyClone.NativeFields.'
PHYSICAL = 'Compiler.Extraction.OwnedKeys.Physical.'
PUBLICATION = OWNED + 'Publication.'
CORE = [FIELDS + 'Represents.backed', FIELDS + 'Represents.apart_words',
        CALLER + 'Origin.custody_after_publication', CALLER + 'Origin.source_private_after_publication',
        NS + 'CallFrame.publication_completed', NS + 'CallFrame.publish_parent', NS + 'CallFrame.publication_parent']
CLAIMS = CORE + [NATIVE + 'CallerInput.custody_after_growth', NATIVE + 'CallerInput.source_private_after_publication',
                PUBLICATION + 'Tests.replacement_success', PUBLICATION + 'Tests.replacement_oom',
                NS + 'CallFrame.publication', NS + 'step_taken_verified']
MODULE = 'Compiler.Extraction.InternerNativeParentPublicationProofTests'


def audit(claims):
    required = {
        CORE[0]: {'Compiler.Extraction.AssemblyItem.Fields.readTyped_parts',
                  'Compiler.ZigAir.Memory.recordView_parent', 'Compiler.ZigAir.Memory.access_success_region'},
        CORE[1]: {CORE[0], 'Compiler.ZigAir.Memory.acceptsView'},
        CORE[2]: {CALLER + 'Origin.fresh', CALLER + 'Custody.apart'},
        CORE[3]: {CALLER + 'Origin.freshNative', OWNED + 'Good.backed'},
        CORE[4]: {CORE[1], CORE[2], CORE[3], step.recursion.FACTS + 'publication_completed',
                  PUBLICATION + 'completion_held', PHYSICAL + 'Completed.registry_frame', PHYSICAL + 'Completed.frame'},
        CORE[5]: {CORE[4], NS + 'CallFrame.private_frame', PUBLICATION + 'publish_success', PUBLICATION + 'publish_oom'},
        CORE[6]: {CORE[5], NS + 'CallFrame.publication', NS + 'CallFrame.release', CALLER + 'Origin.detached'},
        NATIVE + 'CallerInput.custody_after_growth': {CORE[2]},
        NATIVE + 'CallerInput.source_private_after_publication': {CORE[3]},
        PUBLICATION + 'Tests.replacement_success': {PUBLICATION + 'publish'},
        PUBLICATION + 'Tests.replacement_oom': {PUBLICATION + 'publish'},
        NS + 'CallFrame.publication': {step.recursion.FACTS + 'finish_publication'},
        NS + 'step_taken_verified': {NS + 'CallFrame.publication'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('parent publication lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
        if name in CORE and any(any(part.endswith('Tests') for part in dep.split('.')) for dep in claims[name]):
            raise ValueError('general parent publication depends on fixtures: ' + name)
    return {'checkedDependencies': sorted(required), 'oldKeySeparationFromReachedCustodyAndTypedItemReads': True,
            'newKeySeparationFromOriginalChildProvenance': True, 'existingGrowthAndPrivacyProofsSpecializeGeneralOrigin': True,
            'publicationAndRefusalCleanupComposedForLiveParent': True, 'nativeMapImplementationVerified': False,
            'childEntryFrameAndNextOuterLawsRemainExplicit': True, 'insertionParentLawsVerified': False,
            'allEntryInductionVerified': False, 'composedProductionTheoremVerified': False}


def audit_statements(rows):
    expected = {
        CORE[2]: {'before', 'memory', 'after', 'origin', 'initial', 'current', 'live', 'keys'},
        CORE[3]: {'before', 'current', 'keys', 'origin', 'good', 'privateSource', 'published'},
        CORE[4]: {'origin', 'initial', 'reached', 'projected', 'custody', 'completed', 'outer'},
        CORE[5]: {'origin', 'initial', 'frame', 'aligned', 'publicationOuter'},
        CORE[6]: {'origin', 'initial', 'frame', 'matched', 'publicationOuter', 'releaseOuter'},
    }
    forbidden = {NS + 'Returns', 'Compiler.Extraction.Interner.Represented'}
    native = {NS + 'CallFrame', NS + 'InputFrame', NS + 'GraphFrame', step.recursion.FACTS.rstrip('.')}
    for name, wanted in expected.items():
        statement = next(row['statement'] for row in rows if row['theorem'] == name)
        if statement.get('encoding') != 'kernelExprDag-v1':
            raise ValueError('unsupported parent publication statement encoding')
        nodes, index, binders = statement['nodes'], statement['root'], set()
        while nodes[index][0] in ('forall', 'let'):
            node = nodes[index]
            if node[0] == 'forall':
                binders.add(node[1])
                constants = step.constants_below(statement, node[3])
                if constants & forbidden:
                    raise ValueError('parent publication assumes completed execution or semantic correspondence')
                if node[1] in ('outer', 'publicationOuter', 'releaseOuter') and constants & native:
                    raise ValueError('outer law hides native parent preservation')
            index = node[4]
        if not wanted <= binders:
            raise ValueError('parent publication lost original/reached provenance or actual completion: ' + name)
    statement = next(row['statement'] for row in rows if row['theorem'] == CORE[6])
    step.release_parent_guard(statement, 'reached', 'releaseOuter', 'outer')
    return {'checkedGeneralInterfaces': sorted(expected), 'originalAndReachedWorldsSeparate': True,
            'currentKeyTableIndependentOfOriginal': True, 'noFinalNativeFrameAssumed': True,
            'nextOuterReleaseGuardBindsSamePrivateOwner': True}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / (name + '.lean')).read_text()
        return '\n'.join(line for line in raw.splitlines() if line.startswith('import ')) + '\n' + (
            'set_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw))
    typed = '''import Compiler.Extraction.AssemblyCloneFields
open Compiler.ZigAir.Memory Compiler.Extraction.AssemblyClone.NativeFields
example (state : State) (source : Address) (input : ItemValue)
    (represented : Represents state source input) (id length : Nat) (cell : Allocation)
    (found : state.heap.lookup id = some cell)
    (typed : cell.type = .array length WordArray.word) : source.allocation ≠ id :=
  represented.apart_words id length cell found typed
'''
    return (
        ('fields', source('AssemblyCloneFields'), (
            ('lose-interior-view', 'acceptsView cell.type source.offset viewType = true := by',
             'acceptsView cell.type 0 viewType = true := by', 1),
        )),
        ('typed-boundary', typed, (
            ('permit-word-alias', ': source.allocation ≠ id :=', ': source.allocation = id :=', 1),
            ('exclude-item-allocations', '(typed : cell.type = .array length WordArray.word)',
             '(typed : cell.type = Compiler.Extraction.AssemblyItem.viewType)', 1),
        )),
        ('custody', source('InternerCallerCustody'), (
            ('rebase-origin-live', '(initial : SliceValid allocator before.memory.heap parent)',
             '(initial : SliceValid allocator memory.heap parent)', 1),
            ('rewind-old-key-custody', '(current : Custody allocator parent memory)',
             '(current : Custody allocator parent before.memory)', 1),
            ('publish-parent-owner', 'keys : after.effects.keys = OwnedKeys.store memory.effects.keys key ⟨owned.address, id⟩',
             'keys : after.effects.keys = OwnedKeys.store memory.effects.keys key ⟨parent.address, id⟩', 1),
        )),
        ('source', source('InternerCallerGraphCustody'), (
            ('rebase-source-origin', '(good : Good parent items before)', '(good : Good parent items taken.world)', 2),
            ('rewind-key-privacy', '(privateSource : SourcePrivate parent current)',
             '(privateSource : SourcePrivate parent before.memory.effects.keys)', 1),
            ('publish-source-owner', 'published : keys = OwnedKeys.store current key ⟨owned.address, id⟩',
             'published : keys = OwnedKeys.store current key ⟨parent.allocation, id⟩', 1),
        )),
        ('parent', source('InternerNativeParentPublication'), (
            ('wrong-current-rows', 'world.graph.representatives = some currentRows',
             'world.graph.representatives = some []', 1),
            ('wrong-private-owner', 'Caller.GraphCustody allocator owned currentRows world.memory',
             'Caller.GraphCustody allocator normalized currentRows world.memory', 1),
            ('rebase-parent-owner', 'normalized initial.1.2.2.1', 'normalized reached.1.2.2.1', 1),
            ('rewind-item-content', 'reached.2.1.frame', 'initial.2.1.frame', 1),
            ('lose-old-key-separation', 'parentCustody.apart key old found nonempty',
             'privateOwned.apart key old found nonempty', 1),
            ('lose-source-provenance', 'source values initial.1.2.1 privateSource keys',
             'source values reached.1.2.1 privateSource keys', 1),
            ('lose-outer-update', 'completed publicationOuter', 'completed frame.parent.parent', 1),
        )),
        ('composition', source('InternerNativeStep'), (
            ('rewind-release-world', 'CallFrame.release origin initial held host projected custody',
             'CallFrame.release origin initial frame.parent host projected custody', 1),
            ('rebase-publication-entry', 'CallFrame.publish_parent origin initial frame',
             'CallFrame.publish_parent origin frame.parent frame', 1),
            ('wrong-outer-release-owner', 'Caller.GraphCustody allocator normalized currentRows reached.memory',
             'Caller.GraphCustody allocator parentNormalized currentRows reached.memory', 1),
        )),
        ('replacement', source('InternerPublicationTests'), (
            ('retain-retired-key', '(replacement).2.memory.heap 5 = none',
             '(replacement).2.memory.heap 5 = some ⟨7, .arguments [1, 3]⟩', 1),
            ('retire-old-key-on-oom', '(replacement true).2.memory.heap 5 = some ⟨7, .arguments [1, 3]⟩',
             '(replacement true).2.memory.heap 5 = none', 1),
            ('drop-incoming-on-oom', '(replacement true).2.memory.heap 8 = some ⟨7, .arguments [1, 3]⟩',
             '(replacement true).2.memory.heap 8 = none', 1),
        )),
    )


def controls(output, env, lean):
    records = []
    for group, source, changes in mutation_cases():
        records += checked_controls(output, [mutation_check(output,
            'parent-publication-' + group + '-unchanged', source, True, env, lean)])
        for name, before, after, count in changes:
            if source.count(before) != count:
                raise ValueError('ambiguous parent publication control: ' + name)
            records += checked_controls(output, [mutation_check(output,
                'parent-publication-' + group + '-' + name, source.replace(before, after), False, env, lean)])
    return records
