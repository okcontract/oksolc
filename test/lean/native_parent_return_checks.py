#!/usr/bin/env python3
"""Audit local return under the actual enclosing input and item frame.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
from assembly_item_creation_checks import checked_controls
import native_step_checks as step
import recursive_growth_checks as growth

NS = step.NS
MODULE = 'Compiler.Extraction.InternerNativeParentReturnProofTests'
CORE = [NS + name for name in
        ('InputFrame.cleanup', 'CallFrame.cleanup', 'CallFrame.locals', 'GraphFrame.parent_locals')]
CLAIMS = CORE + [growth.TESTS + 'child_contract']


def audit(claims):
    required = {
        CORE[0]: {step.recursion.FACTS + 'cleanup', step.arguments.OWNED + 'ConstructorFrame.represented_older',
                  'Compiler.ZigAir.Memory.cleanup_lookup_older', 'Compiler.ZigAir.Memory.valid_lookup'},
        CORE[1]: {CORE[0], 'Compiler.Extraction.AssemblyClone.NativeFields.Represents.live',
                  'Compiler.Extraction.AssemblyClone.NativeFields.Represents.frame',
                  'Compiler.ZigAir.Memory.valid_lookup', 'Compiler.ZigAir.Memory.cleanup_lookup_older',
                  step.arguments.OWNED + 'ArraySource.cleanup'},
        CORE[2]: {CORE[1]},
        CORE[3]: {CORE[2], NS + 'GraphFrame.locals'},
        growth.TESTS + 'child_contract': {CORE[1], CORE[2], growth.TESTS + 'child_native',
                                          growth.TESTS + 'parent_input', growth.TESTS + 'child_result'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('parent return lost dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
        if name in CORE and any(any(part.endswith('Tests') for part in dep.split('.')) for dep in claims[name]):
            raise ValueError('general parent return depends on fixtures: ' + name)
    return {'checkedDependencies': sorted(required), 'entryLifetimeBoundsDerived': True,
            'reachedGraphMayGrowAndRelocate': True, 'parentInputAndItemCleanupDerived': True,
            'existingGrowthConsumerSpecializesGeneralReturn': True,
            'arbitraryOuterPredicateLawRemainsExplicit': True,
            'publicationAndReleaseParentLawsVerified': False,
            'recursiveInductionVerified': False, 'composedProductionTheoremVerified': False}


def audit_statements(rows):
    expected = {
        CORE[0]: {'before', 'world', 'initial', 'reached', 'mark', 'ordered'},
        CORE[1]: {'before', 'world', 'initial', 'reached', 'mark', 'ordered', 'outer'},
        CORE[2]: {'before', 'initial', 'itemMark', 'scratchMark', 'itemOrdered', 'scratchOrdered', 'localOuter'},
        CORE[3]: {'before', 'initial', 'itemMark', 'scratchMark', 'itemOrdered', 'ordered', 'localOuter'},
    }
    forbidden = {step.arguments.OWNED + 'Caller.Origin', step.arguments.OWNED + 'Insertion.Native.CallerInput',
                 'Compiler.Extraction.Interner.Represented', NS + 'Returns'}
    for name, wanted in expected.items():
        statement = next(row['statement'] for row in rows if row['theorem'] == name)
        if statement.get('encoding') != 'kernelExprDag-v1':
            raise ValueError('unsupported parent return statement encoding')
        nodes, index, binders = statement['nodes'], statement['root'], set()
        while nodes[index][0] in ('forall', 'let'):
            node = nodes[index]
            if node[0] == 'forall':
                binders.add(node[1])
                constants = step.constants_below(statement, node[3])
                if forbidden & constants or any(any(part.endswith('Tests') for part in value.split('.')) for value in constants):
                    raise ValueError('parent return assumes origin, semantic correspondence or fixture: ' + name)
                if node[1] in ('outer', 'localOuter'):
                    # Only the arbitrary outer predicate may be assumed after
                    # cleanup; input/item/native graph must be derived.
                    if {NS + 'CallFrame', NS + 'InputFrame', NS + 'GraphFrame',
                        step.recursion.FACTS.rstrip('.')} & constants:
                        raise ValueError('outer law hides native parent preservation')
            index = node[4]
        if not wanted <= binders:
            raise ValueError('parent return lost its actual entry/reached world or local marks: ' + name)
    return {'checkedGeneralInterfaces': sorted(expected), 'originalEntryAndReachedFrameSeparate': True,
            'arbitraryAllocatorSafetyViewsAndItems': True, 'noNormalizationOriginRebased': True,
            'outerLawDoesNotAssumeInputItemOrNativeGraph': True}


def mutation_cases():
    raw = (ROOT / 'lean/Compiler/Extraction/InternerNativeParentReturn.lean').read_text()
    source = '\n'.join(line for line in raw.splitlines() if line.startswith('import ')) + '\n'
    source += 'set_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + without_imports(raw)
    fixture = '''import Compiler.Extraction.InternerRecursiveGrowthTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
open ConstructorItem.RecursiveGrowthTests ConstructorItem.RecursiveNonemptyTests
open ConstructorItem.RecursiveTests (debug)
set_option pp.maxSteps 8
set_option pp.deepTerms false
attribute [local irreducible] ConstructorItem.RecursiveTests.Call.address
  ConstructorItem.RecursiveTests.Call.native returnedChild parent
  Compiler.Extraction.AssemblyClone.NativeFields.Represents
example (safety publishOK : Bool) (depth : Nat) : ∃ after,
    (children safety (depth + 1) publishOK).operation 21 [0] debug (parent safety).taken.2.world =
      (.ok 5, returnedChild safety after) ∧
    Compiler.Extraction.AssemblyClone.NativeFields.Represents
      (returnedChild safety after).memory.memory (parent safety).address (parent safety).native := by
  obtain ⟨after, called, _, _, _, _, _, _, _, _, _, item⟩ := child_contract safety depth publishOK
  exact ⟨after, called, item⟩
'''
    return (
        ('general', source, (
            ('unbind-entry-source', 'initial.2.1.2 empty', 'reached.2.1.2 empty', 1),
            ('lose-reached-source', 'source values reached.2.1.2', 'source values initial.2.1.2', 1),
            ('lose-mark-order', 'before.memory.memory.nextId ≤ mark', 'mark ≤ before.memory.memory.nextId', 2),
            ('lose-item-mark', 'before.memory.memory.nextId ≤ itemMark', 'itemMark ≤ before.memory.memory.nextId', 2),
            ('lose-scratch-mark', 'before.memory.memory.nextId ≤ scratchMark', 'scratchMark ≤ before.memory.memory.nextId', 1),
            ('use-entry-item', 'reached.2.1.frame', 'initial.2.1.frame', 1),
            ('rebase-item-entry', 'initial.2.1.live', 'reached.2.1.live', 1),
            ('lose-returned-outer', 'localOuter world reached.parent', 'reached.parent', 1),
            ('rewind-local-history', 'memory := Compiler.ZigAir.Memory.cleanup mark world.memory.memory',
             'memory := Compiler.ZigAir.Memory.cleanup 0 world.memory.memory', 3),
            ('change-normalized-owner', 'source values normalized\n      { world with',
             'source values { normalized with address := normalized.address + 1 }\n      { world with', 1),
        )),
        ('consumer', fixture, (
            ('wrong-result', '(.ok 5, returnedChild safety after)', '(.ok 4, returnedChild safety after)', 1),
            ('wrong-item-offset', 'memory.memory (parent safety).address',
             'memory.memory { (parent safety).address with offset := (parent safety).address.offset + 1 }', 1),
        )),
    )


def controls(output, env, lean):
    records = []
    for group, source, changes in mutation_cases():
        records += checked_controls(output, [mutation_check(output,
            'parent-return-' + group + '-unchanged', source, True, env, lean)])
        for name, before, after, count in changes:
            if source.count(before) != count:
                raise ValueError('ambiguous parent return control: ' + name)
            records += checked_controls(output, [mutation_check(output,
                'parent-return-' + group + '-' + name, source.replace(before, after), False, env, lean)])
    return records
