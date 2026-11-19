#!/usr/bin/env python3
"""Connect literal stores to native constructor ownership and recursive return.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
import constructor_item_checks
import recursive_child_checks
import extract_temporary_arguments
import extract_temporary_unary
import extract_rule_ternary

OWNED = constructor_item_checks.OWNED
ITEM = constructor_item_checks.ITEM
ARGUMENTS = ITEM + 'Arguments.'
TESTS = ARGUMENTS + 'Tests.'
CLAIMS = [ARGUMENTS + name for name in ('prepare_storage', 'prepare_success', 'Prepared.retire', 'Prepared.native_apart', 'Prepared.key_apart', 'Prepared.caller_input', 'caller_input',
    'returned_nonempty', 'returned_rejected', 'operation_prepared', 'operation_rejected', 'operation_item_rejected')]
CLAIMS += [TESTS + name for name in ('literal_prefix', 'native_entry', 'complete_route', 'literal_stack', 'complete_contract')]
CLAIMS += [OWNED + name for name in ('TemporaryMemory.allocated_array', 'TemporaryArguments.orderedStores_success',
    'TemporaryArguments.writePair_success', 'TemporaryUnary.writeOne_success', 'TemporaryTernary.writeTriple_success')]
CLAIMS += ['Compiler.Algebraic.Effect.bind_success_phases']


def bindings():
    return {'constructor': constructor_item_checks.bindings(),
            'pairPreparation': extract_temporary_arguments.check(),
            'unaryPreparation': extract_temporary_unary.check(),
            'ternaryPreparation': extract_rule_ternary.check(),
            'scope': 'existing literal allocation/store programs into complete constructor-local item and caller; elements already evaluated',
            'completeCallSiteAndElementEvaluationVerified': False}


def audit(claims):
    required = {
        'Compiler.Algebraic.Effect.bind_success_phases': {'Compiler.Algebraic.Effect.bind'},
        OWNED + 'TemporaryMemory.allocated_array': {'Compiler.ZigAir.Memory.allocate_shape',
            'Compiler.ZigAir.Memory.Heap.RetainsShape'},
        OWNED + 'TemporaryArguments.orderedStores_success': {'Compiler.ZigAir.Memory.Heap.RetainsShape.trans'},
        OWNED + 'TemporaryArguments.writePair_success': {OWNED + 'TemporaryArguments.orderedStores_success',
            'Compiler.ZigAir.Memory.store_retains_shape'},
        OWNED + 'TemporaryUnary.writeOne_success': {OWNED + 'TemporaryArguments.orderedStores_success',
            'Compiler.ZigAir.Memory.store_retains_shape'},
        OWNED + 'TemporaryTernary.writeTriple_success': {'Compiler.Algebraic.Effect.bind_success_phases',
            OWNED + 'TemporaryArguments.writePair_success', OWNED + 'TemporaryUnary.writeOne_success'},
        ARGUMENTS + 'prepare_storage': {OWNED + 'TemporaryMemory.allocated_array',
            OWNED + 'TemporaryArguments.writePair_success', OWNED + 'TemporaryUnary.writeOne_success',
            OWNED + 'TemporaryTernary.writeTriple_success'},
        ARGUMENTS + 'prepare_success': {OWNED + 'TemporaryArguments.prepare_verified',
            OWNED + 'TemporaryUnary.prepare_verified', OWNED + 'TemporaryTernary.prepare_verified', ARGUMENTS + 'prepare_storage'},
        ARGUMENTS + 'Prepared.retire': {ARGUMENTS + 'Prepared.storage', ARGUMENTS + 'Prepared.address',
            'Compiler.ZigAir.Memory.cleanup_lookup_stack'},
        ARGUMENTS + 'Prepared.native_apart': {'Compiler.ZigAir.Memory.valid_lookup', ARGUMENTS + 'Prepared.address'},
        ARGUMENTS + 'Prepared.key_apart': {ARGUMENTS + 'Prepared.native_apart',
            'Compiler.Extraction.Memory.Arguments.Normalization.Valid.injected'},
        ARGUMENTS + 'Prepared.caller_input': {ARGUMENTS + 'Prepared.key_apart', ITEM + 'caller_input'},
        ARGUMENTS + 'caller_input': {ARGUMENTS + 'prepare_success', ARGUMENTS + 'Prepared.caller_input'},
        ARGUMENTS + 'returned_nonempty': {OWNED + 'TemporaryArguments.unwind'},
        ARGUMENTS + 'returned_rejected': {OWNED + 'TemporaryArguments.unwind'},
        ARGUMENTS + 'operation_prepared': {ITEM + 'operation', ARGUMENTS + 'operation'},
        ARGUMENTS + 'operation_rejected': {ARGUMENTS + 'operation'},
        ARGUMENTS + 'operation_item_rejected': {ARGUMENTS + 'operation_prepared', ITEM + 'invoke_rejected', ARGUMENTS + 'returned_rejected'},
        TESTS + 'native_entry': {ARGUMENTS + 'caller_input', TESTS + 'literal_prefix'},
        TESTS + 'complete_route': {ARGUMENTS + 'operation_prepared', ARGUMENTS + 'returned_nonempty'},
        TESTS + 'literal_stack': {ARGUMENTS + 'prepare_storage', TESTS + 'literal_prefix'},
        TESTS + 'complete_contract': {recursive_child_checks.TESTS + 'full_contract', ARGUMENTS + 'prepare_success',
            TESTS + 'native_entry', recursive_child_checks.TESTS + 'complete_contract', ARGUMENTS + 'Prepared.retire',
            OWNED + 'Insertion.Native.CallerGrowingChainTests.GraphFacts.frame'},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError('constructor argument connection lost dependencies: ' + name + ': ' + ', '.join(sorted(missing)))
    return {'checkedDependencies': sorted(required), 'sourceBinding': bindings(),
            'literalContentsAndMapKeySeparationDerived': True,
            'completeConstructorAndRecursiveFailureReturnConnected': True,
            'outerLiteralRetiredAndOlderNativeGraphRebuilt': True,
            'completeCallSiteAndElementEvaluationVerified': False,
            'initialPrefixIsSelectedInsertionContinuations': False,
            'recursiveInductionVerified': False, 'composedProductionTheoremVerified': False}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / name).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        # A reordered initializer should fail at its checked phase boundary,
        # without expanding the complete native store during error reporting.
        phases = ''
        if name == 'InternerConstructorArguments.lean':
            phases = 'attribute [local irreducible] ' + ' '.join(OWNED + phase for phase in
                ('TemporaryArguments.writePair', 'TemporaryUnary.writeOne', 'TemporaryTernary.writeTriple')) + '\n'
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + phases + without_imports(raw)

    forwarding = ('| (.ok source, prepared) => returned values before.memory.memory.nextId\n'
                  '      (ConstructorItem.operation external budget allocator (p source) q source opcode values debug prepared)')
    storage = '''import Compiler.Extraction.InternerViewInput
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.ZigAir.Memory.WordArray
open Compiler.Extraction.Memory.Arguments.Normalization
open OwnedCall OwnedCall.ConstructorItem
example (values : List NodeId) (before after : World Nat) (source : View)
    (ran : Arguments.prepare values before = (.ok source, after)) (nonempty : values ≠ []) :
    ∃ cell, after.memory.memory.heap.lookup source.allocation = some cell ∧
      cell.type = .array values.length word ∧ cell.writable = true ∧ cell.stack = true :=
  Arguments.prepare_storage values before after source ran nonempty
example (values : List NodeId) (before after : World Nat) (source : View)
    (ready : Arguments.Prepared values before source after) (nonempty : values ≠ [])
    (reached : Compiler.ZigAir.Memory.State) (valid : reached.valid = true)
    (frame : reached.heap.lookup source.allocation = after.memory.memory.heap.lookup source.allocation) :
    (Compiler.ZigAir.Memory.cleanup before.memory.memory.nextId reached).heap.lookup source.allocation = none :=
  ready.retire values before after source nonempty reached valid frame
example (source target : View) (selected : Nat) (value : NodeId) (overwrite : Bool)
    (before after : World Nat) (ran : LocalArguments.zigLocal source selected value overwrite before = (.ok target, after)) :
    ∃ cell, after.memory.memory.heap.lookup target.allocation = some cell ∧
      cell.type = .array 2 word ∧ cell.writable = true ∧ cell.stack = true :=
  LocalArguments.prepare_storage source target selected value overwrite before after ran
example (action : Effect Nat Unit Nat) (next : Nat → Effect Nat Unit Nat)
    (before after value : Nat) (ran : Effect.bind action next before = (.ok value, after)) :
    ∃ first middle, action before = (.ok first, middle) ∧ next first middle = (.ok value, after) :=
  Effect.bind_success_phases action next before after value ran
'''
    return (
        ('storage', storage, (
            ('persistent-literal', 'cell.stack = true :=\n  Arguments.prepare_storage',
             'cell.stack = false :=\n  Arguments.prepare_storage', 1),
            ('wrong-literal-extent', '.array values.length word', '.array (values.length + 1) word', 1),
            ('readonly-literal', 'cell.writable = true ∧ cell.stack = true :=\n  Arguments.prepare_storage',
             'cell.writable = false ∧ cell.stack = true :=\n  Arguments.prepare_storage', 1),
            ('stale-cleanup-mark', 'cleanup before.memory.memory.nextId reached',
             'cleanup (after.memory.memory.nextId + 1) reached', 1),
            ('wrong-cleanup-lifetime', 'reached).heap.lookup source.allocation = none',
             'reached).heap.lookup (source.allocation + 1) = none', 1),
            ('lost-source-frame', 'frame : reached.heap.lookup source.allocation = after.memory.memory.heap.lookup source.allocation',
             'frame : reached.heap.lookup source.allocation = before.memory.memory.heap.lookup source.allocation', 1),
            ('local-borrows-source', 'heap.lookup target.allocation = some cell',
             'heap.lookup source.allocation = some cell', 1),
            ('persistent-local', 'cell.stack = true :=\n  LocalArguments.prepare_storage',
             'cell.stack = false :=\n  LocalArguments.prepare_storage', 1),
            ('stale-phase-world', '∧ next first middle =', '∧ next first before =', 1),
        )),
        ('prefix', source('InternerConstructorArguments.lean'), (
            ('pair-order', '| [a, b] => TemporaryArguments.prepare a b', '| [a, b] => TemporaryArguments.prepare b a', 1),
            ('omit-third', '| [a, b, c] => TemporaryTernary.prepare a b c', '| [a, b, c] => TemporaryArguments.prepare a b', 1),
            ('lose-source', forwarding, forwarding.replace('q source opcode', 'q ⟨0, 0, 0⟩ opcode'), 1),
            ('discard-debug', forwarding, forwarding.replace('values debug prepared', 'values (fun _ => .scalar (.int false 32 0)) prepared'), 1),
            ('skip-return', 'else TemporaryArguments.unwind mark ran', 'else (ran.1, ran.2.world)', 1),
            ('erase-parent', 'else TemporaryArguments.unwind mark ran', 'else TemporaryArguments.unwind 0 ran', 1),
        )),
        ('composed', source('InternerConstructorArgumentsTests.lean'), (
            ('wrong-result', '(complete safety).1 = .error (.language .outOfMemory)',
             '(complete safety).1 = .error (.language .capacity)', 1),
            ('retain-literal', '(complete safety).2.memory.memory.heap.lookup rootSource.allocation = none ∧',
             '(complete safety).2.memory.memory.heap.lookup rootSource.allocation ≠ none ∧', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    records = []
    for group, text, changes in mutation_cases():
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous constructor argument mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'constructor-arguments-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'constructor-arguments-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
