#!/usr/bin/env python3
"""Check source-bound queries in complete physical interner callers.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import json
import re

from check_word_swap import ROOT
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
import extract_interner_queries as extraction

MODULE = 'Compiler.Extraction.InternerTerminalTests'
QUERY = 'Compiler.Extraction.Interner.Queries.'
BASE = 'Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.'
NS = BASE + 'Query.'
TERMINAL = BASE + 'Terminal.'
CLAIMS = [QUERY + name for name in ('absent_rejected', 'present_execution', 'capacity_exact',
    'validation_exact', 'deterministic_exact', 'assembly_error_ordinary', 'malformed_rejected')]
CLAIMS += [NS + name for name in ('admitted_verified', 'production_verified')]
CLAIMS += [NS + 'Tests.' + name for name in ('graph_valid', 'production_contract', 'found_from_representatives',
    'force_validated', 'invalid_before_normalization', 'assembly_error_cleanup', 'early_assembly_error',
    'malformed_retains_scope', 'absent_rejected', 'deterministic_cache_hit', 'nondeterministic_skips_cache_and_simplifier')]
CLAIMS += [TERMINAL + name for name in ('force_independent', 'find_independent', 'contracts',
    'production_verified', 'force_verified', 'constant_verified')]
CLAIMS += [TERMINAL + 'Tests.' + name for name in ('force_contract', 'force_publishes_without_recursion',
    'force_failure_cleanup', 'constant_contract', 'constant_inserts_without_recursion', 'constant_failure_cleanup',
    'empty_arguments_skip_allocation', 'constant_needs_no_sort_fuel', 'force_sort_cutoff_rejected', 'operation_reaches_poison')]


def binding():
    if extraction.current() != extraction.OUTPUT.read_bytes():
        raise ValueError('interner query extraction is stale')


def audit(output):
    claims = {c['theorem']: set(c['dependencies'])
              for c in json.loads((output / 'audit.json').read_bytes())['claims']}
    required = {
        QUERY + 'validation_exact': {'Compiler.Extraction.Storage.representativeProgram',
                                    'Compiler.Extraction.Storage.representative_correct'},
        QUERY + 'deterministic_exact': {QUERY + 'determinismCode', QUERY + 'Determinism.run', QUERY + 'classification'},
        NS + 'production_verified': {BASE + 'Insertion.production_verified',
            'Compiler.Extraction.Interner.representative_reads_sound', 'Compiler.Extraction.Interner.representativeReads',
            'Compiler.Extraction.Storage.constantProgram', 'Compiler.Extraction.Storage.operationProgram',
            QUERY + 'queries', QUERY + 'admit', QUERY + 'determinismCode', NS + 'admitted_verified'},
        NS + 'Tests.production_contract': {NS + 'production_verified', NS + 'Tests.graph_valid'},
        NS + 'Tests.assembly_error_cleanup': {BASE + 'Caller.invoke', BASE + 'finish', BASE + 'Fault.recoverable',
                                             QUERY + 'determinismCode'},
        TERMINAL + 'production_verified': {BASE + 'Insertion.graph_contracts', BASE + 'Semantic.production_verified',
            'Compiler.Extraction.Interner.ForceCode.controlRun', TERMINAL + 'find_independent', TERMINAL + 'contracts',
            QUERY + 'queries', QUERY + 'admit', NS + 'admitted_verified'},
        TERMINAL + 'constant_verified': {TERMINAL + 'production_verified',
            'Compiler.Extraction.Interner.constructorCode', 'Compiler.Extraction.Interner.ConstructorCode.constantRequest'},
        TERMINAL + 'force_verified': {TERMINAL + 'production_verified', BASE + 'Semantic.force_verified'},
        TERMINAL + 'Tests.force_contract': {TERMINAL + 'force_verified'},
        TERMINAL + 'Tests.constant_contract': {TERMINAL + 'constant_verified'},
    }
    for name, needed in required.items():
        if not needed <= claims[name]:
            raise ValueError('query caller lost checked dependencies: ' + name + ': ' + ', '.join(sorted(needed - claims[name])))
    # force_independent is definitional equality, so elaboration may erase its
    # application. It remains an audited root; the endpoint must use controlRun.
    for name in ('production_verified', 'constant_verified', 'force_verified'):
        forbidden = {BASE + 'Recursive.projection', BASE + 'Recursive.Projects', NS + 'production_verified'}
        if forbidden & claims[TERMINAL + name]:
            raise ValueError('terminal caller regained recursive simulation dependencies: ' + name)
    return {'checkedDependencies': sorted(required), 'sourceBoundCallerQueriesIntegrated': True,
            'representativeReadContractsDerived': True, 'nativeFieldRefinementVerified': False,
            'recursiveConstructorSimulationVerified': False, 'terminalCallersWithoutRecursivePremisesVerified': True}


def controls(output, env, lean):
    directory = ROOT / 'lean/Compiler/Extraction'
    source = 'import Compiler.Extraction.InternerInsertionCallerTests\n' + '\n'.join(
        without_imports((directory / name).read_text()) for name in ('InternerQueryIR.lean',
            'InternerQueryProgram.lean', 'InternerQueries.lean', 'InternerQueryProduction.lean', 'InternerQueryCallerTests.lean',
            'InternerTerminalProduction.lean', 'InternerTerminalTests.lean'))
    records = [mutation_check(output, 'queries-unchanged', source, True, env, lean)]
    originals = [p.read_bytes() for p in (extraction.cache.SOURCE, extraction.cache.SEMANTICS,
                                        extraction.cache.ITEMS, extraction.cache.OPCODES)]
    generated = without_imports(extraction.extract(*originals).decode())
    if source.count(generated) != 1:
        raise ValueError('ambiguous query profile replacement')
    # These variants pass extraction; the actual changed program must fail its
    # semantic theorem, not only a digest comparison or parser admission.
    for name, index, before, after in (
        ('verbatim-guard', 1, 'if (item.item_type == .VerbatimBytecode)', 'if (item.item_type != .VerbatimBytecode)'),
        ('plain-classification', 1, 'if (!item.hasInstruction()) return true;', 'if (!item.hasInstruction()) return false;'),
        ('instruction-kind', 2, 'const should_have_instruction = self.item_type == .Operation;',
            'const should_have_instruction = self.item_type != .Operation;'),
        ('erase-shape-precondition', 2, 'std.debug.assert(should_have_instruction == (self.instruction_value != null));', ''),
        ('opcode-binding', 3, 'BALANCE = 0x31,', 'BALANCE = 0x30,')):
        inputs = list(originals)
        if inputs[index].count(before.encode()) != 1:
            raise ValueError('ambiguous query source mutation: ' + name)
        inputs[index] = inputs[index].replace(before.encode(), after.encode())
        changed = without_imports(extraction.extract(*inputs).decode())
        records.append(mutation_check(output, 'queries-' + name, source.replace(generated, changed), False, env, lean))
    for name, before, after in (
        ('capacity-boundary', '(heap.representatives.getD []).length ≥ 2^32 - 1', '(heap.representatives.getD []).length > 2^32 - 1'),
        ('validation-error', '| .invalidId => .invalidId |', '| .invalidId => .capacity |'),
        ('assembly-error-is-fault', 'deterministic := determinismCode.run',
            'deterministic := fun item => (determinismCode.run item).mapError (fun _ => .safetyFault)'),
        ('missing-projection-admitted', 'if before.world.graph.representatives.isSome then action before', 'if true then action before')):
        if source.count(before) != 1:
            raise ValueError('ambiguous query mutation: ' + name)
        records.append(mutation_check(output, 'queries-' + name, source.replace(before, after), False, env, lean))
    # Keep the guard mutation at its owning equality theorem. A deliberately
    # false guard otherwise cascades through later clients into elaboration
    # limits, which cannot count as a semantic rejection. Full source remains
    # the positive control and the fresh acceptance root.
    terminal_prefix = ('import Compiler.Extraction.InternerQueryProduction\n' +
        without_imports((directory / 'InternerTerminalProduction.lean').read_text()).split('\ntheorem contracts ', 1)[0] +
        '\nend ' + BASE + 'Terminal\n')
    records.append(mutation_check(output, 'queries-terminal-prefix-unchanged', terminal_prefix, True, env, lean))
    for name, before, after in (
        ('terminal-kind-guard', '(terminal : request.item.kind ≠ 1)', '(terminal : request.item.kind ≠ 2)'),
        ('terminal-erased-publication', '{ p with simplify := fun _ _ => pure none }',
            '{ p with simplify := fun _ _ => pure none, publish := fun _ _ _ => pure () }'),
        ('constant-wrong-value', 'input (fun id after => after.read id = some value) := by',
            'input (fun id after => after.read id = some (value + 1)) := by'),
        ('force-equality-required', '(equal : before.graph.read id = some value)', '(equal : True)')):
        candidate = terminal_prefix if name == 'terminal-kind-guard' else source
        if candidate.count(before) != 1:
            raise ValueError('ambiguous terminal caller mutation: ' + name)
        records.append(mutation_check(output, 'queries-' + name, candidate.replace(before, after), False, env, lean))
    for record in records:
        diagnostic = (output / (record['name'] + '.stdout')).read_text()
        if re.search(r'maximum.*(?:recursion|heartbeats)|deep recursion|timeout|unexpected token|unknown identifier|unknown constant|failed to synthesize|Invalid field', diagnostic, re.I):
            raise ValueError('query control hit resource, syntax or elaboration failure: ' + record['name'])
        if not record['expectedAcceptance'] and not re.search(
                r'unsolved goals|Type mismatch|Tactic [^\n]*(?:failed|proved)|Dependent elimination failed|Application type mismatch', diagnostic, re.I):
            raise ValueError('query negative has no semantic proof failure: ' + record['name'])
    return records
