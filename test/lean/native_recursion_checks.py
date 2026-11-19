#!/usr/bin/env python3
"""Audit one recursive constructor family through publication and child failure.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from check_word_swap import ROOT
import re
from check_zig_air_memory_proofs import without_imports
from check_zig_air_proofs import mutation_check
import constructor_argument_checks as arguments
import recursive_borrowed_checks as borrowed
import view_input_checks as views

NS = arguments.ITEM + 'NativeRecursion.'
TESTS = NS + 'Tests.'
EFFECTS = 'Compiler.Extraction.Dispatch.Effects.'
READS = arguments.OWNED + 'NativeReads.'
FACTS = arguments.OWNED + 'NativeGraph.Facts.'
TIMING = arguments.OWNED + 'Recursive.QueryTiming.'
CLAIMS = [NS + name for name in ('operation_succ', 'borrowed_succ', 'constant_succ',
    'materialize_succ', 'exhausted_rejected', 'zero_entries', 'local_succ', 'zero_local', 'dispatcher_inputs', 'dispatcher_snapshot')]
CLAIMS += [TESTS + name for name in ('child_simplifier', 'child_equivalent', 'parent_continuation',
    'root_equivalent', 'xor_simplifier', 'xor_insertion', 'xor_equivalent', 'program_equivalent',
    'program_contract', 'root_one', 'program_one', 'incomplete_retains_parent',
    'binary_simplifier', 'binary_insertion', 'binary_equivalent')]
CLAIMS += [EFFECTS + name for name in ('alternating_inputs', 'alternating_build_inputs',
    'alternating_search_inputs', 'alternating_with_inputs', 'signextend_with_inputs',
    'shift_product_with_inputs', 'unary_with_inputs', 'binary_with_inputs', 'shift_with_input',
    'max_with_input', 'evm_with_inputs', 'simplify_options_with_inputs', 'simplify_with_inputs')]
CLAIMS += [NS + name for name in ('projection_at_read_bind', 'projection_read_bind', 'InputFrame.queries_at', 'InputFrame.root_at',
    'dispatch_projects_framed_at', 'dispatcher_projects_cursor', 'dispatcher_verified_cursor', 'InputFrame.initial', 'InputFrame.caller', 'InputFrame.queries', 'InputFrame.root',
    'dispatch_projects_framed', 'dispatch_projects', 'dispatcher_projects', 'dispatcher_verified')]

CLAIMS += [READS + name for name in ('arguments_represented', 'checked_fault', 'arguments_offset', 'query_at')]
CLAIMS += [FACTS + 'reads']
CLAIMS += [TIMING + name for name in ('drop_repeated', 'reassociate', 'shift_mask', 'shift_product',
    'signextend', 'alternating_search', 'alternating', 'constant_stage', 'unary_stage', 'evm_stage',
    'binary_stage', 'simplify_options', 'simplify')]


def bindings():
    return {'constructors': borrowed.bindings(),
            'scope': 'one finite unfolding family of existing native constructor entries and the shared dispatcher with native indexed loads; '
                     'XOR publication -> ISZERO(XOR) -> borrowed EQ growth OOM -> parent and literal cleanup',
            'nativeQueryInputs': 'explicit owner; native constant/item/descriptor and operand allocation reads; '
                'queries execute against reached memory; complete shared-body timing theorem derives entry-snapshot equivalence',
            'observationExhaustion': 'unsupported, nonordinary; retain reached world',
            'sharedIndexedInputCorrespondence': 'all dispatcher instructions/options; query equations retained through read binds; '
                'reached graph prefix and normalized ownership derive loads under proper-child simulation',
            'allSufficientDepths': True, 'generalRecursiveInductionVerified': False}


def audit(claims):
    required = {
        READS + 'query_at': {READS + 'query', READS + 'reads'},
        TIMING + 'simplify': {TIMING + 'simplify_options'},
        TIMING + 'simplify_options': {TIMING + name for name in
            ('or_next', 'constant_stage', 'binary_stage', 'unary_stage', 'evm_stage')},
        TIMING + 'binary_stage': {TIMING + name for name in
            ('search_bind', 'query_bind', 'terminal_related', 'drop_repeated', 'reassociate',
             'shift_mask', 'shift_product', 'signextend', 'alternating')},
        TIMING + 'alternating': {TIMING + 'alternating_search'},
        TIMING + 'alternating_search': {TIMING + 'query_bind', TIMING + 'terminal_related'},
        NS + 'dispatcher_snapshot': {NS + 'context', READS + 'query', TIMING + 'simplify'},
        READS + 'arguments_represented': {arguments.OWNED + 'TemporaryMemory.readId_of_load'},
        READS + 'checked_fault': {READS + 'checked'},
        READS + 'arguments_offset': {READS + 'arguments'},
        FACTS + 'reads': {FACTS + 'constants', FACTS + 'operations', READS + 'arguments_represented',
            arguments.OWNED + 'BorrowedQuery.accepted_good'},
        EFFECTS + 'simplify_with_inputs': {EFFECTS + 'simplify_options_with_inputs'},
        EFFECTS + 'simplify_options_with_inputs': {EFFECTS + name for name in
            ('binary_with_inputs', 'unary_with_inputs', 'evm_with_inputs')},
        EFFECTS + 'binary_with_inputs': {EFFECTS + name for name in
            ('ReadBind.bind', 'Inputs.load', 'alternating_with_inputs', 'signextend_with_inputs', 'shift_product_with_inputs')},
        EFFECTS + 'alternating_inputs': {'Compiler.Extraction.AlternatingMask.candidate_found', EFFECTS + 'Inputs.load'},
        EFFECTS + 'evm_with_inputs': {EFFECTS + 'shift_with_input', EFFECTS + 'max_with_input'},
        NS + 'InputFrame.caller': {FACTS + 'frame', NS + 'InputFrame.initial',
            arguments.OWNED + 'Insertion.Native.CallerInput.graph_custody'},
        NS + 'InputFrame.queries_at': {arguments.OWNED + 'NativeGraph.Facts.operand_after_append'},
        NS + 'InputFrame.root_at': {arguments.OWNED + 'BorrowedQuery.slice_complete',
            arguments.OWNED + 'BorrowedQuery.slice_sound', arguments.ITEM + 'ShiftInput.operand_good'},
        NS + 'dispatch_projects': {NS + 'dispatch_projects_framed'},
        NS + 'projection_read_bind': {NS + 'projection_at_read_bind'},
        NS + 'InputFrame.queries': {NS + 'InputFrame.queries_at', FACTS + 'operand_after_append'},
        NS + 'InputFrame.root': {NS + 'InputFrame.root_at', arguments.ITEM + 'ShiftInput.operand_good'},
        NS + 'dispatch_projects_framed': {NS + 'dispatch_projects_framed_at'},
        NS + 'dispatch_projects_framed_at': {EFFECTS + 'simplify_with_inputs_at', NS + 'projection_at_read_bind',
            NS + 'InputFrame.queries_at', NS + 'InputFrame.root_at'},
        NS + 'dispatcher_projects': {NS + 'dispatcher_projects_cursor'},
        NS + 'dispatcher_projects_cursor': {NS + 'dispatch_projects_framed_at', NS + 'dispatcher_snapshot',
            NS + 'InputFrame.initial', FACTS + 'reads', arguments.OWNED + 'Recursive.cursorGraph'},
        NS + 'dispatcher_verified': {NS + 'dispatcher_verified_cursor'},
        NS + 'dispatcher_verified_cursor': {FACTS + 'reads', NS + 'dispatcher_snapshot', NS + 'dispatch_projects_framed_at',
            arguments.OWNED + 'Recursive.ProjectsAt.safe', 'Compiler.Extraction.Interner.Invariant.with_cursor',
            'Compiler.Extraction.Dispatch.default_key_simplify_safe', 'Compiler.Extraction.Interner.representative_reads_sound'},
        NS + 'dispatcher_inputs': {NS + 'context', NS + 'operand', READS + 'query', READS + 'reads', 'Compiler.Extraction.Dispatch.simplifyWithInputs',
            arguments.ITEM + 'ShiftInput.operand'},
        NS + 'operation_succ': {arguments.ARGUMENTS + 'operation', NS + 'context', NS + 'unfold'},
        NS + 'borrowed_succ': {views.NS + 'borrowed_forwards', NS + 'unfold'},
        NS + 'local_succ': {views.NS + 'local_forwarded', NS + 'unfold'},
        NS + 'zero_local': {NS + 'unfold', NS + 'exhausted'},
        NS + 'constant_succ': {arguments.ITEM + 'constant', NS + 'context', NS + 'unfold'},
        NS + 'materialize_succ': {arguments.ITEM + 'PairInput.materialize_forwarded'},
        NS + 'exhausted_rejected': {NS + 'exhausted', arguments.OWNED + 'ordinary'},
        NS + 'zero_entries': {NS + 'unfold', NS + 'exhausted'},
        TESTS + 'child_simplifier': {NS + 'dispatcher_snapshot', FACTS + 'reads', borrowed.TESTS + 'eq_miss', borrowed.TESTS + 'child_established'},
        TESTS + 'child_equivalent': {NS + 'borrowed_succ', TESTS + 'child_simplifier', borrowed.CALL + 'route'},
        TESTS + 'parent_continuation': {NS + 'dispatcher_snapshot', FACTS + 'reads', TESTS + 'child_equivalent', borrowed.TESTS + 'borrowed_failure',
            borrowed.TESTS + 'xor_query', borrowed.TESTS + 'parent_iszero'},
        TESTS + 'root_equivalent': {NS + 'operation_succ', TESTS + 'parent_continuation',
            arguments.ARGUMENTS + 'operation_prepared', borrowed.TESTS + 'child_contract'},
        TESTS + 'binary_simplifier': {NS + 'dispatcher_snapshot', FACTS + 'reads', 'Compiler.Extraction.Dispatch.simplifyWithInputs', arguments.ITEM + 'BinaryPreludeTests.established'},
        TESTS + 'binary_equivalent': {NS + 'operation_succ', TESTS + 'binary_simplifier', TESTS + 'binary_insertion',
            arguments.ITEM + 'BinaryPreludeTests.established', arguments.ARGUMENTS + 'operation_prepared'},
        TESTS + 'xor_simplifier': {TESTS + 'binary_simplifier'},
        TESTS + 'xor_insertion': {arguments.OWNED + 'Insertion.Native.insert'},
        TESTS + 'xor_equivalent': {TESTS + 'binary_equivalent'},
        TESTS + 'program_equivalent': {TESTS + 'xor_equivalent', TESTS + 'root_equivalent',
            borrowed.TESTS + 'xor_contract', 'Compiler.Algebraic.Effect.bind_success'},
        TESTS + 'program_contract': {TESTS + 'program_equivalent', borrowed.TESTS + 'composition',
            borrowed.TESTS + 'complete_contract'},
        TESTS + 'root_one': {borrowed.TESTS + 'borrowed_failure', NS + 'exhausted', borrowed.CALL + 'route'},
        TESTS + 'program_one': {TESTS + 'xor_equivalent', TESTS + 'root_one', borrowed.TESTS + 'xor_contract'},
        TESTS + 'incomplete_retains_parent': {TESTS + 'program_one', borrowed.TESTS + 'parent_established',
            borrowed.TESTS + 'literal_stack'},
    }
    for name, needed in required.items():
        missing = needed - claims[name]
        if missing:
            raise ValueError('recursive constructor family lost dependencies: ' + name + ': ' + ', '.join(sorted(missing)))
    return {'checkedDependencies': sorted(required), 'sourceBinding': bindings(),
            'oneContextForPublicationAndRecursiveFailure': True, 'indexedInputsUseReachedMemory': True, 'allSufficientDepthsVerified': True,
            'sharedDispatcherIndexedInputCorrespondenceVerified': True,
            'properChildSimulationRemainsPremise': True,
            'explicitCursorProjectionVerified': True, 'completeNativeResourceCouplingVerified': False,
            'exhaustionRetainsPublishedGraphAndLiveParent': True,
            'initialPrefixIsSelectedInsertionContinuations': False, 'initialPrefixUsesSameRecursiveContext': True,
            'nativeQuerySnapshotCorrespondenceVerified': True,
            'sourceQueryTimingVerified': True,
            'completeNativeQueryAndGuardConnectionVerified': False,
            'successfulRecursiveGrowthVerified': False, 'completePublicationRollbackVerified': False,
            'recursiveInductionVerified': False, 'composedProductionTheoremVerified': False}


def mutation_cases():
    def source(name):
        raw = (ROOT / 'lean/Compiler/Extraction' / name).read_text()
        imports = '\n'.join(line for line in raw.splitlines() if line.startswith('import '))
        # A forwarding mismatch must fail at this checked boundary, without
        # expanding the entire native constructor while printing/unifying it.
        boundary = ('attribute [local irreducible] ' + views.NS + 'localOperation '
                    'Compiler.Extraction.Dispatch.simplifyWithInputs ' + arguments.ITEM + 'ShiftInput.operand\n'
                    if name == 'InternerNativeRecursion.lean' else '')
        return imports + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + boundary + without_imports(raw)

    # Program mutations change only the composed invocation, not its already
    # audited prefix/call proofs. Copy that boundary under a diagnostic-only
    # namespace and import the complete helpers. Keep the full original module
    # in the aggregate audit and fresh imported kernel replay.
    raw_program = (ROOT / 'lean/Compiler/Extraction/InternerNativeRecursionTests.lean').read_text()
    anchors = ('namespace ' + TESTS[:-1], 'def children (', '/-- Both calls use one recursive context.',
               'theorem root_one (', 'theorem program_one (', '/-- Exhaustion before the first constructor')
    if any(raw_program.count(anchor) != 1 for anchor in anchors):
        raise ValueError('ambiguous recursive program control boundary')
    start, definitions, program_start, root_one, program_one, zero = map(raw_program.index, anchors)
    if not start < definitions < program_start < root_one < program_one < zero:
        raise ValueError('reordered recursive program control boundary')
    program_namespace = NS + 'ProgramControls'
    program_control = ('import Compiler.Extraction.InternerNativeRecursionTests\n'
               'set_option pp.maxSteps 8\nset_option pp.deepTerms false\n' +
               raw_program[start:definitions].replace(TESTS[:-1], program_namespace, 1) +
               'open ' + TESTS[:-1] + '\n'
               'attribute [local irreducible] ready rootArguments Arguments.operation\n'
               'section\nattribute [local irreducible] ReachablePrefixTests.sequence children\n' +
               raw_program[program_start:root_one] + raw_program[program_one:zero] +
               'end\n' + raw_program[zero:].replace('end ' + TESTS[:-1], 'end ' + program_namespace))

    # Recheck the generated dispatcher and its input proof together under a
    # fresh namespace. Logical operands still ignore the index, so an incorrect
    # native index must be rejected by the retained query/list evidence.
    shared = 'import Compiler.Extraction.DispatchSourceConstructors\nimport Compiler.Extraction.AlternatingMaskProofs\n'
    shared += 'set_option pp.maxSteps 8\nset_option pp.deepTerms false\n'
    for name in ('DispatchProgram.lean', 'DispatchInputEffects.lean'):
        body = without_imports((ROOT / 'lean/Compiler/Extraction' / name).read_text())
        if name == 'DispatchProgram.lean':
            # Keep unchanged recursive collectConstants and literal routines
            # shared with the imported proof; only the dispatcher stages and
            # their wrappers are copied into the diagnostic namespace.
            anchors = ('-- Source SHA-256:', '@[reducible] def binaryStageWithInputs',
                       '/-- The max-base EXP constructor sequence', '@[reducible] def evmStageWithInputs')
            if any(body.count(anchor) != 1 for anchor in anchors):
                raise ValueError('ambiguous shared dispatcher control boundary')
            header, binary, literals, evm = map(body.index, anchors)
            body = body[:header] + body[binary:literals] + body[evm:]
        body = body.replace('namespace Compiler.Extraction.Dispatch\n',
            'namespace Compiler.Extraction.DispatchInputMutation\nopen Compiler.Extraction.Dispatch\n')
        body = body.replace('end Compiler.Extraction.Dispatch\n', 'end Compiler.Extraction.DispatchInputMutation\n')
        body = body.replace('namespace Effects\n', 'namespace Effects\nopen Compiler.Extraction.Dispatch.Effects\n')
        body = body.replace('(Dispatch.simplify reads', '(DispatchInputMutation.simplify reads')
        shared += body + '\n'

    # Recheck the complete timing proof against a diagnostic copy of the same
    # generated dispatcher. A successful child may mutate; a missed stage may
    # not. These controls must fail without adding child-preservation premises.
    program = (ROOT / 'lean/Compiler/Extraction/DispatchProgram.lean').read_text()
    proof = (ROOT / 'lean/Compiler/Extraction/InternerQueryTiming.lean').read_text()
    imports = list(dict.fromkeys(line for raw in (program, proof) for line in raw.splitlines()
                                if line.startswith('import ')))
    program = without_imports(program).replace('namespace Compiler.Extraction.Dispatch\n',
        'namespace Compiler.Extraction.DispatchTimingMutation\nopen Compiler.Extraction.Dispatch\n')
    program = program.replace('end Compiler.Extraction.Dispatch\n', 'end Compiler.Extraction.DispatchTimingMutation\n')
    proof = without_imports(proof).replace('Recursive.QueryTiming\n', 'Recursive.QueryTimingMutation\n')
    for name in ('constantStage', 'binaryStageWithInputs', 'unaryStageWithInputs', 'evmStageWithInputs',
                 'maxExponent', 'simplifyOptionsWithInputs', 'simplifyWithInputs', 'defaultOptions'):
        proof = re.sub(r'\b' + name + r'\b', 'Compiler.Extraction.DispatchTimingMutation.' + name, proof)
    timing = '\n'.join(imports) + '\nset_option pp.maxSteps 8\nset_option pp.deepTerms false\n' + program + '\n' + proof

    return (
        ('query-timing', timing, (
            ('query-after-child',
             'let shifted ← ConstructorPair.scalars constructors instruction left masked.expression debug',
             'let shifted ← ConstructorPair.scalars constructors instruction left masked.expression debug\n'
             '              let _ ← query (fun reads => reads.constant left)', 1),
            ('mutating-miss', '  return none\n\n\n/-- Logical projection of the same source body. -/\ndef binaryStage',
             '  let _ ← constructors.constant 0 debug\n  return none\n\n\n/-- Logical projection of the same source body. -/\ndef binaryStage', 1),
        )),
        ('shared-inputs', shared, (
            ('borrowed-address', 'constructors.borrowedOperation inner.address opBYTE inner.items debug',
             'constructors.borrowedOperation 0 opBYTE inner.items debug', 1),
            ('borrowed-items', 'constructors.borrowedOperation inner.address opBYTE inner.items debug',
             'constructors.borrowedOperation inner.address opBYTE inner.items.reverse debug', 1),
            ('binary-index', 'operand lhs 1 a, ← operand rhs 1 b', 'operand lhs 0 a, ← operand rhs 1 b', 1),
            ('unary-index', 'operand third 0 inner', 'operand third 1 inner', 1),
            ('root-index', 'operand ⟨address, arguments⟩ 1 exponent', 'operand ⟨address, arguments⟩ 0 exponent', 3),
        )),
        ('native-reads', source('InternerNativeReads.lean'), (
            ('query-owner', '(Nested.readAction (m := GraphAction σ) (action (reads owner before.memory.memory))) before',
             '(Nested.readAction (m := GraphAction σ) (action (reads (owner + 1) before.memory.memory))) before', 1),
            ('wrong-owner', 'Operation.run memory (Owner.headerAddress ⟨owner, 0⟩)',
             'Operation.run memory (Owner.headerAddress ⟨owner + 1, 0⟩)', 1),
            ('wrong-constant-owner', 'Constant.value memory (Owner.headerAddress ⟨owner, 0⟩)',
             'Constant.value memory (Owner.headerAddress ⟨owner + 1, 0⟩)', 1),
            ('wrong-operand-index', '⟨address.allocation, 0, length⟩ index.val',
             '⟨address.allocation, 0, length⟩ (index.val + 1)', 1),
            ('wrong-operand-allocation', '⟨address.allocation, 0, length⟩ index.val',
             '⟨address.allocation + 1, 0, length⟩ index.val', 1),
            ('fault-as-invalid-id', '| .error _ => .error .safetyFault',
             '| .error _ => .error .invalidId', 1),
            ('operation-error-as-miss', '| .error fault => return .error fault',
             '| .error _ => return .ok none', 1),
            ('ignore-offset', 'if address.offset ≠ 0 then .error .unsupported else do',
             'if false then .error .unsupported else do', 1),
        )),
        ('model', source('InternerNativeRecursion.lean'), (
            ('logical-query-fallback', 'simplify := fun key source before => Dispatch.simplifyWithInputs (NativeReads.reads owner before.memory.memory)',
             'simplify := fun key source before => Dispatch.simplifyWithInputs (Interner.representativeReads before.graph)', 1),
            ('logical-input-fallback', 'key.instruction key.arguments debug operand source.address (NativeReads.query owner) before',
             'key.instruction key.arguments debug Nested.logicalOperand source.address (NativeReads.query owner) before', 1),
            ('snapshot-query-fallback', 'debug operand source.address (NativeReads.query owner) before',
             'debug operand source.address (fun action => Nested.readAction (action (NativeReads.reads owner before.memory.memory))) before', 1),
            ('indexed-input-position', 'ShiftInput.operand (view source) index',
             'ShiftInput.operand (view source) (index + 1)', 1),
            ('indexed-input-annotation', 'fun source index _ =>\n  ShiftInput.operand (view source) index',
             'fun _ _ annotation => pure annotation', 1),
            ('exhaustion-as-oom', '(.error (.language .unsupported), before)',
             '(.error (.language .outOfMemory), before)', 11),
            ('borrowed-address', 'debug)).borrowedOperation address opcode values debug',
             'debug)).borrowedOperation (address + 1) opcode values debug', 1),
            ('constant-value', 'debug)).constant value debug', 'debug)).constant (value + 1) debug', 1),
            ('literal-order', 'debug)).operation opcode values debug', 'debug)).operation opcode values.reverse debug', 1),
            ('local-index', 'debug)).localOperation opcode source selected repeated first debug',
             'debug)).localOperation opcode source (selected + 1) repeated first debug', 1),
            ('local-copy-disabled', 'debug)).localOperation opcode source selected repeated first debug',
             'debug)).operation opcode source.items debug', 1),
        )),
        ('dispatch', source('InternerNativeDispatch.lean'), (
            ('misbound-original-source', 'Caller.SourcePrivate source world.memory.effects.keys',
             'Caller.SourcePrivate { source with allocation := source.allocation + 1 } world.memory.effects.keys', 2),
            ('misbound-parent-custody', 'Caller.GraphCustody allocator normalized (rows ++ added) world.memory',
             'Caller.GraphCustody allocator { normalized with address := normalized.address + 1 } (rows ++ added) world.memory', 1),
            ('normalized-as-original', 'InputFrame safety allocator owner rows source request.arguments normalized taken.world',
             'InputFrame safety allocator owner rows source values normalized taken.world', 1),
            ('lost-row-prefix', 'world (rows ++ added)', 'world (added ++ rows)', 1),
            ('wrong-root-address', 'operand normalized := by',
             'operand { normalized with address := normalized.address + 1 } := by', 1),
            ('invented-result', 'executed.1 = logical.1.mapError Fault.language',
             'executed.1 = .ok (some 0)', 2),
            ('discarded-child-cursor', 'cursorGraph cursor executed.2 = logical.2', 'cursorGraph cursor before = logical.2', 1),
            ('discarded-child-graph', 'executed.2.graph = logical.2', 'executed.2.graph = before.graph', 1),
        )),
        ('program', program_control, (
            ('truncated-prefix', 'ReachablePrefixTests.sequence (children safety depth) 3',
             'ReachablePrefixTests.sequence (children safety depth) 2', 1),
            ('wrong-returned-id', '.operation 21 [id] debug) (CallerInputTests.world safety)',
             '.operation 21 [0] debug) (CallerInputTests.world safety)', 1),
            ('stale-world', '(children safety depth).operation 21 [id] debug) (CallerInputTests.world safety)',
             '(fun _ => (children safety depth).operation 21 [id] debug (initial safety))) (CallerInputTests.world safety)', 1),
            ('wrong-result', '(program safety (depth + 2)).1 = .error (.language .outOfMemory)',
             '(program safety (depth + 2)).1 = .error (.language .capacity)', 1),
            ('retain-parent-literal', '(program safety (depth + 2)).2.memory.memory.heap.lookup rootSource.allocation = none ∧',
             '(program safety (depth + 2)).2.memory.memory.heap.lookup rootSource.allocation ≠ none ∧', 1),
            ('exhaustion-ordinary', 'ordinary (program safety 1).1 = false ∧',
             'ordinary (program safety 1).1 = true ∧', 1),
            ('exhaustion-erases-parent', 'cell.stack = true := by\n  rw [program_one]',
             'cell.stack = false := by\n  rw [program_one]', 1),
        )),
    )


def controls(output, env, lean):
    from assembly_item_creation_checks import checked_controls
    records = []
    for group, text, changes in mutation_cases():
        for name, before, _, count in changes:
            if text.count(before) != count:
                raise ValueError('ambiguous recursive constructor mutation: ' + group + '-' + name)
        records += checked_controls(output, [mutation_check(output, 'native-recursion-' + group + '-unchanged', text, True, env, lean)])
        for name, before, after, _ in changes:
            records += checked_controls(output, [mutation_check(output, 'native-recursion-' + group + '-' + name,
                text.replace(before, after), False, env, lean)])
    return records
