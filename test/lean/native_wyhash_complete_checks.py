"""Audit complete native update execution and the exposed empty-view boundary.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check, kernel_rejection
from check_zig_air_memory_proofs import without_imports
from check_word_swap import ROOT

AIR = 'Compiler.ZigAir.WyhashUpdateAir.'
MODEL = 'Compiler.Extraction.WyhashUpdate.'
TEST = 'Compiler.ZigAir.WyhashUpdateAirTests.'
EMPTY = 'Compiler.Extraction.ExpressionMap.HashSlice.empty_native_update'
CLAIMS = ['Compiler.ZigAir.AggregateAir.SavedValue.owned', MODEL + 'update_from_body']
CLAIMS += [AIR + n for n in ('parameters_with_input', 'guard_select', 'buffered_invocation_framed',
    'Index.generated_entry', 'Index.allocate_steps', 'Index.store',
    'Fill.length_steps', 'Fill.length_before', 'Fill.generated_guard', 'Fill.guard_steps', 'Fill.guard_before',
    'Fill.generated_assign', 'Fill.assign_steps', 'Fill.assigned_before',
    'Fill.generated_target', 'Fill.target_head_steps', 'Fill.target_tail_steps', 'Fill.target_steps',
    'Fill.generated_source', 'Fill.source_steps', 'Fill.source_before', 'Fill.generated_copy_end', 'Fill.copy_end_steps',
    'Loop.At.mutated', 'Fill.copy_steps', 'Fill.generated_reset', 'Fill.reset_steps', 'Fill.reset_before',
    'Fill.execute', 'Long.execute', 'long_steps', 'invocation', 'empty_literal')]
CLAIMS += [EMPTY, TEST + 'complete_invocation_specializes', TEST + 'anonymous_empty_rejected', TEST + 'caller_empty_view_rejected']
DEFINITION_NAMES = [AIR + n for n in ('decisionEnv', 'Index.guard', 'Index.continuation', 'Index.resultEnv',
    'Fill.lengthCode', 'Fill.lengthEnv', 'Fill.skip', 'Fill.decision', 'Fill.guardEnv', 'Fill.copy', 'Fill.assign',
    'Fill.assignedEnv', 'Fill.targetTail', 'Fill.targetHead', 'Fill.targetHeadEnv', 'Fill.targetTailEnv',
    'Fill.sourceCode', 'Fill.sourceEnv', 'Fill.copyEnd', 'Fill.reset', 'Fill.resetEnv',
    'Fill.Interrupted', 'Long.Interrupted', 'Interrupted', 'emptyArguments')]
STATEMENT_NAMES = [MODEL + 'update_from_body', EMPTY]
STATEMENT_NAMES += [AIR + n for n in ('parameters_with_input', 'guard_select', 'buffered_invocation_framed',
    'Index.allocate_steps', 'Fill.assign_steps', 'Fill.copy_steps', 'Fill.reset_steps', 'Fill.execute',
    'Long.execute', 'long_steps', 'invocation', 'empty_literal')]
# Reviewed exported terms are pinned before acceptance, never by the gate.
DEFINITIONS = {'Compiler.ZigAir.WyhashUpdateAir.decisionEnv': '39da2ac7c5a32e79610c6220aeaefcac925251e90b5c83f4fe2a88e3615e22f6',
 'Compiler.ZigAir.WyhashUpdateAir.Index.guard': '4107b4fb25332224390321b5264574e84d0bffdc102e1052dff2a7bcb8d5b7de',
 'Compiler.ZigAir.WyhashUpdateAir.Index.continuation': 'c25c6ca22406ca2340ec03c1471949c3e19b61cecd36fa82d9f75066314aaf4a',
 'Compiler.ZigAir.WyhashUpdateAir.Index.resultEnv': '81e6dacb2c8af699b5f742a3535b8d801b8d3afb03263d69a73605e6ca12e263',
 'Compiler.ZigAir.WyhashUpdateAir.Fill.lengthCode': 'adf82d15bb41ed87535a389206d96b67cc1c30814c157fe1cd407f0230901204',
 'Compiler.ZigAir.WyhashUpdateAir.Fill.lengthEnv': '6c9579d319641de4d1bdac5c370c7bb036644bd0d2cb0484f5d1328ac5ad9520',
 'Compiler.ZigAir.WyhashUpdateAir.Fill.skip': '70a92f22412a6d966190338b8f878ce9c1b29e19d06531864087338c4372eb7d',
 'Compiler.ZigAir.WyhashUpdateAir.Fill.decision': '13e10b7c1be939cd312511a7483409edfd18463ed36edab9af095a7bee389114',
 'Compiler.ZigAir.WyhashUpdateAir.Fill.guardEnv': 'ef2bb066a0e09059d55882fdae7fc1e42bb5f059afc2f9a01da9a58c20690735',
 'Compiler.ZigAir.WyhashUpdateAir.Fill.copy': '6dcaab3a2da1e3d92eafc38aecbea1efe98d659584e396846bda25d40f09a353',
 'Compiler.ZigAir.WyhashUpdateAir.Fill.assign': 'dfe388c38c2f33adcca5e6244649a2d7215e92752ef08c0791b29ce5dc640325',
 'Compiler.ZigAir.WyhashUpdateAir.Fill.assignedEnv': '54bd55188b76db6551957063b659f0405ab7d5d62dbf8de483f9fd701d0f2c0c',
 'Compiler.ZigAir.WyhashUpdateAir.Fill.targetTail': '5df328592f71a782f452895387801341c6161d14b09d2a80fcf9f81f9fb1e4a7',
 'Compiler.ZigAir.WyhashUpdateAir.Fill.targetHead': '74d7ca6fffdee57f23975830976cbf1716764e07212e7d39c4de6f8861129227',
 'Compiler.ZigAir.WyhashUpdateAir.Fill.targetHeadEnv': 'f972756aadd981e017e7d4ed62bbf0edf1923dcc5bdd4aecb6d13bfb9eee6684',
 'Compiler.ZigAir.WyhashUpdateAir.Fill.targetTailEnv': 'd827d61f04412a94ecc11468e346300b7feccf9c843af51bc8f9163467e6ae74',
 'Compiler.ZigAir.WyhashUpdateAir.Fill.sourceCode': '32f830b91182238c9ba4bb77914cb3e1539a49c3b93409cab85c2c7aaab4f17b',
 'Compiler.ZigAir.WyhashUpdateAir.Fill.sourceEnv': '0ebfc215bffe32dbf877590d3a61a875a30c5c0b05897546006c5b3573f4586f',
 'Compiler.ZigAir.WyhashUpdateAir.Fill.copyEnd': '81a33b5bae584a742e3a9a740f790feb66ce7daa2f4303195953b1a57dff1d52',
 'Compiler.ZigAir.WyhashUpdateAir.Fill.reset': 'e5ac98459df4853fac3303c5e937754a9edfd1a048a1f500104492aefe40a69f',
 'Compiler.ZigAir.WyhashUpdateAir.Fill.resetEnv': '8f02d79231e5a1b17271324f8900e0b1ffc4a886a37884d6093bf237edbfca86',
 'Compiler.ZigAir.WyhashUpdateAir.Fill.Interrupted': '74e80a7cd4668369df1f2ac5accb43f480545a11c1fbafc13ade5bf567b80fe2',
 'Compiler.ZigAir.WyhashUpdateAir.Long.Interrupted': 'f8f029d08bbc6ef8970cdb37d2bdc79648daa797a6c52eb254613026cab89b7a',
 'Compiler.ZigAir.WyhashUpdateAir.Interrupted': 'e64e5bd24f90f5189df9db2b206c9e9602f1f099801beb20cb772a23fe87b873',
 'Compiler.ZigAir.WyhashUpdateAir.emptyArguments': '1d555537181f59e0fc3e60381e65398acb1da0fa7dabf955390e52419fd2ee7f'}
STATEMENTS = {'Compiler.Extraction.WyhashUpdate.update_from_body': 'c1353c5f8fa71b58f063718251bcf0f57437632f5b2622748b7af59e2f4e8ef8',
 'Compiler.ZigAir.WyhashUpdateAir.parameters_with_input': 'f762a4a0b3a2b5a56b7863497d74ad2ec2593ec8b94f839392b67fc792ff9df4',
 'Compiler.ZigAir.WyhashUpdateAir.guard_select': '097d8897eb4ae156d17017eea96e5a5ce85927d86a398d70c3d426f54ec8425e',
 'Compiler.ZigAir.WyhashUpdateAir.buffered_invocation_framed': 'cdefd0c0a522c8b0979928b79f85f272b1481f50a2f82c99fc188a467d3c280b',
 'Compiler.ZigAir.WyhashUpdateAir.Index.allocate_steps': 'f3e4d31a752d65445b676248c61028ab066863a958413d589eb8d4a5e3f2ef91',
 'Compiler.ZigAir.WyhashUpdateAir.Fill.assign_steps': '267c4ff13161ca269a41329402f0af42480e7a0005e0f24adbe957bbe8aa39ce',
 'Compiler.ZigAir.WyhashUpdateAir.Fill.copy_steps': 'f385d2b35a01aacf9414f7d47501ee1d5c8f08af4f0e98351b206b88a0a79341',
 'Compiler.ZigAir.WyhashUpdateAir.Fill.reset_steps': '807ce2f8ee8a290ef30540128eec9b0470fff78d74c2b6a1cbb3ff53987e740c',
 'Compiler.ZigAir.WyhashUpdateAir.Fill.execute': 'dadf21b0ec7849e0ffb29a525d504df7b417292d540f8eb842168e9ee75e9b05',
 'Compiler.ZigAir.WyhashUpdateAir.Long.execute': '4fb60254acac34edbc751a2c53b5c054dc504f7473ace794811112b1e4e8e248',
 'Compiler.ZigAir.WyhashUpdateAir.long_steps': '28a99d3b54c97afcbfc0d633912cfe604365c8e0a0a2c75e3dd4b054bbc71802',
 'Compiler.ZigAir.WyhashUpdateAir.invocation': 'e682c63149d9c8932f383b7864909004a55a1ae7a240f12a740965d2688bd20f',
 'Compiler.ZigAir.WyhashUpdateAir.empty_literal': '2582ac6c143a5859f4a4bf21dbcfbeb828beb87429031c21a5585f76a7f579c5',
 'Compiler.Extraction.ExpressionMap.HashSlice.empty_native_update': '0b87c2778d48f55a69a9cefe33501fbc291bad86c2214bf811aeac7694d742f8'}


def audit(rows, encoded_digest, require):
    indexed = {row['theorem']: row for row in rows}
    require(set(STATEMENTS) == set(STATEMENT_NAMES), 'incomplete native update statement pins')
    for name, expected in STATEMENTS.items():
        require(encoded_digest(indexed[name]['statement']) == expected, 'native update statement changed: ' + name)
    for name in CLAIMS:
        if not name.startswith(TEST):
            require(not any('Tests' in d for d in indexed[name]['dependencies']), 'native update depends on fixtures')
    required = {
        AIR + 'Index.allocate_steps': {'Compiler.ZigAir.AggregateAir.SavedValue.owned'},
        AIR + 'Fill.assign_steps': {AIR + 'Fill.length_steps', AIR + 'Index.store'},
        AIR + 'Fill.copy_steps': {AIR + 'Fill.target_steps', AIR + 'Fill.source_steps', AIR + 'Fill.copy_end_steps', AIR + 'copy_bytes'},
        AIR + 'Fill.execute': {AIR + 'Fill.guard_steps', AIR + 'Fill.assign_steps', AIR + 'Fill.copy_steps',
                              AIR + 'Round.buffer_steps', AIR + 'Fill.reset_steps', AIR + 'Loop.At.mutated'},
        AIR + 'Long.execute': {AIR + 'Index.allocate_steps', AIR + 'Fill.execute', AIR + 'Loop.through_return'},
        AIR + 'long_steps': {AIR + 'counter_steps', AIR + 'guard_select', AIR + 'Long.execute',
                            MODEL + 'update_from_body', MODEL + 'update_verified'},
        AIR + 'invocation': {AIR + 'parameters_with_input', AIR + 'buffered_invocation_framed', AIR + 'long_steps',
                            'Compiler.ZigAir.AggregateCall.Program.run_of_steps', 'Compiler.ZigAir.Memory.StackFrame.cleaned'},
        EMPTY: {'Compiler.Extraction.ExpressionMap.HashSlice.view_verified', AIR + 'empty_literal'},
        TEST + 'complete_invocation_specializes': {AIR + 'invocation'},
    }
    for name, dependencies in required.items():
        require(dependencies <= set(indexed[name]['dependencies']), 'native update composition bypassed: ' + name)
    return {'checkedStatements': list(STATEMENTS), 'checkedDependencies': sorted(required),
            'completeUpdateInvocationVerified': True, 'partialOomWritesRetained': True,
            'cleanupAndAllocationHistoryVerified': True, 'anonymousEmptyViewRejected': True,
            'originalInputAndRootAdmissionRequired': True, 'hashRunnerConsumptionVerified': False,
            'consumedByLookupPublication': False,
            'remainingHashConnections': ['anonymous-empty-slice-adapter', 'caller-byte-admission',
                                         'hash-runner-consumption', 'finalization-air', 'context-key-copy-admission']}


def controls(output, env, lean):
    records = []
    groups = (
        ('fill-target', 'WyhashUpdateAirFillTarget', 'WyhashUpdateAirFillIndex', (
            ('wrong-fill-offset', '.offsetPointer false (.local 69) (.local 67)', '.offsetPointer false (.local 69) (.local 68)'),
            ('oversized-fill', '(bounded : length + count ≤ 48)', '(bounded : length + count ≤ 49)'),
        )),
        ('fill-reset', 'WyhashUpdateAirFillExecution', 'WyhashUpdateAirFillSource', (
            ('wrong-reset', '.int false 64 0', '.int false 64 1'),
        )),
        ('complete-update', 'WyhashUpdateAirComplete', 'WyhashUpdateAirCompleteSteps', (
            ('unadmitted-input', '(reads : ByteRange.Reads state address view.length bytes)', '(reads : ByteRange.Reads state address 0 bytes)'),
            ('allow-alias', '(apart : address.allocation ≠ id)', '(apart : True)'),
            ('discard-oom-writes', 'after.heap = (frame.install failedCells).heap', 'after.heap = state.heap'),
            ('discard-success-writes', 'after.heap = (frame.install cells).heap', 'after.heap = state.heap'),
            ('unchecked-total', '(sumBound : total + view.length < addressLimit)', '(sumBound : True)'),
        )),
        ('empty-native', 'WyhashUpdateAirEmpty', 'WyhashUpdateAirComplete', (
            ('pretend-empty-success', 'result = .error .unsupported', 'result = .ok (.value (.scalar .unit))'),
        )),
    )
    for label, module, imports, edits in groups:
        source = without_imports((ROOT / f'lean/Compiler/ZigAir/{module}.lean').read_text())
        prefix = 'import Compiler.ZigAir.' + imports + '\n'
        records.append(mutation_check(output, label + '-unchanged', prefix + source, True, env, lean))
        for name, before, after in edits:
            if before not in source:
                raise ValueError('missing native update mutation site: ' + name)
            mutated = source.replace(before, after)
            if name == 'wrong-fill-offset':
                mutated = mutated.split('theorem generated_target', 1)[0]
                mutated += '\nend Compiler.ZigAir.WyhashUpdateAir.Fill\n'
                mutated += kernel_rejection(AIR + 'Fill.copy = ' + AIR + 'Fill.targetHead')
            elif name == 'wrong-reset':
                mutated = mutated.split('theorem generated_reset', 1)[0]
                mutated += '\nend Compiler.ZigAir.WyhashUpdateAir.Fill\n'
                mutated += kernel_rejection(AIR + 'Round.lanesAt false 3 = ' + AIR + 'Fill.reset')
            records.append(mutation_check(output, label + '-' + name, prefix + mutated, False, env, lean))
    return checked_controls(output, records)
