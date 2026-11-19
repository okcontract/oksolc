"""Audit general captured buffered-update refinement and its admission boundary.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check
from check_zig_air_memory_proofs import without_imports
from check_word_swap import ROOT
import native_wyhash_lane_checks as lane
import native_wyhash_round_checks as rounds
import native_wyhash_tail_checks as tail
import native_wyhash_complete_checks as complete

MEMORY = 'Compiler.ZigAir.Memory.'
BYTE = MEMORY + 'ByteRange.'
AIR = 'Compiler.ZigAir.WyhashUpdateAir.'
CALL = 'Compiler.ZigAir.AggregateCall.'
TEST = 'Compiler.ZigAir.WyhashUpdateAirTests.'
CLAIMS = [BYTE + n for n in ('Reads.install', 'Reads.extend', 'copyLoop_refines', 'copy_refines')]
CLAIMS += [MEMORY + n for n in ('allocate_end_bound', 'StackFrame.install_old', 'StackFrame.cleanup_install')]
CLAIMS += ['Compiler.ZigAir.AggregateAir.SavedValue.success_cursors']
CLAIMS += [CALL + n for n in ('primitive_bind', 'primitive_steps', 'save_steps', 'Program.run_of_steps')]
CLAIMS += ['Compiler.ZigAir.WyhashInit.' + n for n in ('object_word_read', 'object_word_store')]
CLAIMS += [AIR + n for n in ('field_pointer', 'byte_access', 'buffer_cast',
    'buffer_offset', 'buffer_slice', 'copy_buffer', 'generated_buffered_branch', 'generated_buffered_return',
    'generated_buffered_body', 'size_add', 'load_saved', 'buffered_return', 'buffered_loads',
    'buffer_offset_eval', 'buffer_bounds_eval', 'buffer_cast_eval', 'buffered_prepare', 'buffered_copy_tail',
    'buffered_body', 'saved_readonly', 'saved_cast', 'parameters', 'count_pointer', 'counter_steps',
    'generated_guard', 'guard_loads', 'size_bitcast', 'buffer_remaining', 'size_le', 'guard_choose',
    'buffered_steps', 'buffered_invocation')]
CLAIMS += [TEST + n for n in ('buffered_preserves', 'empty_full_buffer_one_past',
    'second_parameter_oom_cleans_first', 'no_initial_spare_address_required')]
DEFINITION_NAMES = [BYTE + 'Reads', MEMORY + 'CellFrame.extend']
DEFINITION_NAMES += [AIR + n for n in ('bufferedBody', 'bufferedReturn', 'bufferedCopy', 'bufferedLoaded',
    'bufferedPrepared', 'arguments', 'remaining', 'parameterEnv', 'counterEnv', 'guardBody', 'longBody',
    'guardEnv', 'chosenEnv')]
STATEMENT_NAMES = [BYTE + 'copy_refines', MEMORY + 'StackFrame.cleanup_install']
STATEMENT_NAMES += [AIR + n for n in ('parameters', 'counter_steps', 'buffered_body', 'guard_choose',
    'buffered_steps', 'buffered_invocation')]
# Exported terms are reviewed and pinned before acceptance, never by the gate.
DEFINITIONS = {'Compiler.ZigAir.Memory.ByteRange.Reads': 'b3b69c63d57a222d147d568bacea475c3c443340e57be0c154a467d569aa4f32',
 'Compiler.ZigAir.Memory.CellFrame.extend': '395b23451aa0f625e055fb506f9fc0de82dc9e3abc21ec9dac5daf2ec510fd41',
 'Compiler.ZigAir.WyhashUpdateAir.bufferedBody': '877b95864014b68b6784ebe1b45a5d0aaedcf53c8eabac7afbce8b6d11f2da98',
 'Compiler.ZigAir.WyhashUpdateAir.bufferedReturn': '4749bb162af3c46d38b13e96c801e748f75025fec8044d5ac23d1ccf39471e71',
 'Compiler.ZigAir.WyhashUpdateAir.bufferedCopy': '110e8d4e0011ef6811b31ac1dc59d0b36a918ee05ed6f55d74d38174586acfa6',
 'Compiler.ZigAir.WyhashUpdateAir.bufferedLoaded': 'b1261bf8306d792322d47e4895d9f897ac64210bdc2257869dacdebf98b1a29e',
 'Compiler.ZigAir.WyhashUpdateAir.bufferedPrepared': 'f8e140435a96a3b53e3ec3434812433a7db9f5998475a4a2aaf2880dba6a9411',
 'Compiler.ZigAir.WyhashUpdateAir.arguments': 'dafd613d72ca880b600690359830d966d81f07ceaae3bf29858c93378b0d671a',
 'Compiler.ZigAir.WyhashUpdateAir.remaining': '082d5a4aee5871965a367ee0efde14b229fff1f7d20ba189beec798538d842f3',
 'Compiler.ZigAir.WyhashUpdateAir.parameterEnv': '06de863c303b6e659e57930df0c7cbe892e0dee20ee69f86e7dec4d2c7ef5e54',
 'Compiler.ZigAir.WyhashUpdateAir.counterEnv': '4ad889af2774f553fd8378eff853cd3fb498baab658ad2f5a812dbd09191649c',
 'Compiler.ZigAir.WyhashUpdateAir.guardBody': 'fec570c199d634221a7b4a3c0fc5dc55a396c94914c434b109a8a24a0a9fbc6b',
 'Compiler.ZigAir.WyhashUpdateAir.longBody': '58046a2aa4952c9768365ea65df962ab69e449cb12b7182c3d5890dcd080daa1',
 'Compiler.ZigAir.WyhashUpdateAir.guardEnv': 'aa197c7c31764e4d0474fcc9320f14c3109955831241518b74edf4b8823739a4',
 'Compiler.ZigAir.WyhashUpdateAir.chosenEnv': '5821754b9d8444c4c86ea9a6af0f8afc8416755235e69b47e81d339517bfe194'}
STATEMENTS = {'Compiler.ZigAir.Memory.ByteRange.copy_refines': '85241b232e7d8485a806849b4cae130c890e7bbb425802d210ee11ebfc7cc9c8',
 'Compiler.ZigAir.Memory.StackFrame.cleanup_install': '9d4daead00c97ec473b41bd2b25caf4adab30cc8241eeeeaf8333e22da6a9ff4',
 'Compiler.ZigAir.WyhashUpdateAir.parameters': 'bf54c3e983b3a9bfe46b9ea55026397f2ffe7dfc4f22ccab3c95a082ebc240ca',
 'Compiler.ZigAir.WyhashUpdateAir.counter_steps': 'ffbe0af21ee415ec2bcc34d873a045acfbde8b90b6938487b4832feda9f32581',
 'Compiler.ZigAir.WyhashUpdateAir.buffered_body': 'd60dd2dcd520a2e099cccc38489921accb6053a57fb7cda570cdc637c2698516',
 'Compiler.ZigAir.WyhashUpdateAir.guard_choose': '24a87536c5d417ccec036b1e0962aff8ded91f125d56cf96478f1b06373fcae8',
 'Compiler.ZigAir.WyhashUpdateAir.buffered_steps': '5ddb5e619763af824d24daa5c3ea9c383f6e5fc4232adef5efbe7d13628c238a',
 'Compiler.ZigAir.WyhashUpdateAir.buffered_invocation': '3c2b0f7e080a8ed09a2c9454b22966b31d8addb8b533cc79f0573c9cb1f8b3c8'}


CLAIMS += lane.CLAIMS
DEFINITION_NAMES += lane.DEFINITION_NAMES
DEFINITIONS.update(lane.DEFINITIONS)
STATEMENT_NAMES += lane.STATEMENT_NAMES
STATEMENTS.update(lane.STATEMENTS)
CLAIMS += rounds.CLAIMS
DEFINITION_NAMES += rounds.DEFINITION_NAMES
DEFINITIONS.update(rounds.DEFINITIONS)
STATEMENT_NAMES += rounds.STATEMENT_NAMES
STATEMENTS.update(rounds.STATEMENTS)
CLAIMS += tail.CLAIMS
DEFINITION_NAMES += tail.DEFINITION_NAMES
DEFINITIONS.update(tail.DEFINITIONS)
STATEMENT_NAMES += tail.STATEMENT_NAMES
STATEMENTS.update(tail.STATEMENTS)
CLAIMS += complete.CLAIMS
DEFINITION_NAMES += complete.DEFINITION_NAMES
DEFINITIONS.update(complete.DEFINITIONS)
STATEMENT_NAMES += complete.STATEMENT_NAMES
STATEMENTS.update(complete.STATEMENTS)


def audit(rows, encoded_digest, require):
    lane_audit = lane.audit(rows, encoded_digest, require)
    round_audit = rounds.audit(rows, encoded_digest, require)
    tail_audit = tail.audit(rows, encoded_digest, require)
    complete_audit = complete.audit(rows, encoded_digest, require)
    indexed = {row['theorem']: row for row in rows}
    require(set(STATEMENTS) == set(STATEMENT_NAMES), 'incomplete buffered refinement statement pins')
    for name, expected in STATEMENTS.items():
        require(encoded_digest(indexed[name]['statement']) == expected, 'buffered refinement statement changed: ' + name)
        require(not any('Tests' in d for d in indexed[name]['dependencies']), 'buffered proof depends on fixtures')
    required = {
        AIR + 'copy_buffer': {BYTE + 'copy_refines', 'Compiler.Extraction.WyhashUpdate.copy_buffer'},
        AIR + 'parameters': {CALL + 'save_steps', 'Compiler.ZigAir.AggregateAir.SavedValue.verified'},
        AIR + 'buffered_steps': {AIR + 'counter_steps', AIR + 'guard_choose', AIR + 'buffered_body',
                                'Compiler.Extraction.WyhashUpdate.update_verified'},
        AIR + 'buffered_invocation': {AIR + 'parameters', AIR + 'buffered_steps', CALL + 'Program.run_of_steps',
                                     MEMORY + 'StackFrame.cleanup_install'},
        TEST + 'buffered_preserves': {AIR + 'buffered_invocation'},
    }
    for name, dependencies in required.items():
        require(dependencies <= set(indexed[name]['dependencies']), 'buffered composition bypassed: ' + name)
    return {'checkedStatements': list(STATEMENTS), 'bufferedInvocationRefinementVerified': True,
            'laneRefinement': lane_audit,
            'roundAndLoopRefinement': round_audit,
            'loopThroughReturnRefinement': tail_audit,
            'completeUpdateRefinement': complete_audit,
            'allocationFailureAndCleanupVerified': True, 'generalUpdateRefinementVerified': True,
            'consumedByLookupPublication': False,
            'remainingUpdateCases': ['anonymous-empty-slice-adapter', 'caller-byte-admission', 'hash-runner-consumption']}


def controls(output, env, lean):
    source = without_imports((ROOT / 'lean/Compiler/ZigAir/WyhashUpdateAirExecution.lean').read_text())
    prefix = 'import Compiler.ZigAir.WyhashUpdateAirPrefix\n'
    records = [mutation_check(output, 'buffered-refinement-unchanged', prefix + source, True, env, lean)]
    edits = (
        ('unbounded-branch', '(fits : view.length ≤ 48 - length)', '(fits : True)'),
        ('unadmitted-input', '(reads : ByteRange.Reads state address view.length bytes)',
         '(reads : ByteRange.Reads state address 0 bytes)'),
        ('unchecked-total-overflow', '(sumBound : total + view.length < addressLimit)', '(sumBound : True)'),
        ('discard-hasher-writes', 'after.heap = (frame.install cells).heap', 'after.heap = state.heap'),
    )
    for name, before, after in edits:
        if before not in source:
            raise ValueError('missing refinement mutation site: ' + name)
        records.append(mutation_check(output, 'buffered-refinement-' + name,
                                      prefix + source.replace(before, after), False, env, lean))
    return checked_controls(output, records + lane.controls(output, env, lean) + rounds.controls(output, env, lean)
                            + tail.controls(output, env, lean) + complete.controls(output, env, lean))
