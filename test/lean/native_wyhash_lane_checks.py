"""Audit captured Wyhash lanes against the existing update invariant.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check
from check_zig_air_memory_proofs import without_imports
from check_word_swap import ROOT

BYTE = 'Compiler.ZigAir.Memory.ByteRange.'
AGGREGATE = 'Compiler.ZigAir.AggregateAir.'
INIT = 'Compiler.ZigAir.WyhashInit.'
MIX = 'Compiler.ZigAir.WyhashMixAllocation.'
READ = 'Compiler.ZigAir.WyhashUpdateAir.WordRead.'
ROUND = 'Compiler.ZigAir.WyhashUpdateAir.Round.'
LANE = 'Compiler.ZigAir.WyhashUpdateAir.Lane.'
TEST = 'Compiler.ZigAir.WyhashUpdateAirTests.'
CLAIMS = [BYTE + n for n in ('Reads.read_window', 'decode_window', 'decode_shift',
    'Reads.access_window', 'Reads.array_cast', 'Reads.byte_cast', 'Reads.offset_pointer')]
CLAIMS += [AGGREGATE + n for n in ('eval_offset', 'eval_bounds', 'eval_load_bytes', 'eval_bytes_word')]
CLAIMS += [INIT + 'mix_steps']
CLAIMS += [MIX + n for n in ('saved_word', 'result_word', 'result_before', 'steps')]
CLAIMS += [READ + n for n in ('assertion', 'block_limit', 'natural_constant', 'offset_eval',
    'array_bounds_eval', 'prepare_steps', 'finish_steps', 'steps', 'result_word', 'result_before')]
CLAIMS += [ROUND + n for n in ('generated_fill_branch', 'generated_loop_branch', 'generated_read_sites',
    'read_bounds', 'read_steps')]
CLAIMS += [LANE + n for n in ('prepare_steps', 'updated_valid', 'body_before', 'body_steps',
    'generated_second', 'generated_body', 'register_bounds', 'steps', 'model_eq', 'model_steps')]
CLAIMS += [TEST + n for n in ('lane_allocation_failures', 'later_lane_oom_keeps_completed_store')]
DEFINITION_NAMES = [INIT + n for n in ('mixCode', 'mixedEnvAt', 'mixedEnv')]
DEFINITION_NAMES += [MIX + n for n in ('code', 'allocatedEnv', 'resultEnv')]
DEFINITION_NAMES += [READ + n for n in ('prepare', 'save', 'finish', 'code', 'prepareEnv',
    'finishEnv', 'savedEnv', 'resultEnv')]
DEFINITION_NAMES += [ROUND + n for n in ('fillBody', 'loopBody', 'readSite', 'readBase', 'readGuard',
    'readOffset')]
DEFINITION_NAMES += [LANE + n for n in ('prepare', 'prepareEnv', 'finish', 'body', 'updatedCells',
    'bodyEnv', 'base', 'selfReg', 'inputReg', 'site', 'next', 'word')]
STATEMENT_NAMES = [BYTE + 'Reads.read_window', INIT + 'mix_steps', INIT + 'mix_prefix',
                   MIX + 'steps', READ + 'steps', LANE + 'steps', LANE + 'model_steps']
# Exported terms are reviewed and pinned before acceptance, never by the gate.
DEFINITIONS = {'Compiler.ZigAir.WyhashInit.mixCode': 'eb18eb0e121aa9b7887d5ed6750ad134d4490083cc30dfc1cbd4aeb59c09ef08',
 'Compiler.ZigAir.WyhashInit.mixedEnvAt': '7a07f9b2fc940a47218bed88864ee81951eb2fe1a84a0fc14c0c09c873789a18',
 'Compiler.ZigAir.WyhashInit.mixedEnv': '21bb27fee848cbb9b01d2f58f060053537581c8344d406409bbcded35100734a',
 'Compiler.ZigAir.WyhashMixAllocation.code': '08f64a65faf87f0e1435c968e9d63a9eeacad76013c837cbc304c3d14ce755a1',
 'Compiler.ZigAir.WyhashMixAllocation.allocatedEnv': '49f7df173dc7b8fa2e456422bf82d467de23dfada18e8f2fbad927188d027b09',
 'Compiler.ZigAir.WyhashMixAllocation.resultEnv': '3856a968b78e22cb739dd09184c809655847119d277b5545b6984b33b094c798',
 'Compiler.ZigAir.WyhashUpdateAir.WordRead.prepare': '667cc6dd8a9d97daab499fc9a969dca03a4960ba2a6042597667ba003e8458b3',
 'Compiler.ZigAir.WyhashUpdateAir.WordRead.save': '4a55a66526fc30475ac144c62b0bdf80215852f7a1a3252d73c24e2ab7038048',
 'Compiler.ZigAir.WyhashUpdateAir.WordRead.finish': '1033e08f3b04305bddf7370e25fa1d5991722faad5beb01eb39b0697f68aad4d',
 'Compiler.ZigAir.WyhashUpdateAir.WordRead.code': 'e0e8376f842c10353a59f0b9ac7d4a047e6faf76d5dfb6abc4aa44073d3585e1',
 'Compiler.ZigAir.WyhashUpdateAir.WordRead.prepareEnv': 'e501af04e10ba2ef44c1e8b0334afb5ecbf6341341861bd644605b2cf54f5c83',
 'Compiler.ZigAir.WyhashUpdateAir.WordRead.finishEnv': '01742d4ff48fc4d55f01bb9af1fb7dc54ece435babc29b7b5bd8214f9f69cb1c',
 'Compiler.ZigAir.WyhashUpdateAir.WordRead.savedEnv': '6f45fcaee415698f2130a47b6d855ea138953e8c0450dc5b61be0419522f9a03',
 'Compiler.ZigAir.WyhashUpdateAir.WordRead.resultEnv': '60e5e2dc94f43321364f635aa1c93ba1e08c437c426bd198e2eb21da18db38b5',
 'Compiler.ZigAir.WyhashUpdateAir.Round.fillBody': '9b23d70840c8d2f75b27b8d90fb8208f7c4d5f1fc74a285409ec29b8d05ad452',
 'Compiler.ZigAir.WyhashUpdateAir.Round.loopBody': '2b0bcae7d74241f73634c1b5e157e7c1b94de9df2ee49e5b61bd724ae3b3ca15',
 'Compiler.ZigAir.WyhashUpdateAir.Round.readSite': 'acaaada30a853d4c9dbe9e702e59dc3e056ca85918ca34eeff960ec3b1f3e090',
 'Compiler.ZigAir.WyhashUpdateAir.Round.readBase': '7ca8d85b6e4d10a281408ad269956cfafb134e45f8bb648bdacfac44bf920144',
 'Compiler.ZigAir.WyhashUpdateAir.Round.readGuard': '1ef740daf2676e28990a3ef5a722df35381acf52e48040696dbccba919f7a962',
 'Compiler.ZigAir.WyhashUpdateAir.Round.readOffset': 'd49d87b81bd7a18bce9deea50d266e40a9a0cac9a990ddd2970da32814909d46',
 'Compiler.ZigAir.WyhashUpdateAir.Lane.prepare': 'e7d261b4b4846b8c834b99ff09f03cb9eb0c4d5bcb4c387738b1cf4fa96d80b0',
 'Compiler.ZigAir.WyhashUpdateAir.Lane.prepareEnv': '9ad5921e4d2d7a5895e665c6e4cdb6378024ffb3d5b710c1af24667cb008ebd5',
 'Compiler.ZigAir.WyhashUpdateAir.Lane.finish': 'ca0f3ed9aa028e2980b6ed9c8e379cf46501faffecba7d45d8884999f2bcd74a',
 'Compiler.ZigAir.WyhashUpdateAir.Lane.body': 'f6688d589ab0654932563d45bb6b25f9c7b82ad7f4dcc6df6dd6f07c87866e46',
 'Compiler.ZigAir.WyhashUpdateAir.Lane.updatedCells': 'cf3d4d52847ab43ac0c6d197bb3d8c23df8e1701b4f7bc59369d9f72b7a8bf6e',
 'Compiler.ZigAir.WyhashUpdateAir.Lane.bodyEnv': '4321e24cde77b22d9f9bd1abb2b5e3e4ef60745ab6038606c6fcb3f3f191f066',
 'Compiler.ZigAir.WyhashUpdateAir.Lane.base': '6bc96b999491bc35fd89b4652247a60ac688e88c123d9d90213c536962d668d0',
 'Compiler.ZigAir.WyhashUpdateAir.Lane.selfReg': '3b99dbe6499ded3b19cb787f9061eca14f8a37b10960c047eb6c67aee4a84569',
 'Compiler.ZigAir.WyhashUpdateAir.Lane.inputReg': '650767631a005816d3407465fc1060543d6be26ce06932aedd2384952e394a08',
 'Compiler.ZigAir.WyhashUpdateAir.Lane.site': '1599397fc7906a3a9f199db31eee77f6aad00e3158e2e7844f3fb32277dd851c',
 'Compiler.ZigAir.WyhashUpdateAir.Lane.next': 'b4174bfb5588de76f087c238db14398dfb41c33ad9e6c59828f5127ca535d5c8',
 'Compiler.ZigAir.WyhashUpdateAir.Lane.word': 'b740e2a9bf323537e143744a69eab319b09faf65c09697e449a88722460150b3'}
STATEMENTS = {'Compiler.ZigAir.Memory.ByteRange.Reads.read_window': 'ca2a7f39c2dfd4f55e311d8c8012f5b54f68973acc396bc0676e81ddca3da790',
 'Compiler.ZigAir.WyhashInit.mix_steps': '49ee167d6b76b4f9bd63adbc7fb29c8d1d063a7934f54dc1a67eda9d06f7cc01',
 'Compiler.ZigAir.WyhashMixAllocation.steps': 'd65ab8fa847a0379aeb19f115f3a2cb004732898719ccdeef77e57d87707e435',
 'Compiler.ZigAir.WyhashUpdateAir.WordRead.steps': '523adf99f869ba71554b9ac312e546bed9983617faa5de6ab63662cebe6d31f5',
 'Compiler.ZigAir.WyhashUpdateAir.Lane.steps': '3d079cd6a94a2550910679db673dca8b748f6fd1d10d0e49d288b1905c644376',
 'Compiler.ZigAir.WyhashUpdateAir.Lane.model_steps': 'd8f770293e7c9c000a344dae6db753cd7974d0a94b40c653d193a30488c29770',
 'Compiler.ZigAir.WyhashInit.mix_prefix': '49d70068f7feaca784336cb70d69797a2f3f4d229df8b7896375eeb5e158cc66'}


def audit(rows, encoded_digest, require):
    indexed = {row['theorem']: row for row in rows}
    require(set(STATEMENTS) == set(STATEMENT_NAMES), 'incomplete native lane statement pins')
    for name, expected in STATEMENTS.items():
        require(encoded_digest(indexed[name]['statement']) == expected, 'native lane statement changed: ' + name)
    for name in CLAIMS:
        if not name.startswith(TEST):
            require(not any('Tests' in d for d in indexed[name]['dependencies']), 'native lane depends on fixtures')
    required = {
        INIT + 'mix_prefix': {INIT + 'mix_steps', 'Compiler.ZigAir.Control.Machine.finite_result'},
        READ + 'steps': {READ + 'prepare_steps', READ + 'finish_steps', AGGREGATE + 'SavedValue.verified',
                        'Compiler.ZigAir.AggregateCall.save_steps'},
        ROUND + 'read_steps': {READ + 'steps', ROUND + 'generated_read_sites'},
        LANE + 'body_steps': {LANE + 'prepare_steps', MIX + 'steps', INIT + 'lane_store_step',
                              'Compiler.ZigAir.Memory.StackFrame.install_old'},
        LANE + 'steps': {ROUND + 'read_steps', LANE + 'body_steps',
                         'Compiler.ZigAir.Memory.StackFrame.install_old'},
        LANE + 'model_steps': {LANE + 'steps', LANE + 'model_eq', 'Compiler.Extraction.WyhashUpdate.lane_verified'},
    }
    for name, dependencies in required.items():
        require(dependencies <= set(indexed[name]['dependencies']), 'native lane composition bypassed: ' + name)
    return {'checkedStatements': list(STATEMENTS), 'checkedDependencies': sorted(required),
            'capturedLaneModelRefinementVerified': True, 'fillAndLoopLaneSites': 6,
            'allocationsPerLane': 4, 'originalByteAdmissionRequired': True,
            'savedParameterAdmissionRequired': True, 'completeRoundRefinementVerified': False,
            'generalUpdateRefinementVerified': False, 'consumedByLookupPublication': False}


def controls(output, env, lean):
    source = without_imports((ROOT / 'lean/Compiler/ZigAir/WyhashUpdateAirLaneRefinement.lean').read_text())
    prefix = 'import Compiler.ZigAir.WyhashUpdateAirLane\n'
    records = [mutation_check(output, 'lane-refinement-unchanged', prefix + source, True, env, lean)]
    edits = (
        ('unadmitted-bytes', '(reads : ByteRange.Reads state address 48 ', '(reads : ByteRange.Reads state address 0 '),
        ('unrepresented-input', '(represented : ByteSlice.Represents (input.cells frame.cell.cells) input.view bytes)',
         '(represented : True)'),
        ('short-input', '(inside : offset + 48 ≤ input.view.length)', '(inside : offset + 47 ≤ input.view.length)'),
        ('discard-hasher-write', 'StackFrame (frame.install cells) after', 'StackFrame state after'),
        ('wrong-failure', '(.finished (.fault .outOfMemory after))', '(.finished (.fault .memoryValidity after))'),
    )
    for name, before, after in edits:
        if before not in source:
            raise ValueError('missing native lane mutation site: ' + name)
        records.append(mutation_check(output, 'lane-refinement-' + name,
                                      prefix + source.replace(before, after), False, env, lean))
    return checked_controls(output, records)
