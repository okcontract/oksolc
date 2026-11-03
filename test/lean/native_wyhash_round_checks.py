"""Audit captured rounds and the full-block loop, including partial OOM writes.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check
from check_zig_air_memory_proofs import without_imports
from check_word_swap import ROOT

MEMORY = 'Compiler.ZigAir.Memory.'
AIR = 'Compiler.ZigAir.WyhashUpdateAir.'
PARAMETER = 'Compiler.ZigAir.AggregateCall.ReadonlyParameter.'
ROUND = AIR + 'Round.'
LOOP = AIR + 'Loop.'
TEST = 'Compiler.ZigAir.WyhashUpdateAirTests.'
CLAIMS = [MEMORY + n for n in ('CellFrame.replaced_install', 'CellFrame.load_outside', 'ByteRange.Reads.window')]
CLAIMS += [PARAMETER + n for n in ('before', 'cast', 'steps')]
CLAIMS += [AIR + 'size_add_constant']
CLAIMS += [ROUND + n for n in ('buffer_locate', 'buffer_reads', 'InputAdmitted.reads',
    'represented_frame', 'InputAdmitted.install', 'InputAdmitted.extend', 'prefix_complete',
    'generated_lane_chain', 'prefix_steps', 'generated_parameters', 'parameter_bounds',
    'parameter_registers', 'parameter_before', 'parameters_steps', 'steps',
    'generated_buffer_preparation', 'buffer_prepare_steps', 'generated_external_preparation',
    'external_prepare_steps', 'buffer_steps', 'external_steps')]
CLAIMS += [LOOP + n for n in ('generated_entry', 'generated_guard', 'guard_before', 'size_lt',
    'branch_steps', 'guard_steps', 'generated_tail', 'tail_before', 'tail_steps',
    'At.old_load', 'At.reads', 'At.updated', 'execute', 'entry_steps')]
CLAIMS += [TEST + n for n in ('loop_admitted', 'loop_specializes')]
DEFINITION_NAMES = [MEMORY + 'CellFrame.replaced']
DEFINITION_NAMES += [PARAMETER + n for n in ('code', 'resultEnv')]
DEFINITION_NAMES += [ROUND + n for n in ('InputAdmitted', 'lanePrefix', 'lanesAt',
    'parameterBase', 'selfArgument', 'inputArgument', 'parameterSite', 'parameterEnv',
    'bufferSite', 'bufferPreparation', 'bufferEnv', 'externalPreparation', 'externalEnv')]
DEFINITION_NAMES += [LOOP + n for n in ('condition', 'body', 'continuation', 'entry', 'frames',
    'innerFrames', 'guardCode', 'guardEnv', 'tail', 'tailEnv', 'Context.mk', 'At.mk', 'Locals',
    'Interrupted.lane', 'Interrupted.next')]
DEFINITION_NAMES += [TEST + n for n in ('loopBase', 'loopContext', 'loopState', 'loopEnv')]
STATEMENT_NAMES = [PARAMETER + 'steps']
STATEMENT_NAMES += [ROUND + n for n in ('prefix_steps', 'parameters_steps', 'steps', 'buffer_steps', 'external_steps')]
STATEMENT_NAMES += [LOOP + n for n in ('guard_steps', 'tail_steps', 'execute', 'entry_steps')]
# Exported terms are reviewed and pinned before acceptance, never by the gate.
DEFINITIONS = {'Compiler.ZigAir.Memory.CellFrame.replaced': '5f957769b57d3adda8680d1a426afe8fa0b2d92196a80c6db5cae3a7a37b211b',
 'Compiler.ZigAir.AggregateCall.ReadonlyParameter.code': '00d286a5a7411e96b23c6c0f7d4eaec6172e18857a09748c8615469205bd2a82',
 'Compiler.ZigAir.AggregateCall.ReadonlyParameter.resultEnv': '7677ce3d8c45bdb2de8ab1711dc3ae24416a2df2769a0c8f7fc11d127a65007e',
 'Compiler.ZigAir.WyhashUpdateAir.Round.InputAdmitted': 'be00f4a769e3d8e9b74f729b19d93f97ac94464997c311a1343db65d93f41e5e',
 'Compiler.ZigAir.WyhashUpdateAir.Round.lanePrefix': 'aac6b332d823cabda744bdaf779b6467b59a0d3d2b8c1f9cb7594bec0df381bd',
 'Compiler.ZigAir.WyhashUpdateAir.Round.lanesAt': 'c93f077d00d52c5f71d66438d1b58874caa5f575eedef78f075c3d51f25a3502',
 'Compiler.ZigAir.WyhashUpdateAir.Round.parameterBase': '11df926776055b529cfb13a903958d244dc295e306321b7bbc823fd9dd63ca61',
 'Compiler.ZigAir.WyhashUpdateAir.Round.selfArgument': '94fc80e94cfde629582c2f996a0cfeef1f5c2cb28abcafb3b04f04e96a67acae',
 'Compiler.ZigAir.WyhashUpdateAir.Round.inputArgument': '4bc464d761b53483c87309d880594579ff1b0958cdff997ace9a14c34454a316',
 'Compiler.ZigAir.WyhashUpdateAir.Round.parameterSite': '2158fe030ac755b7c01b8a6b742f132d8b16c5e1252d7e094c52de6962551e06',
 'Compiler.ZigAir.WyhashUpdateAir.Round.parameterEnv': 'cb727cae75292bfac3bf44b4bba9a702389c6bbc0cf5c1caef215a1011522bb7',
 'Compiler.ZigAir.WyhashUpdateAir.Round.bufferSite': 'e7dc32a3c50575ebd315cbd9ecaeade64d8810d2e25273a7f29179f013f41d59',
 'Compiler.ZigAir.WyhashUpdateAir.Round.bufferPreparation': '9535b0dd0a729175e8a27178572fe44735d2510833b00caa9824049c04097b13',
 'Compiler.ZigAir.WyhashUpdateAir.Round.bufferEnv': '028da8e82f9356d9517c9f07f9c44b5bf4f889f4af4e398fa6f081675a75227c',
 'Compiler.ZigAir.WyhashUpdateAir.Round.externalPreparation': 'cb245126b4cab1eebeb41c48458b342deaa17542e13758c7eb4de16eeda15a67',
 'Compiler.ZigAir.WyhashUpdateAir.Round.externalEnv': '06606533226a53cb66e229e9e9288f5b1be6c36fa39e7d628fda8389f575d922',
 'Compiler.ZigAir.WyhashUpdateAir.Loop.condition': '72cfc701c97fc7b77cb542118d96c9effc1fef25f592627cc72dae2b486ab663',
 'Compiler.ZigAir.WyhashUpdateAir.Loop.body': '3e96b5d4397000340ff88109fdae6e32f0a07009f284037e454282a531e49dc2',
 'Compiler.ZigAir.WyhashUpdateAir.Loop.continuation': '49537bba73f5bc735bb2fc26829d461d18d9d0a9fbcf16b1e3d2b611f8d2a381',
 'Compiler.ZigAir.WyhashUpdateAir.Loop.entry': '8791817b9b9c3dd8cbdd8ef904bd7a2e6a01bc1368604a8a53531ddbb7e8396f',
 'Compiler.ZigAir.WyhashUpdateAir.Loop.frames': '9877140e20fa1fbdd1dec90ea5d2f0912d8fa108f9efb596405d832bc328880e',
 'Compiler.ZigAir.WyhashUpdateAir.Loop.innerFrames': '5f210c1cb9bc80a7d9ec1d7f951829fad4f0945bf79af9d3ff221e67cb45a147',
 'Compiler.ZigAir.WyhashUpdateAir.Loop.guardCode': '4b098e789e5d8feadb20e145cec3f73fe57d11209f5c4ca86c1c07a47ca2ed5a',
 'Compiler.ZigAir.WyhashUpdateAir.Loop.guardEnv': '064f15284b02e2bc8e0186fae6adbafd19bd14a2e6ecb3a9107f32d92a53fc0d',
 'Compiler.ZigAir.WyhashUpdateAir.Loop.tail': '329541c1e6afb2d42f6839d18d679a8037e27853316d9e37865c398134176276',
 'Compiler.ZigAir.WyhashUpdateAir.Loop.tailEnv': '67b34f3d0778ba90e242449be9e990b09abba672edd7ce45f73615e66aca463f',
 'Compiler.ZigAir.WyhashUpdateAir.Loop.Context.mk': 'aca034ded9e256d880b9b780a0dbce7ca38c0905835e9a2a71866f8b87dd782e',
 'Compiler.ZigAir.WyhashUpdateAir.Loop.At.mk': '0e7b5e44493b064dbf344724efb91868cbaaa5236b87a99f305a68aa07794cc9',
 'Compiler.ZigAir.WyhashUpdateAir.Loop.Locals': '68b361c925975f19447bdf7f08b32ebd53a5e7c7496a947b52558d70908661eb',
 'Compiler.ZigAir.WyhashUpdateAir.Loop.Interrupted.lane': '9b9dbccd558a19e790ee34c987066c4ab312cbb4700db767184b35161ec7ab59',
 'Compiler.ZigAir.WyhashUpdateAir.Loop.Interrupted.next': '3051e038a94e7570af1ce98e1868a06464ce977c9cac5fbe2b34074e3b32148c',
 'Compiler.ZigAir.WyhashUpdateAirTests.loopBase': 'bd063607b5894fe84c76c9c5c2dcba431ba61357f96394b8930c3748e6d4549a',
 'Compiler.ZigAir.WyhashUpdateAirTests.loopContext': '518366f4cb5a500bef9beeb25008701e6bc6812f56029250a8b4ea170fd4cf26',
 'Compiler.ZigAir.WyhashUpdateAirTests.loopState': 'd9487ac7169948f30eaeb2959d1a8c24bebcb0b82424cf90a1d334c95a11adfa',
 'Compiler.ZigAir.WyhashUpdateAirTests.loopEnv': '5f7f9e86c42bed074e9ea89dfe5996f711dae433471730886bed6ae8d41bf043'}
STATEMENTS = {'Compiler.ZigAir.AggregateCall.ReadonlyParameter.steps': 'a7133adcce9392493d4a0ceb1ab4b340f193d15c40b3b4734cd294a30fa7ff5d',
 'Compiler.ZigAir.WyhashUpdateAir.Round.prefix_steps': 'd513cc7e91689523b456933c0fce24971e9bfe130521059c2d88e09b02bfba2d',
 'Compiler.ZigAir.WyhashUpdateAir.Round.parameters_steps': '204b42c8104fb2a38d3705b7aff743fd2b06f5304d2e3a0c16ab99c3bb2b2c20',
 'Compiler.ZigAir.WyhashUpdateAir.Round.steps': 'efd3b1c48ecfb0d7950111a6800f607e951183656fc983d393de59a4f9c6009d',
 'Compiler.ZigAir.WyhashUpdateAir.Round.buffer_steps': '0f4fa0c354a43d0755b3828a947693e629f3155838afd4cfa9f2ddccd1d04ad9',
 'Compiler.ZigAir.WyhashUpdateAir.Round.external_steps': '4583802e01ea460e0c42d33c807818c6e4fb9c90cc2ad9c5b7fafdf9f4fb9817',
 'Compiler.ZigAir.WyhashUpdateAir.Loop.guard_steps': 'dfb4ff30a1938cd6f3e213ac0a4a9766cf0df92fdcc901c5043d7146ae3d6977',
 'Compiler.ZigAir.WyhashUpdateAir.Loop.tail_steps': '3a1809bb0ffd8bf2c0601a66fa27ad4b3d715664da8115cd4e8287dede3c107b',
 'Compiler.ZigAir.WyhashUpdateAir.Loop.execute': '6b7b05364abc07cbbe5bac997a0eb9f7afc3bb1a703c619ce8326e4c55652d05',
 'Compiler.ZigAir.WyhashUpdateAir.Loop.entry_steps': '710fb1338b0532ae8c0536446bce9aa6af35f0a6016e398149e2d77922f3928d'}


def audit(rows, encoded_digest, require):
    indexed = {row['theorem']: row for row in rows}
    require(set(STATEMENTS) == set(STATEMENT_NAMES), 'incomplete native round statement pins')
    for name, expected in STATEMENTS.items():
        require(encoded_digest(indexed[name]['statement']) == expected, 'native round statement changed: ' + name)
    for name in CLAIMS:
        if not name.startswith(TEST):
            require(not any('Tests' in d for d in indexed[name]['dependencies']), 'native round depends on fixtures')
    required = {
        AIR + 'parameters': {PARAMETER + 'steps'},
        ROUND + 'prefix_steps': {AIR + 'Lane.model_steps', MEMORY + 'StackFrame.install_old'},
        ROUND + 'parameters_steps': {PARAMETER + 'steps', ROUND + 'generated_parameters'},
        ROUND + 'steps': {ROUND + 'parameters_steps', ROUND + 'prefix_steps', ROUND + 'prefix_complete'},
        ROUND + 'buffer_steps': {ROUND + 'buffer_prepare_steps', ROUND + 'steps', ROUND + 'buffer_reads'},
        ROUND + 'external_steps': {ROUND + 'external_prepare_steps', ROUND + 'steps', MEMORY + 'ByteRange.Reads.window'},
        LOOP + 'execute': {LOOP + 'guard_steps', ROUND + 'external_steps', LOOP + 'tail_steps',
                           MEMORY + 'StackFrame.install'},
        LOOP + 'entry_steps': {LOOP + 'execute', 'Compiler.Extraction.WyhashUpdate.loop_verified'},
        TEST + 'loop_specializes': {LOOP + 'entry_steps', TEST + 'loop_admitted'},
    }
    for name, dependencies in required.items():
        require(dependencies <= set(indexed[name]['dependencies']), 'native round composition bypassed: ' + name)
    return {'checkedStatements': list(STATEMENTS), 'checkedDependencies': sorted(required),
            'completeRoundRefinementVerified': True, 'savedRoundParameterAdmissionRequired': False,
            'fullBlockLoopRefinementVerified': True, 'strictLoopBoundaryVerified': True,
            'partialOomWritesRetained': True, 'originalInputAndRootAdmissionRequired': True,
            'generalUpdateRefinementVerified': False, 'consumedByLookupPublication': False,
            'executionStopsAt': 'Loop.continuation'}


def controls(output, env, lean):
    records = []
    groups = (
        ('round-input', 'WyhashUpdateAirRoundRefinement', 'WyhashUpdateAirRoundPreparation', (
            ('shift-buffer-window', 'steps false frames frame valid typed .buffer 0 total core ready',
             'steps false frames frame valid typed .buffer 1 total core ready'),
            ('unadmitted-input', '(reads : ByteRange.Reads state address view.length bytes)',
             '(reads : ByteRange.Reads state address 0 bytes)'),
        )),
        ('loop-control', 'WyhashUpdateAirLoopControl', 'WyhashUpdateAirRoundRefinement\nimport Compiler.ZigAir.WyhashUpdateAirPrefix', (
            ('nonstrict-loop', '(.comparison .lt (.local 333) (.local 334))', '(.comparison .le (.local 333) (.local 334))'),
            ('wrong-index-stride', '(.local 578) (.constant (.int false 64 48))', '(.local 578) (.constant (.int false 64 47))'),
        )),
        ('loop-execution', 'WyhashUpdateAirLoopExecution', 'WyhashUpdateAirLoopControl', (
            ('unadmitted-bytes', 'reads : ByteRange.Reads base address view.length bytes', 'reads : ByteRange.Reads base address 0 bytes'),
            ('unowned-counter', 'indexFresh : base.nextId ≤ indexSlot', 'indexFresh : True'),
            ('unchecked-index-overflow', 'budget : view.length + 48 < addressLimit', 'budget : True'),
            ('discard-partial-writes', 'StackFrame (ctx.frame.install failedCells) after', 'StackFrame (ctx.frame.install cells) after'),
        )),
    )
    for label, module, imports, edits in groups:
        source = without_imports((ROOT / f'lean/Compiler/ZigAir/{module}.lean').read_text())
        prefix = 'import Compiler.ZigAir.' + imports + '\n'
        records.append(mutation_check(output, label + '-unchanged', prefix + source, True, env, lean))
        for name, before, after in edits:
            if before not in source:
                raise ValueError('missing native round mutation site: ' + name)
            records.append(mutation_check(output, label + '-' + name, prefix + source.replace(before, after), False, env, lean))
    return checked_controls(output, records)
