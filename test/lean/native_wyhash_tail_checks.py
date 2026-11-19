"""Audit native loop-through-return composition and retained allocation failures.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from assembly_item_creation_checks import checked_controls
from check_zig_air_proofs import mutation_check, kernel_rejection
from check_zig_air_memory_proofs import without_imports
from check_word_swap import ROOT

AIR = 'Compiler.ZigAir.WyhashUpdateAir.'
MODEL = 'Compiler.Extraction.WyhashUpdate.'
MEMORY = 'Compiler.ZigAir.Memory.'
TEST = 'Compiler.ZigAir.WyhashUpdateAirTests.'
CLAIMS = [MEMORY + 'ByteRange.Reads.make_slice']
CLAIMS += [AIR + n for n in ('end_bound', 'size_sub', 'slice_valid', 'size_comparison',
    'slice_pointer', 'slice_length', 'slice_construct', 'copy_bytes')]
CLAIMS += [AIR + 'Finish.' + n for n in ('generated_body', 'return_steps', 'prepare_steps', 'copy_return_steps', 'body_steps')]
CLAIMS += [AIR + 'Remainder.' + n for n in ('generated_preparation', 'prepared_before', 'head_steps',
    'construct_steps', 'prepare_steps', 'save_steps', 'execute')]
CLAIMS += [AIR + 'Suffix.' + n for n in ('generated_guard', 'prefix_steps', 'decision_steps', 'guard_steps',
    'generated_target_head', 'target_head_steps', 'generated_target_tail', 'target_tail_steps', 'target_steps',
    'generated_source_head', 'source_head_steps', 'generated_source_tail', 'source_tail_steps', 'source_steps',
    'generated_copy_end', 'copy_end_steps', 'copy_steps', 'execute')]
CLAIMS += [AIR + 'Loop.through_return', TEST + 'loop_return_specializes']
DEFINITION_NAMES = [MODEL + 'remainder']
DEFINITION_NAMES += [AIR + 'Finish.' + n for n in ('returned', 'body', 'preparedEnv')]
DEFINITION_NAMES += [AIR + 'Remainder.' + n for n in ('suffix', 'continuation', 'parameter', 'preparation', 'preparedEnv', 'headEnv')]
DEFINITION_NAMES += [AIR + 'Suffix.' + n for n in ('copy', 'skip', 'secondary', 'decision', 'guard', 'guardEnv', 'copyAt',
    'targetHead', 'targetEnv', 'targetTail', 'targetTailEnv', 'sourceHead', 'sourceEnv', 'sourceTail', 'sourceTailEnv', 'copyEnd')]
STATEMENT_NAMES = [AIR + n for n in ('size_sub', 'slice_construct', 'copy_bytes', 'Finish.body_steps',
    'Remainder.save_steps', 'Remainder.execute', 'Suffix.guard_steps', 'Suffix.copy_steps', 'Suffix.execute', 'Loop.through_return')]
# Reviewed exported terms are pinned before acceptance, never by the gate.
DEFINITIONS = {'Compiler.Extraction.WyhashUpdate.remainder': '6cd89aca15d4f96144cf37c24a433e247080f73e4ab68382477a1e734b1860fa',
 'Compiler.ZigAir.WyhashUpdateAir.Finish.returned': 'b55218412d8fbef4519cc30be4b2a949f94fc3c205437775293ee6dc16aa0835',
 'Compiler.ZigAir.WyhashUpdateAir.Finish.body': '0f03d26ef00d5ba205c4fc585ac8da57e78fdcc8d810749f2290000d4d2d73b9',
 'Compiler.ZigAir.WyhashUpdateAir.Finish.preparedEnv': '2d20889ed2064a62c6aab4df7d2dfd9c81fe12ba6c8f720da1dc8c6b73f1a2d8',
 'Compiler.ZigAir.WyhashUpdateAir.Remainder.suffix': '5d5d6aa54bddc64fb157ba2784329c2d00c3bca218e31122820d37db435a59d4',
 'Compiler.ZigAir.WyhashUpdateAir.Remainder.continuation': '89cbdde9a33547c78ac5d1f04c3db466819ed856d52f435ee1a3abfab9789ae0',
 'Compiler.ZigAir.WyhashUpdateAir.Remainder.parameter': 'ab22367a7571662de8a753419a3c49d5eb12aefc4822b6cd7d375ea2a4079856',
 'Compiler.ZigAir.WyhashUpdateAir.Remainder.preparation': '3553084c66229d37fe1cc2a318cc459ec9ddfd34c47373aa2525e0fe78ab1b2a',
 'Compiler.ZigAir.WyhashUpdateAir.Remainder.preparedEnv': '973f2bdeacd90b79f712aeb02456ccfdcc3329acd619a30025c75c503f5eb1ec',
 'Compiler.ZigAir.WyhashUpdateAir.Remainder.headEnv': '84774ebcde2a6687d4f08bf70f119f2dbee62b4f137d31c1126bf66843a8b8e9',
 'Compiler.ZigAir.WyhashUpdateAir.Suffix.copy': 'f6a0de3af0393912598eda0dd09bd3c21c8a1b6331eb7e2c9c49f22de8bc3328',
 'Compiler.ZigAir.WyhashUpdateAir.Suffix.skip': '9305845a02b824f04e25f68f2f87ecb7bebe26bf837e6134ddb67de74e6cc41a',
 'Compiler.ZigAir.WyhashUpdateAir.Suffix.secondary': '9405e83107be20619588ae2e83110a9808f563202b5834414a58a3ca79ae836f',
 'Compiler.ZigAir.WyhashUpdateAir.Suffix.decision': 'f67a9d6d71162902d08f19b81d904d8e9de1bf6f08ebaf83dfb6ddd24ca31696',
 'Compiler.ZigAir.WyhashUpdateAir.Suffix.guard': '18bb6727b8a6b4f9a5d0c23f5045c6e832d0063bfc78fc6889601fbeaf9154ea',
 'Compiler.ZigAir.WyhashUpdateAir.Suffix.guardEnv': '8040383236048ef0cd68be36d46fbfef31702da19641b84d47aaaae047cbd777',
 'Compiler.ZigAir.WyhashUpdateAir.Suffix.copyAt': 'c3139d9dc9a5c3800d081287bb78dc0d2918e0b4af2457b67ffb9d326dc0ba06',
 'Compiler.ZigAir.WyhashUpdateAir.Suffix.targetHead': '2b1a3c462e1bd85e0ef2e4065b301a0443878076fc90445b67a70195ff3e7d40',
 'Compiler.ZigAir.WyhashUpdateAir.Suffix.targetEnv': '9c2dd65273280184e99bece0f8ceace9d5c62a851a80114f8d3c0e1789cead95',
 'Compiler.ZigAir.WyhashUpdateAir.Suffix.targetTail': '970cdfda6471c8205eee51ff3e40b708756a306920bd95752c9521e0db8f5e75',
 'Compiler.ZigAir.WyhashUpdateAir.Suffix.targetTailEnv': '53d633afa00bf685713e12d926a2a5facb3ee21d6702d26347f43a6059120105',
 'Compiler.ZigAir.WyhashUpdateAir.Suffix.sourceHead': 'd821b19531176315f890c64b25bfdcec77d0919ec4751abaa9731e126d62a9a4',
 'Compiler.ZigAir.WyhashUpdateAir.Suffix.sourceEnv': 'ac8d437019f6d24f052d76a9cbea38135af12133ac6283f21c7659919346e2c9',
 'Compiler.ZigAir.WyhashUpdateAir.Suffix.sourceTail': '62823a55027f02718b2ab592c4606d8aaf20e82b13b97819d28ce397c7fbf966',
 'Compiler.ZigAir.WyhashUpdateAir.Suffix.sourceTailEnv': '3b4dfd58bee31bd8d9aef914dc815d9fc23d54ca8e3cae96b7dbe2ec77f1ae82',
 'Compiler.ZigAir.WyhashUpdateAir.Suffix.copyEnd': 'fc5bb22a6bd59943f77d8e32ac980bb71c2d2970c33679351430f7775cd2f218'}
STATEMENTS = {'Compiler.ZigAir.WyhashUpdateAir.size_sub': '1a9ce0e1c0d28eb650ad08a25e5fd7c7288eede8ec51dd954e0523afc1d8a260',
 'Compiler.ZigAir.WyhashUpdateAir.slice_construct': '7b2765cb710e04c82a6657bc8df174aacbeb76045c6d68eeb7096acac78665d8',
 'Compiler.ZigAir.WyhashUpdateAir.copy_bytes': '2904de6676ca047a8e5aed619c0a22dbe8b61ad9e052a33f970336a0c935713c',
 'Compiler.ZigAir.WyhashUpdateAir.Finish.body_steps': 'cfa93800ea8ae326a7db0c145fa28e53ee240a753108f6c31f569332d6e52250',
 'Compiler.ZigAir.WyhashUpdateAir.Remainder.save_steps': 'e45c8a33105d8f04443ff650ed30e933d9677dd8b29fc314b9a1f913b134cb71',
 'Compiler.ZigAir.WyhashUpdateAir.Remainder.execute': '8e4849b64723a26c2e4ed222319ec0f4c95d0e802671fb46cdc0058c0094d875',
 'Compiler.ZigAir.WyhashUpdateAir.Suffix.guard_steps': '01183b1b159fb0d57ec64bdfb6fa1b2a84c483c11523e6d6aafde6f752156b0c',
 'Compiler.ZigAir.WyhashUpdateAir.Suffix.copy_steps': '2315cfc12b344d560a639a9bd83a0dcdd3d489845db6f62ce33e457aaf376a0c',
 'Compiler.ZigAir.WyhashUpdateAir.Suffix.execute': '155857372e748f7f997c0c86ab30b9493dd9bde48df3a71f3f0d601d4770874b',
 'Compiler.ZigAir.WyhashUpdateAir.Loop.through_return': '24074fe8039acd0bada1355299fabe28f13134c63560704bd22d73c4c21ad93e'}


def audit(rows, encoded_digest, require):
    indexed = {row['theorem']: row for row in rows}
    require(set(STATEMENTS) == set(STATEMENT_NAMES), 'incomplete native tail statement pins')
    for name, expected in STATEMENTS.items():
        require(encoded_digest(indexed[name]['statement']) == expected, 'native tail statement changed: ' + name)
    for name in CLAIMS:
        if not name.startswith(TEST):
            require(not any('Tests' in d for d in indexed[name]['dependencies']), 'native tail depends on fixtures')
    required = {
        AIR + 'copy_bytes': {AIR + 'copy_buffer'},
        AIR + 'Finish.body_steps': {AIR + 'Finish.prepare_steps', AIR + 'Finish.copy_return_steps', AIR + 'Finish.return_steps', AIR + 'copy_bytes'},
        AIR + 'Remainder.save_steps': {AIR + 'Remainder.prepare_steps', 'Compiler.ZigAir.AggregateCall.ReadonlyParameter.steps'},
        AIR + 'Suffix.copy_steps': {AIR + 'Suffix.target_steps', AIR + 'Suffix.source_steps', AIR + 'Suffix.copy_end_steps', AIR + 'copy_bytes'},
        AIR + 'Suffix.execute': {AIR + 'Suffix.guard_steps', AIR + 'Suffix.copy_steps'},
        AIR + 'Remainder.execute': {AIR + 'Remainder.save_steps', AIR + 'Suffix.execute', AIR + 'Finish.body_steps',
                                  AIR + 'end_bound', MEMORY + 'StackFrame.install_old', MODEL + 'remainder'},
        AIR + 'Loop.through_return': {AIR + 'Loop.entry_steps', AIR + 'Remainder.execute', AIR + 'Loop.At.updated'},
        TEST + 'loop_return_specializes': {AIR + 'Loop.through_return', TEST + 'loop_admitted'},
    }
    for name, dependencies in required.items():
        require(dependencies <= set(indexed[name]['dependencies']), 'native tail composition bypassed: ' + name)
    return {'checkedStatements': list(STATEMENTS), 'checkedDependencies': sorted(required),
            'nativeLoopThroughReturnVerified': True, 'retainedSuffixRefinementVerified': True,
            'finalCopyLengthReturnVerified': True, 'remainingDescriptorAllocationVerified': True,
            'partialOomWritesRetained': True, 'originalInputAndRootAdmissionRequired': True,
            'scope': 'loop-through-return; complete invocation audited separately', 'consumedByLookupPublication': False,
            'connectionsOutsideThisAudit': ['fill-copy-and-index-admission', 'fill-length-reset',
                                           'whole-update-entry-and-cleanup', 'hash-runner-consumption']}


def controls(output, env, lean):
    records = []
    groups = (
        ('suffix-guard', 'WyhashUpdateAirSuffixGuard', 'WyhashUpdateAirRemainder', (
            ('non-strict-short-tail', '.comparison .lt (.local 598)', '.comparison .le (.local 598)'),
            ('strict-prior-block', '.comparison .ge (.local 603)', '.comparison .gt (.local 603)'),
        )),
        ('suffix-source', 'WyhashUpdateAirSuffixSource', 'WyhashUpdateAirSuffixTarget', (
            ('wrong-source-offset', '.offsetPointer false (.local 623) (.local 620)', '.offsetPointer false (.local 623) (.local 619)'),
            ('unadmitted-source', '(reads : ByteRange.Reads state address count bytes)', '(reads : ByteRange.Reads state address 0 bytes)'),
        )),
        ('update-finish', 'WyhashUpdateAirFinish', 'WyhashUpdateAirSlices', (
            ('wrong-length-store', '.store (.local 647) (.local 649)', '.store (.local 647) (.constant (.value (.scalar (.int false 64 0))))'),
            ('oversized-buffer', '(bounded : count ≤ 48)', '(bounded : count ≤ 49)'),
        )),
        ('loop-return', 'WyhashUpdateAirLongExecution', 'WyhashUpdateAirRemainderExecution', (
            ('discard-failed-writes', 'StackFrame (ctx.frame.install failedCells) after', 'StackFrame (ctx.frame.install cells) after'),
            ('discard-returned-writes', 'StackFrame (ctx.frame.install finalCells) after', 'StackFrame (ctx.frame.install cells) after'),
        )),
    )
    for label, module, imports, edits in groups:
        source = without_imports((ROOT / f'lean/Compiler/ZigAir/{module}.lean').read_text())
        prefix = 'import Compiler.ZigAir.' + imports + '\n'
        records.append(mutation_check(output, label + '-unchanged', prefix + source, True, env, lean))
        for name, before, after in edits:
            if before not in source:
                raise ValueError('missing native tail mutation site: ' + name)
            mutated = source.replace(before, after)
            # Compare the complete captured code before attempting later proofs
            # about intentionally changed instructions. Those later applications
            # can exhaust elaborator recursion instead of rejecting semantically.
            if label == 'suffix-guard':
                mutated = mutated.split('theorem generated_guard', 1)[0]
                mutated += '\nend Compiler.ZigAir.WyhashUpdateAir.Suffix\n'
                mutated += kernel_rejection(AIR + 'Remainder.suffix = ' + AIR + 'Suffix.guard')
            elif name == 'wrong-source-offset':
                mutated = mutated.split('theorem generated_source_head', 1)[0]
                mutated += '\nend Compiler.ZigAir.WyhashUpdateAir.Suffix\n'
                mutated += kernel_rejection(AIR + 'Suffix.copyAt 13 = ' + AIR + 'Suffix.sourceHead')
            records.append(mutation_check(output, label + '-' + name, prefix + mutated, False, env, lean))
    return checked_controls(output, records)
