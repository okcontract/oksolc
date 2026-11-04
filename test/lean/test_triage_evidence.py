#!/usr/bin/env python3
"""
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""
import gzip
import hashlib
import io
import json
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
import tempfile
import unittest
from triage_evidence import cached_triage, main, triage
from unittest.mock import patch


class TriageTests(unittest.TestCase):
    def inspect(self, data, *, name='checks.json.gz', **limits):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary)/name
            raw = json.dumps(data).encode() if '.json' in name else data.encode()
            path.write_bytes(gzip.compress(raw, mtime=0) if name.endswith('.gz') else raw)
            before = hashlib.sha256(path.read_bytes()).hexdigest()
            result = triage([path], **limits)
            self.assertEqual(before, hashlib.sha256(path.read_bytes()).hexdigest())
            return result

    def test_deduplication_and_bounded_display_retain_counts(self):
        result = self.inspect([{'severity': 'warning', 'message': 'a'*300}]*5+
                              [{'severity': 'error', 'message': 'different'}], max_items=1, max_chars=80)
        self.assertEqual(result['counts'], {'warning': 5, 'error': 1})
        self.assertEqual(result['omittedSignalGroups'], 1)
        self.assertEqual(result['signals'][0]['level'], 'error')

    def test_expected_revert_is_not_a_failed_comparison(self):
        outcome = {'kind': 'revert', 'data': '1234'}
        result = self.inspect({'case': {'expected': outcome}, 'result': outcome})
        self.assertEqual(result['uniqueSignals'], 0)

    def test_raw_payload_mismatch_is_preserved(self):
        result = self.inspect({'case': {'expected': {'kind': 'revert', 'data': '1234'}},
                               'result': {'kind': 'revert', 'data': '123400'}})
        self.assertEqual(result['signals'][0]['kind'], 'observation-mismatch')
        self.assertIn('123400', result['signals'][0]['message'])

    def test_mismatch_skips_large_equal_fields_to_name_the_different_field(self):
        shared = '00'*100000
        expected = {'aBytecode': shared, 'effects': {'logs': [{'data': '1234'}], 'storage': [0]}}
        actual = {**expected, 'effects': {'logs': [{'data': '123400'}], 'storage': [1]}}
        result = self.inspect({'expected': expected, 'actual': actual}, max_chars=240)
        signal = result['signals'][0]
        self.assertIn('first difference at "/effects/logs/0/data"', signal['message'])
        self.assertIn('123400', signal['message'])
        self.assertNotIn('aBytecode', signal['message'])
        self.assertFalse(signal['messageTruncated'])
        pair = json.dumps([expected, actual], sort_keys=True, separators=(',', ':')).encode('ascii')
        self.assertEqual(signal['comparisonSha256'], hashlib.sha256(pair).hexdigest())
        self.assertLess(len(json.dumps(result)), 1500)

    def test_long_string_mismatch_selects_the_changed_tail_not_the_prefix(self):
        prefix = '00'*100000
        result = self.inspect({'expected': {'data': prefix+'aa'}, 'actual': {'data': prefix+'bb'}})
        message = result['signals'][0]['message']
        self.assertIn('"/data" (character 200000)', message)
        self.assertIn('[199992:200002]="00000000aa"', message)
        self.assertIn('[199992:200002]="00000000bb"', message)
        self.assertFalse(result['signals'][0]['messageTruncated'])
        result = self.inspect({'expected': prefix, 'actual': prefix+'00'})
        self.assertIn('first difference at "" (character 200000)', result['signals'][0]['message'])
        self.assertIn('string(200002 chars)', result['signals'][0]['message'])

    def test_same_first_difference_does_not_merge_distinct_comparison_pairs(self):
        first = {'expected': {'a': 1, 'z': 1}, 'actual': {'a': 2, 'z': 2}}
        second = {'expected': {'a': 1, 'z': 1}, 'actual': {'a': 2, 'z': 3}}
        result = self.inspect([first, first, second], max_items=2)
        self.assertEqual(result['counts'], {'error': 3})
        self.assertEqual(result['uniqueSignals'], 2)
        self.assertEqual([s['count'] for s in result['signals']], [2, 1])
        self.assertEqual(len({s['message'] for s in result['signals']}), 1)
        self.assertEqual(len({s['comparisonSha256'] for s in result['signals']}), 2)
        limited = self.inspect([first, second], max_items=1)
        self.assertEqual(limited['omittedSignalGroups'], 1)

    def test_mismatch_missing_values_are_not_null_or_empty_values(self):
        for expected, actual, pointer in (({}, {'x': None}, '/x'), ([], [None], '/0'),
                                          ([1, 2], [1, 2, []], '/2')):
            forward = self.inspect({'expected': expected, 'actual': actual})['signals'][0]['message']
            backward = self.inspect({'expected': actual, 'actual': expected})['signals'][0]['message']
            self.assertIn(json.dumps(pointer), forward)
            self.assertIn('expected=<missing>', forward)
            self.assertIn('actual=<missing>', backward)
        result = self.inspect({'expected': {}, 'actual': {'x': None}})
        self.assertIn('actual=null', result['signals'][0]['message'])

    def test_mismatch_path_is_sorted_escaped_and_insertion_order_independent(self):
        expected = {'z': 1, 'a/~': {'': [False, 0]}}
        actual = {'a/~': {'': [False, 1]}, 'z': 2}
        first = self.inspect({'expected': expected, 'actual': actual})['signals'][0]
        second = self.inspect({'expected': dict(reversed(list(expected.items()))),
                               'actual': dict(reversed(list(actual.items())))})['signals'][0]
        self.assertIn('"/a~1~0//1"', first['message'])
        self.assertEqual(first['message'], second['message'])
        self.assertEqual(first['comparisonSha256'], second['comparisonSha256'])

    def test_structural_mismatch_never_dumps_nested_payloads(self):
        result = self.inspect({'expected': {'large': ['x'*100000]}, 'actual': ['y'*100000]})
        message = result['signals'][0]['message']
        self.assertIn('expected=object(1 fields) actual=array(1 items)', message)
        self.assertFalse(result['signals'][0]['messageTruncated'])

    def test_long_paths_and_unicode_mismatch_windows_remain_bounded(self):
        for expected, actual in (({'x'*10000: 0}, {'x'*10000: 1}),
                                  ('\u2603'*100000+'a', '\u2603'*100000+'b')):
            signal = self.inspect({'expected': expected, 'actual': actual}, max_chars=80)['signals'][0]
            self.assertTrue(signal['messageTruncated'])
            self.assertEqual(len(signal['message']), 80)
            self.assertEqual(len(signal['comparisonSha256']), 64)

    def test_equal_structured_observations_keep_fast_native_comparison(self):
        value = {'payload': 'ff'*100000, 'rows': list(range(10000)), 'logs': [], 'storage': None}
        with patch('triage_evidence.comparison_digest', side_effect=AssertionError('no mismatch digest needed')):
            result = self.inspect({'case': {'expected': value}, 'result': value})
        self.assertEqual(result['uniqueSignals'], 0)

    def test_embedded_compiler_diagnostics_not_source_keywords(self):
        result = self.inspect({'Contract.sol': 'error E();', 'compiler-output.json': json.dumps({
            'errors': [{'severity': 'warning', 'message': 'unused variable'}]})})
        self.assertEqual(result['counts'], {'warning': 1})

    def test_json_filenames_in_hash_manifests_are_not_embedded_json(self):
        result = self.inspect({'inputHashes': {'library.json': 'a'*64, 'profiles.json': '1'*64}})
        self.assertEqual(result['uniqueSignals'], 0)

    def test_limits_and_corrupt_json_fail_explicitly(self):
        result = self.inspect({'data': 'a'*400}, max_bytes=80)
        self.assertFalse(result['files'][0]['inspected'])
        self.assertEqual(result['signals'][0]['kind'], 'input-not-inspected')
        result = self.inspect({'broken.json': '{'})
        self.assertEqual(result['signals'][0]['kind'], 'embedded-json')

    def test_logs_are_signals_not_acceptance_decisions(self):
        result = self.inspect('warning: repeated\nwarning: repeated\nAssertionError: failed\nBuild Summary: 4/4 steps succeeded; 217/217 tests passed\n', name='test.log.gz')
        self.assertEqual(result['counts'], {'warning': 2, 'error': 1})
        self.assertEqual(len(result['completions']), 1)

    def test_admission_diagnostics_and_explicit_error_are_not_lost(self):
        result = self.inspect({'status': 'unsupported', 'diagnostics': [
            {'capability': 'recursive-call-profile', 'message': 'unsupported profile'}], 'error': 'invalid configuration'})
        self.assertEqual(result['counts'], {'warning': 2, 'error': 1})
        self.assertEqual({row['kind'] for row in result['signals']}, {'status', 'admission-diagnostic', 'reported-error'})

    def test_operation_hints_prioritize_bounded_children_without_hiding_scope(self):
        hint = {'operation': 'assignment', 'reason': 'conditional-pointer-class-change',
                'coordinateSpace': 'source', 'start': 1024, 'length': 7,
                'source': {'file': 'src/A.sol', 'line': 42, 'excerpt': 'p:=data'}}
        result = self.inspect({'schema': 'oksolc.chainwall.coverage-summary.v1',
            'scope': {'kind': 'declared-subset', 'omittedSourceFiles': 267}, 'sourceFiles': 1,
            'operationHints': [hint, hint], 'roots': [{'root': 'A', 'diagnosticStatus': 'unsupported'}]}, max_items=2)
        self.assertEqual(result['counts'], {'warning': 4})
        self.assertEqual(result['omittedSignalGroups'], 1)
        self.assertEqual([s['kind'] for s in result['signals']], ['coverage-scope', 'operation-hint'])
        self.assertIn('src/A.sol:42; p:=data', result['signals'][1]['message'])
        self.assertEqual(result['signals'][1]['count'], 2)
        result = self.inspect({'operationHints': [{**hint, 'reason': 'x'*500}]}, max_chars=80)
        self.assertTrue(result['signals'][0]['messageTruncated'])
        self.assertEqual(len(result['signals'][0]['message']), 80)

    def test_raw_and_legacy_hints_remain_signals_not_source_remappings(self):
        for space in ('source', 'inline-operations'):
            result = self.inspect({'diagnostics': [{'capability': 'assembly-memory-call', 'message': 'retained',
                'source': {'file': 'src/A.sol', 'line': 99}, 'hint': {'operation': 'assignment', 'reason': 'reason',
                'coordinateSpace': space, 'start': 2, 'length': 7}}]})
            hint = next(s for s in result['signals'] if s['kind'] == 'operation-hint')
            self.assertIn(space+' bytes 2 length 7', hint['message'])
            self.assertEqual('src/A.sol' in hint['message'], space == 'source')
            self.assertNotIn(':99', hint['message'])
        result = self.inspect({'operationHints': [None], 'error': 'other failure'})
        self.assertEqual(result['counts'], {'warning': 1, 'error': 1})

    def test_source_error_precedes_repeated_build_scaffolding(self):
        result = self.inspect('transitive failure\n'*20+
                              'src/rule.zig:15:68: error: incompatible types\n'+
                              'error: 1 compilation errors\n', name='build.log', max_items=1)
        self.assertEqual(result['counts'], {'error': 22})
        self.assertEqual(result['signals'][0]['kind'], 'compiler-diagnostic')
        self.assertEqual(result['omittedSignalGroups'], 2)

    def test_malformed_coverage_fields_do_not_abort_other_diagnostics(self):
        result = self.inspect({'schema': 'oksolc.chainwall.coverage-summary.v1', 'scope': [],
            'roots': [{'root': 'A', 'diagnosticStatus': 'unsupported', 'capabilities': None},
                      {'root': 'B', 'diagnosticStatus': 'inspection-failed', 'failure': 9}]})
        self.assertEqual(result['counts'], {'error': 2, 'warning': 1})
        self.assertIn('coverage-summary', {row['kind'] for row in result['signals']})

    def test_completion_omissions_are_explicit(self):
        result = self.inspect('Build Summary: 4/4 steps succeeded\n'*15, name='build.log')
        self.assertEqual(len(result['completions']), 12)
        self.assertEqual(result['completionCount'], 15)
        self.assertEqual(result['omittedCompletions'], 3)

    def test_backend_rejection_keeps_request_out_of_diagnostic_context(self):
        result = self.inspect({'status':'rejected', 'reason':'BackendRejectedCandidate',
            'backendRejection':{'accepted':False, 'requestSha256':'a'*64,
                'request':{'sources':{'X.yul':{'content':'error false_source_signal\n'*100000}}},
                'response':{'errors':[{'severity':'error','message':'StackTooDeep'}]}}}, max_items=2)
        self.assertTrue(all(f['inspected'] for f in result['files']))
        self.assertTrue(any('StackTooDeep' in s['message'] for s in result['signals']))
        self.assertEqual(result['counts']['error'], 1)
        self.assertEqual(result['omittedSignalGroups'], 0)
        self.assertFalse(any('false_source_signal' in s['message'] for s in result['signals']))

    def test_completion_limits_do_not_hide_diagnostics_or_totals(self):
        for limit in (0, 1, 2, 100):
            result = self.inspect('Build Summary: 4/4 steps succeeded\n'*15+
                                  'error: real failure\nwarning: real warning\n',
                                  name='build.log', max_completions=limit, max_items=1)
            self.assertEqual(len(result['completions']), min(limit, 15))
            self.assertEqual(result['completionCount'], 15)
            self.assertEqual(result['omittedCompletions'], max(0, 15-limit))
            self.assertEqual(result['counts'], {'error': 1, 'warning': 1})
            self.assertEqual(result['signals'][0]['level'], 'error')
            self.assertEqual(result['omittedSignalGroups'], 1)

    def test_failed_expectation_precedes_repeated_source_excerpts(self):
        result = self.inspect('    return error.Unsupported;\n'*20+
                              'expected error.Unsupported, found error.InvalidResolvedView\n', name='test.log', max_items=1)
        self.assertEqual(result['signals'][0]['kind'], 'test-failure')
        self.assertEqual(result['counts'], {'error': 21})
        result = self.inspect('failed command: zig test\n', name='test.log')
        self.assertEqual(result['signals'][0]['kind'], 'log-signal')

    def test_exception_and_warning_classification(self):
        result = self.inspect('Traceback (most recent call last):\nValueError: bad input\n'+
                              'src/warnings.zig:2: warning: unused error handler\n', name='build.log', max_items=2)
        self.assertEqual(result['signals'][0]['kind'], 'log-exception')
        self.assertEqual(result['counts'], {'error': 2, 'warning': 1})

    def test_lean_diagnostic_ids_precede_proof_output(self):
        result = self.inspect('    Except.error Fault.resourceLimit\n'*20+
                              'Tests/Flow.lean:50:53: error(lean.synthInstanceFailed): missing instance\n',
                              name='lean.log', max_items=1)
        self.assertEqual(result['signals'][0]['kind'], 'compiler-diagnostic')
        self.assertIn('missing instance', result['signals'][0]['message'])
        self.assertEqual(result['counts'], {'error': 21})
        self.assertEqual(result['omittedSignalGroups'], 1)
        result = self.inspect('Tests/Flow.lean:7: warning(lean.unusedVariables): unused error\n', name='lean.log')
        self.assertEqual(result['signals'][0]['level'], 'warning')

    def test_lean_uncaught_exception_precedes_proof_output(self):
        result = self.inspect('    Except.error Fault.resourceLimit\n'*20+
                              'uncaught exception: result/control changed\n', name='lean.log', max_items=1)
        self.assertEqual(result['signals'][0]['kind'], 'log-exception')
        self.assertIn('result/control changed', result['signals'][0]['message'])
        self.assertEqual(result['counts'], {'error': 21})
        self.assertEqual(result['omittedSignalGroups'], 1)

    def test_lean_completion_summaries_are_not_acceptance(self):
        result = self.inspect('Build completed successfully (232 jobs).\n'+
                              'Result defaults: 833 checks passed (finite checks).\n', name='lean.log')
        self.assertEqual(result['completionCount'], 2)
        self.assertEqual(result['uniqueSignals'], 0)

    def test_wrapped_tool_streams_surface_compiler_errors_and_keep_wrapper(self):
        diagnostic = 'error: Generated/C.lean:193:99: Unknown constant `Contract.Interaction.Op.mul`\n'
        wrapper = 'RuntimeError: (PosixPath('+repr('/long/'*100)+'), '+repr({
            'toolDiagnostics': {'stdout': diagnostic*2, 'stderr': 'error: build failed\n'}})+')\n'
        result = self.inspect(wrapper, name='wrapped.log', max_items=1)
        self.assertEqual(result['signals'][0]['kind'], 'compiler-diagnostic')
        self.assertIn('Unknown constant', result['signals'][0]['message'])
        self.assertEqual(result['signals'][0]['count'], 2)
        self.assertEqual(result['counts'], {'error': 4})  # wrapper and stderr remain.
        self.assertEqual(result['omittedSignalGroups'], 2)

    def test_wrapped_json_and_python_string_quoting(self):
        diagnostic = "warning: Generated/C.lean:2:7: unused 'error' handler\x1b\n"
        for encode in (repr, json.dumps):
            result = self.inspect('RuntimeError: '+encode({'stdout': diagnostic})+'\n', name='wrapped.log')
            compiler = [r for r in result['signals'] if r['kind'] == 'compiler-diagnostic']
            self.assertEqual(len(compiler), 1)
            self.assertEqual(compiler[0]['level'], 'warning')
            self.assertEqual(result['counts'], {'error': 1, 'warning': 1})
        result = self.inspect({'toolDiagnostics': {'stdout': diagnostic}})
        self.assertEqual(result['counts'], {'warning': 1})

    def test_embedded_streams_never_evaluate_expressions(self):
        expression = "RuntimeError: {'stdout': __import__('os').system('do-not-run')}\n"
        with patch('os.system', side_effect=AssertionError('must not execute')):
            result = self.inspect(expression, name='wrapped.log')
        self.assertIn('not inspected', result['signals'][0]['message'])
        self.assertEqual(result['signals'][0]['kind'], 'embedded-log')
        result = self.inspect("RuntimeError: {'stdout': 'bad\\xZZ'}\n", name='wrapped.log')
        self.assertEqual(result['signals'][0]['kind'], 'embedded-log')

    def test_embedded_stream_limits_are_explicit(self):
        with patch('triage_evidence.MAX_EMBEDDED_LOG_CHARS', 16):
            result = self.inspect('RuntimeError: '+repr({'stdout': 'x'*17})+'\n', name='wrapped.log')
        self.assertIn('oversized', result['signals'][0]['message'])
        with patch('triage_evidence.MAX_EMBEDDED_STREAMS', 1):
            result = self.inspect('RuntimeError: '+repr({'stdout': '', 'stderr': ''})+'\n', name='wrapped.log')
        self.assertIn('exceed limit', result['signals'][0]['message'])
        nested = 'RuntimeError: '+repr({'stdout': 'error: hidden'})
        result = self.inspect('RuntimeError: '+repr({'stdout': nested})+'\n', name='wrapped.log')
        self.assertIn('depth limit', result['signals'][0]['message'])

    def test_json_stdout_extracts_diagnostics_without_scanning_source_strings(self):
        response = {'status': 'rejected', 'toolDiagnostics': {
            'stdout': 'error: Generated/C.lean:6439:4: maximum recursion depth\n',
            'stderr': 'warning: Generated/C.lean:2:1: unused variable\n'},
            'sources': {'C.lean': 'Except.error Fault.resourceLimit\n'*2000},
            'bytecode': 'ff'*100000, 'backendDiagnostics': [
                {'severity': 'error', 'message': 'Yul code generation failed: StackTooDeep'}]}
        result = self.inspect({'exitCode': 1, 'stdout': json.dumps(response), 'stderr': ''}, max_items=2)
        self.assertTrue(result['files'][0]['inspected'])
        self.assertEqual(result['counts'], {'error': 3, 'warning': 2})
        self.assertEqual(result['omittedSignalGroups'], 3)
        self.assertEqual({s['kind'] for s in result['signals']}, {'compiler-diagnostic', 'diagnostic'})
        self.assertTrue(all('.stdout.' in s['firstLocation'] for s in result['signals']))
        self.assertFalse(any('Except.error' in s['message'] for s in result['signals']))

    def test_json_wrapped_streams_retain_failures_warnings_and_completions(self):
        response = {'passed': False, 'toolDiagnostics': {'stdout': 'Build Summary: 1/1 steps succeeded\n'},
                    'diagnostics': [{'severity': 'warning', 'message': 'retained'}]}
        for value in (response, [response]):
            for encode in (repr, json.dumps):
                result = self.inspect('RuntimeError: '+encode({'stdout': json.dumps(value)})+'\n', name='wrapped.log')
                self.assertEqual(result['counts'], {'error': 2, 'warning': 1})
                self.assertEqual(result['completionCount'], 1)
                self.assertTrue(result['files'][0]['inspected'])

    def test_ordinary_stream_text_and_foundry_tags_stay_logs(self):
        for field in ('stdout', 'stderr', 'log', 'traceback', 'run.log'):
            result = self.inspect({field: '[PASS] testOkay()\n[FAIL] testBad()\n[FAIL: Revert] testOther()\nerror: failed\n'})
            self.assertTrue(result['files'][0]['inspected'])
            self.assertEqual(result['counts'], {'error': 3})
            self.assertEqual(result['signals'][0]['kind'], 'test-failure')
            self.assertEqual({s['kind'] for s in result['signals']}, {'test-failure', 'log-signal'})

    def test_malformed_json_stream_reports_partial_inspection_and_keeps_text_signals(self):
        result = self.inspect({'stdout': '{"broken":\nerror: Generated/C.lean:3:4: retained error\n'})
        self.assertFalse(result['files'][0]['inspected'])
        self.assertEqual({s['kind'] for s in result['signals']}, {'embedded-json', 'compiler-diagnostic'})

    def test_embedded_json_cumulative_budgets_reset_per_file(self):
        document = json.dumps({'passed': False})
        with patch('triage_evidence.MAX_EMBEDDED_JSON_CHARS', len(document)):
            result = self.inspect({'stdout': document, 'stderr': document})
        self.assertFalse(result['files'][0]['inspected'])
        self.assertEqual({s['kind'] for s in result['signals']}, {'embedded-json', 'failed-check'})
        with patch('triage_evidence.MAX_EMBEDDED_JSON_DOCUMENTS', 1):
            result = self.inspect({'stdout': document, 'other.json': document})
            with tempfile.TemporaryDirectory() as temporary:
                paths = [Path(temporary)/name for name in ('a.json', 'b.json')]
                for path in paths: path.write_text(json.dumps({'stdout': document}))
                independent = triage(paths)
        self.assertFalse(result['files'][0]['inspected'])
        self.assertTrue(all(f['inspected'] for f in independent['files']))
        self.assertEqual(independent['counts'], {'error': 2})

    def test_embedded_json_depth_and_long_log_limits_are_visible(self):
        response = {'passed': False}
        for _ in range(4): response = {'stdout': json.dumps(response)}
        result = self.inspect(response)
        self.assertTrue(result['files'][0]['inspected'])
        self.assertEqual(result['signals'][0]['kind'], 'failed-check')
        response = {'stdout': json.dumps(response)}
        result = self.inspect(response)
        self.assertFalse(result['files'][0]['inspected'])
        self.assertEqual(result['signals'][0]['kind'], 'embedded-json')
        self.assertIn('depth budget exceeded (5 > 4)', result['signals'][0]['message'])
        with patch('triage_evidence.MAX_LOG_LINE_CHARS', 80):
            result = self.inspect({'stdout': 'f'*81+'\nwarning: still inspected\n'})
        self.assertFalse(result['files'][0]['inspected'])
        self.assertEqual(result['counts'], {'error': 1, 'warning': 1})
        self.assertEqual(result['signals'][0]['kind'], 'log-line-limit')

    def test_json_stream_never_evaluates_embedded_expressions(self):
        with patch('os.system', side_effect=AssertionError('must not execute')):
            result = self.inspect({'stdout': '{"stdout": __import__("os").system("do-not-run")}'})
        self.assertFalse(result['files'][0]['inspected'])
        self.assertEqual(result['signals'][0]['kind'], 'embedded-json')

    def test_long_single_token_before_diagnostic_does_not_obscure_location(self):
        result = self.inspect('f'*100000+' C.lean:3:4: error: retained\n', name='build.log')
        self.assertEqual(result['signals'][0]['kind'], 'compiler-diagnostic')
        self.assertTrue(result['files'][0]['inspected'])

    def test_scoped_coverage_index_keeps_omissions_and_failed_roots(self):
        result = self.inspect({'schema': 'oksolc.chainwall.coverage-summary.v1', 'sourceFiles': 1,
            'scope': {'kind': 'declared-subset', 'omittedSourceFiles': 173}, 'roots': [
                {'root': 'src/A.sol:A', 'diagnosticStatus': 'candidate-only'},
                {'root': 'src/A.sol:B', 'diagnosticStatus': 'unsupported', 'capabilities': ['assembly-memory-call']},
                {'root': 'src/A.sol:C', 'diagnosticStatus': 'inspection-failed', 'failure': 'invalid reference'},
                {'root': 'src/A.sol:D', 'diagnosticStatus': 'inconclusive-resource-limit', 'failure': 'timeout'},
                {'root': 'src/A.sol:I', 'diagnosticStatus': 'dependency-only'},
            ]}, max_items=2)
        self.assertEqual(result['counts'], {'error': 1, 'warning': 3})
        self.assertIn('inspection-failed', result['signals'][0]['message'])
        self.assertEqual(result['signals'][1]['kind'], 'coverage-scope')
        self.assertIn('173 source units omitted', result['signals'][1]['message'])
        self.assertEqual(result['omittedSignalGroups'], 2)


class CacheTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.source = self.root/'run.json.gz'
        self.cache = self.root/'cache'
        self.source.write_bytes(gzip.compress(json.dumps({'severity': 'error', 'message': 'actual failure'}).encode(), mtime=0))
        self.original = self.source.read_bytes()

    def inspect(self, **limits):
        return cached_triage([self.source], self.cache, **limits)

    def test_hit_reuses_view_but_binds_raw_compressed_bytes(self):
        first = self.inspect(max_items=2)
        self.assertEqual(first['cache']['status'], 'miss')
        with patch('triage_evidence.triage', side_effect=AssertionError('unchanged evidence reparsed')):
            second = self.inspect(max_items=2)
        self.assertEqual(second['cache']['status'], 'hit')
        self.assertEqual(first['signals'], second['signals'])
        self.assertEqual(second['cache']['inputs'][0]['sha256'], hashlib.sha256(self.original).hexdigest())
        self.assertEqual(self.source.read_bytes(), self.original)

    def test_changed_inputs_or_limits_invalidate_cache(self):
        first = self.inspect(max_items=1)
        limited = self.inspect(max_items=2)
        self.assertEqual(limited['cache']['status'], 'miss')
        self.assertNotEqual(first['cache']['key'], limited['cache']['key'])
        self.source.write_bytes(gzip.compress(b'{"passed":false}', mtime=0))
        changed = self.inspect(max_items=1)
        self.assertEqual(changed['cache']['status'], 'miss')
        self.assertEqual(changed['signals'][0]['kind'], 'failed-check')
        self.assertNotEqual(first['cache']['key'], changed['cache']['key'])

    def test_changed_tool_invalidates_cache(self):
        first = self.inspect()
        tool = self.root/'updated-tool.py'
        tool.write_text('changed tool identity')
        with patch('triage_evidence.__file__', str(tool)):
            changed = self.inspect()
        self.assertEqual(changed['cache']['status'], 'miss')
        self.assertNotEqual(first['cache']['key'], changed['cache']['key'])

    def test_completion_limits_bind_cached_views(self):
        self.source.write_bytes(gzip.compress(json.dumps({'stderr': 'Build Summary: done\n'*3,
                                                        'passed': False}).encode(), mtime=0))
        first = self.inspect(max_completions=2)
        changed = self.inspect(max_completions=0)
        self.assertEqual(len(first['completions']), 2)
        self.assertEqual(changed['completions'], [])
        self.assertEqual(changed['completionCount'], 3)
        self.assertEqual(changed['omittedCompletions'], 3)
        self.assertEqual(first['signals'], changed['signals'])
        self.assertNotEqual(first['cache']['key'], changed['cache']['key'])
        self.assertEqual(self.inspect(max_completions=0)['cache']['status'], 'hit')

    def test_corrupt_or_mismatched_entry_is_rebuilt(self):
        first = self.inspect()
        entry = self.cache/(first['cache']['key']+'.json')
        original = entry.read_bytes()
        for kind in ('json', 'identity', 'result', 'oversized'):
            data = json.loads(original)
            if kind == 'identity': data['identity']['toolSha256'] = 'bad'
            if kind == 'result': data['result']['signals'] = []
            entry.write_bytes(b'{' if kind == 'json' else b' '* (8*1024*1024+1) if kind == 'oversized' else json.dumps(data).encode())
            rebuilt = self.inspect()
            self.assertEqual(rebuilt['cache']['status'], 'rebuilt', kind)
            self.assertEqual(rebuilt['signals'], first['signals'], kind)
        self.assertEqual(self.source.read_bytes(), self.original)

    def test_bad_cache_location_does_not_hide_evidence(self):
        self.cache.write_text('not a directory')
        result = self.inspect()
        self.assertEqual(result['cache']['status'], 'not-saved')
        self.assertEqual(result['signals'][0]['message'], 'actual failure')
        self.assertTrue(result['files'][0]['inspected'])

    def test_unreadable_or_over_limit_inputs_are_not_cached(self):
        result = self.inspect(max_bytes=1)
        self.assertFalse(result['files'][0]['inspected'])
        self.assertFalse(self.cache.exists())
        self.source.unlink()
        result = self.inspect()
        self.assertEqual(result['cache']['status'], 'unavailable')
        self.assertEqual(result['signals'][0]['kind'], 'input-not-inspected')

    def test_growing_log_is_explicitly_unbound_and_not_cached(self):
        def growing(paths, **limits):
            result = triage(paths, **limits)
            self.source.write_bytes(gzip.compress(b'{"passed":false}', mtime=0))
            return result
        with patch('triage_evidence.triage', side_effect=growing):
            result = self.inspect()
        self.assertEqual(result['cache']['status'], 'input-changed')
        self.assertNotIn('inputs', result['cache'])
        self.assertFalse(self.cache.exists())

    def test_input_change_during_cache_hit_reinspects_instead_of_returning_stale_view(self):
        first = self.inspect()
        entry = self.cache/(first['cache']['key']+'.json')
        original_open = Path.open
        def changing_open(path, *args, **kwargs):
            stream = original_open(path, *args, **kwargs)
            if path == entry: self.source.write_bytes(gzip.compress(b'{"passed":false}', mtime=0))
            return stream
        with patch.object(Path, 'open', changing_open):
            result = self.inspect()
        self.assertEqual(result['cache']['status'], 'input-changed')
        self.assertEqual(result['signals'][0]['kind'], 'failed-check')
        self.assertNotIn('inputs', result['cache'])


class CLITests(unittest.TestCase):
    def invoke(self, *args):
        output = io.StringIO()
        with patch('sys.argv', ['triage_evidence.py', *map(str, args)]), redirect_stdout(output):
            code = main()
        return code, output.getvalue()

    def cached_log(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        source = Path(temporary.name)/'run.log'
        source.write_text('error: real failure\nwarning: real warning\nBuild Summary: done\n'*3)
        args = (source, '--max-items', '1', '--max-completions', '2', '--compact',
                '--cache-dir', Path(temporary.name)/'cache')
        code, output = self.invoke(*args)
        self.assertEqual(code, 0)
        return source, args, json.loads(output)

    def test_conditional_poll_keeps_counts_without_repeating_details(self):
        source, args, first = self.cached_log()
        raw = source.read_bytes()
        code, output = self.invoke(*args, '--if-changed', first['cache']['key'])
        receipt = json.loads(output)
        self.assertEqual(code, 0)  # Inspection succeeded despite error signals.
        self.assertEqual(receipt['display'], 'unchanged')
        self.assertEqual(receipt['cache'], {'status': 'hit', 'key': first['cache']['key']})
        self.assertEqual(receipt['counts'], {'error': 3, 'warning': 3})
        self.assertEqual(receipt['inspectedInputs'], 1)
        self.assertEqual(receipt['uniqueSignals'], 2)
        self.assertEqual(receipt['omittedSignalGroups'], 2)
        self.assertEqual(receipt['completionCount'], 3)
        self.assertEqual(receipt['omittedCompletions'], 3)
        self.assertNotIn('signals', receipt)
        self.assertNotIn('completions', receipt)
        self.assertIn('not test acceptance', receipt['scope'])
        self.assertLess(len(output), len(json.dumps(first, separators=(',', ':'))))
        self.assertEqual(source.read_bytes(), raw)
        _, expanded = self.invoke(*args)
        self.assertEqual(json.loads(expanded)['signals'], first['signals'])

    def test_mismatch_cache_retains_first_difference_and_full_pair_identity(self):
        with tempfile.TemporaryDirectory() as temporary:
            source = Path(temporary)/'checks.json'
            source.write_text(json.dumps({'expected': {'data': '00'*10000+'aa'},
                                          'actual': {'data': '00'*10000+'bb'}}))
            args = (source, '--cache-dir', Path(temporary)/'cache', '--compact', '--max-items', '1')
            code, output = self.invoke(*args)
            first = json.loads(output)
            self.assertEqual(code, 0)  # Diagnostic inspection, not acceptance.
            self.assertIn('character 20000', first['signals'][0]['message'])
            _, output = self.invoke(*args)
            cached = json.loads(output)
            self.assertEqual(cached['cache']['status'], 'hit')
            self.assertEqual(cached['signals'], first['signals'])
            _, output = self.invoke(*args, '--if-changed', first['cache']['key'])
            receipt = json.loads(output)
            self.assertEqual(receipt['display'], 'unchanged')
            self.assertEqual(receipt['counts'], {'error': 1})

    def test_historical_hit_is_not_the_last_displayed_view(self):
        source, args, first = self.cached_log()
        raw = source.read_bytes()
        source.write_text('error: new failure\n')
        _, output = self.invoke(*args, '--if-changed', first['cache']['key'])
        changed = json.loads(output)
        self.assertNotIn('display', changed)
        self.assertEqual(changed['signals'][0]['message'], 'error: new failure')
        source.write_bytes(raw)
        _, output = self.invoke(*args, '--if-changed', changed['cache']['key'])
        restored = json.loads(output)
        self.assertEqual(restored['cache']['status'], 'hit')
        self.assertEqual(restored['cache']['key'], first['cache']['key'])
        self.assertNotIn('display', restored)
        self.assertEqual(restored['signals'], first['signals'])

    def test_conditional_poll_requires_identical_limits_paths_and_tool(self):
        source, args, first = self.cached_log()
        previous = first['cache']['key']
        variants = [(*args, *extra) for extra in (('--max-items', '2'), ('--max-completions', '0'),
                                                 ('--max-chars', '80'), ('--max-mib', '1'))]
        variants.append((source, *args))  # Different input group, paths before options.
        for changed_args in variants:
            # Populate first: even a historical hit must not suppress a new view.
            self.invoke(*changed_args)
            _, output = self.invoke(*changed_args, '--if-changed', previous)
            result = json.loads(output)
            self.assertEqual(result['cache']['status'], 'hit')
            self.assertNotEqual(result['cache']['key'], previous)
            self.assertNotIn('display', result)
        tool = source.parent/'tool.py'
        tool.write_text('changed tool identity')
        with patch('triage_evidence.__file__', str(tool)):
            self.invoke(*args)
            _, output = self.invoke(*args, '--if-changed', previous)
        self.assertNotIn('display', json.loads(output))

    def test_conditional_poll_does_not_suppress_cache_trouble_or_missing_inputs(self):
        source, args, first = self.cached_log()
        key = first['cache']['key']
        entry = source.parent/'cache'/(key+'.json')
        entry.write_text('{')
        code, output = self.invoke(*args, '--if-changed', key)
        result = json.loads(output)
        self.assertEqual(code, 0)
        self.assertEqual(result['cache']['status'], 'rebuilt')
        self.assertEqual(result['signals'], first['signals'])
        self.assertNotIn('display', result)
        source.unlink()
        code, output = self.invoke(*args, '--if-changed', key)
        self.assertEqual(code, 2)
        result = json.loads(output)
        self.assertFalse(result['files'][0]['inspected'])
        self.assertEqual(result['signals'][0]['kind'], 'input-not-inspected')
        self.assertNotIn('display', result)

    def test_conditional_poll_does_not_suppress_growing_inputs(self):
        source, args, first = self.cached_log()
        key = first['cache']['key']
        entry = source.parent/'cache'/(key+'.json')
        original_open = Path.open
        def changing_open(path, *args, **kwargs):
            stream = original_open(path, *args, **kwargs)
            if path == entry: source.write_text('error: newly written failure\n')
            return stream
        with patch.object(Path, 'open', changing_open):
            code, output = self.invoke(*args, '--if-changed', key)
        result = json.loads(output)
        self.assertEqual(code, 2)
        self.assertEqual(result['cache']['status'], 'input-changed')
        self.assertEqual(result['signals'][0]['message'], 'error: newly written failure')
        self.assertNotIn('display', result)

    def test_invalid_conditional_poll_rejects_before_inspection(self):
        for extra in (('--if-changed', 'a'*64), ('--cache-dir', 'unused', '--if-changed', 'bad'),
                      ('--cache-dir', 'unused', '--if-changed', 'A'*64)):
            with patch('triage_evidence.triage') as inspect, redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit) as failure:
                    self.invoke('unused.log', *extra)
                self.assertEqual(failure.exception.code, 2)
                inspect.assert_not_called()

    def test_compact_preserves_fields_counts_and_cache_identity(self):
        with tempfile.TemporaryDirectory() as temporary:
            source = Path(temporary)/'run.log'
            raw = b'Build Summary: done\n'*4+b'error: real failure\nwarning: real warning\n'
            source.write_bytes(raw)
            args = (source, '--max-items', '1', '--max-completions', '2', '--cache-dir', Path(temporary)/'cache')
            self.invoke(*args)  # Populate; both views below are cache hits.
            code, pretty = self.invoke(*args)
            compact_code, compact = self.invoke(*args, '--compact')
            self.assertEqual(code, compact_code)
            self.assertEqual(code, 0)  # Inspection succeeded, not the tests.
            self.assertEqual(json.loads(pretty), json.loads(compact))
            self.assertEqual(compact.count('\n'), 1)
            self.assertLess(len(compact), len(pretty))
            result = json.loads(compact)
            self.assertEqual(result['cache']['status'], 'hit')
            self.assertEqual(result['counts'], {'error': 1, 'warning': 1})
            self.assertEqual(result['omittedCompletions'], 2)
            self.assertEqual(result['omittedSignalGroups'], 1)
            self.assertEqual(source.read_bytes(), raw)

    def test_compact_unreadable_input_still_fails(self):
        with tempfile.TemporaryDirectory() as temporary:
            code, output = self.invoke(Path(temporary)/'missing.log', '--compact', '--max-completions', '0')
            self.assertEqual(code, 2)
            result = json.loads(output)
            self.assertFalse(result['files'][0]['inspected'])
            self.assertEqual(result['signals'][0]['kind'], 'input-not-inspected')

    def test_partial_stream_inspection_is_not_cached_or_suppressed(self):
        with tempfile.TemporaryDirectory() as temporary:
            source = Path(temporary)/'run.json'
            source.write_text(json.dumps({'stdout': '{"malformed":'}))
            cache = Path(temporary)/'cache'
            args = (source, '--cache-dir', cache, '--compact')
            code, output = self.invoke(*args)
            result = json.loads(output)
            self.assertEqual(code, 2)
            self.assertFalse(result['files'][0]['inspected'])
            self.assertFalse(cache.exists())
            code, output = self.invoke(*args, '--if-changed', result['cache']['key'])
            self.assertEqual(code, 2)
            self.assertNotIn('display', json.loads(output))
            self.assertEqual(json.loads(output)['signals'], result['signals'])

    def test_invalid_completion_limit_rejects_before_inspection(self):
        for limit in ('-1', '101'):
            with patch('triage_evidence.triage') as inspect, redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit) as failure:
                    self.invoke('unused.log', '--max-completions', limit)
                self.assertEqual(failure.exception.code, 2)
                inspect.assert_not_called()


if __name__ == '__main__': unittest.main()
