#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Batch coverage and rejection boundaries for native/Lean dispatcher evidence.
"""
import hashlib
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import check_compiler_dispatch as check


def cases(count):
    return [(dict(name='case-' + str(i), nodes=[], instruction='STOP', arguments=[],
                  version=None, forYul=False, failAt=0), []) for i in range(count)]


class BatchTests(unittest.TestCase):
    def test_boundary_preserves_complete_order(self):
        items = cases(513)
        seen, records = [], []

        def batch(output, chunk, *_):
            seen.extend(chunk)
            self.assertLessEqual(len(chunk), 512)
            return dict(status='passed', usizeBits=64, cases=len(chunk))

        with tempfile.TemporaryDirectory() as directory, patch.object(check, 'check_batch', side_effect=batch):
            check.check_batches(Path(directory), items, None, None, None, 1, 512, records)
        self.assertEqual(seen, items)
        self.assertEqual([(r['firstCase'], r['cases'], r['status']) for r in records],
                         [(0, 512, 'passed'), (512, 1, 'passed')])

    def test_later_failure_stops_and_retains_prior_batch(self):
        records = []
        with tempfile.TemporaryDirectory() as directory, patch.object(check, 'check_batch', side_effect=[
                dict(status='passed', usizeBits=64, cases=1), ValueError('bad second response')]) as run:
            with self.assertRaisesRegex(ValueError, 'bad second response'):
                check.check_batches(Path(directory), cases(3), None, None, None, 1, 1, records)
        self.assertEqual(run.call_count, 2)
        self.assertEqual([r['status'] for r in records], ['passed', 'failed'])

    def test_host_width_change_rejects(self):
        records = []
        with tempfile.TemporaryDirectory() as directory, patch.object(check, 'check_batch', side_effect=[
                dict(status='passed', usizeBits=64, cases=1), dict(status='passed', usizeBits=32, cases=1)]):
            with self.assertRaisesRegex(ValueError, 'host width changed'):
                check.check_batches(Path(directory), cases(2), None, None, None, 1, 1, records)
        self.assertEqual(records[-1]['status'], 'failed')
        self.assertEqual(records[-1]['usizeBits'], 32)

    def test_invalid_scope_rejects_before_native_invocation(self):
        duplicated = cases(513)
        duplicated[-1] = duplicated[0]
        for items, size in [(cases(1), 0), (cases(1), 513), ([], 1), (cases(4097), 512), (duplicated, 512)]:
            with self.subTest(size=size, count=len(items)), tempfile.TemporaryDirectory() as directory, \
                    patch.object(check, 'check_batch') as run, self.assertRaises(ValueError):
                check.check_batches(Path(directory), items, None, None, None, 1, size, [])
            run.assert_not_called()

    def test_response_scope_binding_and_order_reject(self):
        for mutation in ['missing', 'extra', 'hash', 'reorder']:
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as directory:
                output = Path(directory)

                def native(destination, name, command, env, timeout, **kwargs):
                    self.assertEqual(name, 'native')
                    (destination / 'native.stderr').write_bytes(b'')
                    observations = [dict(name='case-' + str(i), result=None, failure=None, calls=[]) for i in range(2)]
                    digest = hashlib.sha256(kwargs['data']).hexdigest()
                    if mutation == 'missing': observations.pop()
                    if mutation == 'extra': observations.append(observations[0])
                    if mutation == 'hash': digest = '0' * 64
                    if mutation == 'reorder': observations.reverse()
                    return check.encode(dict(schema='oksolc.compiler-dispatch-response.v1',
                        requestSha256=digest, usizeBits=64, observations=observations))

                with patch.object(check.gate, 'require_success', side_effect=native), self.assertRaises(ValueError):
                    check.check_batch(output, cases(2), 'native', {}, {}, 1)
                self.assertTrue((output / 'request.json').exists())
                self.assertTrue((output / 'response.json').exists())

    def test_oversize_request_retained_without_invocation(self):
        items = cases(1)
        items[0][0]['name'] = 'x' * (1024 * 1024)
        with tempfile.TemporaryDirectory() as directory, patch.object(check.gate, 'require_success') as run:
            output = Path(directory)
            with self.assertRaisesRegex(ValueError, 'byte limit'):
                check.check_batch(output, items, 'native', {}, {}, 1)
            self.assertGreater((output / 'request.json').stat().st_size, 1024 * 1024)
        run.assert_not_called()


if __name__ == '__main__':
    unittest.main()
