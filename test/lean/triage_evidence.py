#!/usr/bin/env python3
"""
// Copyright (C) 2026 OKcontract Pte. Ltd.

Read-only, bounded triage of local .json[.gz] and .log[.gz] evidence.
Example: python3 test/lean/triage_evidence.py /private/tmp/run.log /private/tmp/checks.json.gz
Signals may be expected negative controls; this is not an acceptance checker.
Raw evidence is never deleted, rewritten, or normalized into an agreement.
"""
import argparse
import ast
from collections import Counter
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import tempfile

SIGNAL = re.compile(r'\b(error|warning|fail|failed|failure|traceback|assertionerror|exception)\b', re.I)
COMPLETION = re.compile(r'(Build Summary:|Build completed successfully|(?:tests?|checks) passed|Ran \d+ tests|exact comparisons|Library review:|generation/build passed|libraries executed:|Yul control executed:|^OK$)', re.I)
SOURCE_DIAGNOSTIC = re.compile(r'(?<!\S)\S+:\d+(?::\d+)?:\s*(?:fatal )?(error|warning)(?:\([\w.-]+\))?:', re.I)
LEAN_BUILD_DIAGNOSTIC = re.compile(r'^\s*(error|warning):\s*\S+:\d+(?::\d+)?:', re.I)
EXCEPTION = re.compile(r'^\s*(?:[\w.]*(?:Error|Exception)|[Uu]ncaught [Ee]xception):')
TEST_FAILURE = re.compile(r'^\s*(?:expected\b.*\bfound\b|\[FAIL[:\]]|FAIL:|FAILED\b(?! command:))', re.I)
STREAM_KEY = re.compile(r'''(?P<quote>['"])(?P<name>stdout|stderr)(?P=quote)\s*:\s*''')
STREAM_STRING = re.compile(r'''(?:'(?:[^'\\]|\\.)*'|"(?:[^"\\]|\\.)*")''')
MAX_EMBEDDED_LOG_CHARS = 1024*1024
MAX_EMBEDDED_STREAMS = 32
MAX_LOG_LINE_CHARS = 1024*1024
MAX_EMBEDDED_JSON_CHARS = 128*1024*1024
MAX_EMBEDDED_JSON_DOCUMENTS = 64
MAX_EMBEDDED_JSON_DEPTH = 4
# Do not mistake ordinary Foundry lines such as [PASS] or [FAIL] for JSON.
JSON_STREAM = re.compile(r'^\s*(?:\{|\[\s*(?:[\[\]{"\d-]|true\b|false\b|null\b))')
MISSING = object()


def comparison_digest(expected, actual):
    """Identity of the entire decoded pair, not just its first difference.

    Stream canonical JSON chunks rather than retaining a second complete pair
    spelling as a diagnostic/group key. This is not the raw input file hash.
    """
    digest = hashlib.sha256()
    for chunk in json.JSONEncoder(sort_keys=True, separators=(',', ':')).iterencode([expected, actual]):
        digest.update(chunk.encode('ascii'))
    return digest.hexdigest()


def first_difference(expected, actual, pointer=''):
    """Return one deterministic JSON-pointer difference; never an agreement rule."""
    if expected == actual: return None
    if isinstance(expected, dict) and isinstance(actual, dict):
        for key in sorted(expected.keys() | actual.keys()):
            child = pointer+'/'+key.replace('~', '~0').replace('/', '~1')
            if key not in expected or key not in actual:
                return child, expected.get(key, MISSING), actual.get(key, MISSING)
            found = first_difference(expected[key], actual[key], child)
            if found is not None: return found
    elif isinstance(expected, list) and isinstance(actual, list):
        for index, (left, right) in enumerate(zip(expected, actual)):
            found = first_difference(left, right, pointer+'/'+str(index))
            if found is not None: return found
        index = min(len(expected), len(actual))
        if len(expected) != len(actual):
            return pointer+'/'+str(index), (expected[index] if index < len(expected) else MISSING), \
                (actual[index] if index < len(actual) else MISSING)
    else:
        return pointer, expected, actual
    return None


def difference_message(difference):
    pointer, expected, actual = difference
    # Long byte strings commonly differ only at their end. Show a small window
    # at the first differing character, not thousands of equal prefix bytes.
    index = 0
    if isinstance(expected, str) and isinstance(actual, str):
        index = next((i for i, (a, b) in enumerate(zip(expected, actual)) if a != b),
                     min(len(expected), len(actual)))

    def preview(value):
        if value is MISSING: return '<missing>'
        if isinstance(value, dict): return 'object('+str(len(value))+' fields)'
        if isinstance(value, list): return 'array('+str(len(value))+' items)'
        if isinstance(value, str) and len(value) > 40:
            start = max(0, min(index, len(value))-8)
            return 'string('+str(len(value))+' chars)['+str(start)+':'+str(min(start+24, len(value)))+']='+\
                json.dumps(value[start:start+24])
        return json.dumps(value)

    where = json.dumps(pointer)  # Empty string is the root JSON pointer.
    if isinstance(expected, str) and isinstance(actual, str):
        where += ' (character '+str(index)+')'
    return 'first difference at '+where+': expected='+preview(expected)+' actual='+preview(actual)


def triage(paths, *, max_items=12, max_completions=12, max_chars=240, max_bytes=128*1024*1024):
    groups = {}; completions = []; files = []; completion_count = 0
    embedded_json_chars = embedded_json_documents = 0
    input_complete = True

    def add(level, kind, message, location, *, comparison_sha256=None):
        nonlocal input_complete
        if kind in ('embedded-json', 'embedded-log', 'log-line-limit'):
            input_complete = False
        # Ordinary signals deduplicate exact messages. A comparison retains the
        # complete pair identity: equal first differences must not merge pairs
        # whose later fields differ. No semantic observations are normalized.
        message = str(message)
        key = (level, kind, comparison_sha256 if comparison_sha256 is not None else message)
        if key not in groups:
            groups[key] = {'level': level, 'kind': kind, 'message': message, 'count': 0, 'firstLocation': location}
            if comparison_sha256 is not None: groups[key]['comparisonSha256'] = comparison_sha256
        groups[key]['count'] += 1

    def operation_hint(hint, location, owner=None):
        if not isinstance(hint, dict):
            add('warning', 'operation-hint', 'malformed operation hint; inspect raw diagnostic', location)
            return
        space = hint.get('coordinateSpace')
        message = str(hint.get('operation'))+': '+str(hint.get('reason'))+'; '+str(space)+\
            ' bytes '+str(hint.get('start'))+' length '+str(hint.get('length'))
        if space == 'source':
            site = hint.get('source')
            if isinstance(site, dict):
                message += '; '+str(site.get('file'))
                if 'line' in site: message += ':'+str(site['line'])
                if 'excerpt' in site: message += '; '+str(site['excerpt'])
            elif isinstance(owner, dict):
                message += '; '+str(owner.get('file'))  # Owner line is not the child line.
        add('warning', 'operation-hint', message, location)

    def structured(text, location, depth, embedded):
        # Native command archives often put a complete compiler JSON response
        # inside stdout. Traverse its diagnostic fields, not source/AST/bytecode
        # string values. Bound cumulative decoding work per input, not per field.
        nonlocal embedded_json_chars, embedded_json_documents
        for unit, used, limit in (('depth', depth+1, MAX_EMBEDDED_JSON_DEPTH),
                                 ('documents', embedded_json_documents+1, MAX_EMBEDDED_JSON_DOCUMENTS),
                                 ('characters', embedded_json_chars+len(text), MAX_EMBEDDED_JSON_CHARS)):
            if used > limit:
                add('error', 'embedded-json', 'embedded JSON '+unit+' budget exceeded ('+str(used)+' > '+
                    str(limit)+'); not inspected', location)
                return
        embedded_json_chars += len(text)
        embedded_json_documents += 1
        try:
            value = json.loads(text)
        except (ValueError, RecursionError) as error:
            add('error', 'embedded-json', 'structured JSON not inspected; bounded text fallback: '+str(error), location)
            log(text, location, depth=depth, embedded=embedded)
            return
        walk(value, location, depth=depth+1, embedded=embedded)

    def tool_stream(text, location, *, depth=0, embedded=False):
        if JSON_STREAM.match(text):
            structured(text, location, depth, embedded)
        else:
            log(text, location, depth=depth, embedded=embedded)

    def embedded_streams(line, location, depth):
        # Tool exceptions often repr() a dictionary containing escaped compiler
        # stdout/stderr. Decode string literals only, never the command/exception
        # expression. Bound both each stream and work per enclosing log line.
        consumed = count = 0
        for field in STREAM_KEY.finditer(line):
            if field.start() < consumed: continue
            if count == MAX_EMBEDDED_STREAMS:
                add('error', 'embedded-log', 'additional embedded streams exceed limit; not inspected', location)
                break
            count += 1
            here = location+'.'+field['name']
            literal = STREAM_STRING.match(line, field.end(), min(len(line), field.end()+MAX_EMBEDDED_LOG_CHARS))
            if literal is None:
                add('error', 'embedded-log', 'nonliteral, malformed or oversized embedded stream; not inspected', here)
                continue
            consumed = literal.end()
            try:
                spelling = literal[0]
                # JSON quoting and Python repr quoting are both used by callers.
                try:
                    value = json.loads(spelling)
                except json.JSONDecodeError:
                    value = ast.literal_eval(spelling)
                if not isinstance(value, str): raise ValueError('embedded stream is not a string')
                tool_stream(value, here, depth=depth, embedded=True)
            except (ValueError, SyntaxError, RecursionError) as error:
                add('error', 'embedded-log', 'embedded stream not inspected: '+str(error), here)

    def log(text, location, *, depth=0, embedded=False):
        nonlocal completion_count
        for line_number, line in enumerate(text.splitlines(), 1):
            if len(line) > MAX_LOG_LINE_CHARS:
                add('error', 'log-line-limit', 'log line exceeds character limit ('+str(len(line))+'); not inspected',
                    location+':'+str(line_number))
                continue
            exception = EXCEPTION.search(line)
            wrapped = exception and STREAM_KEY.search(line)
            # A wrapper quotes a child completion; it is not a second run.
            if not wrapped and COMPLETION.search(line):
                completion_count += 1
                if len(completions) < max_completions:
                    completions.append({'location': location+':'+str(line_number), 'text': line[:max_chars]})
            signal = SIGNAL.search(line)
            if signal or exception:
                diagnostic = SOURCE_DIAGNOSTIC.search(line) or LEAN_BUILD_DIAGNOSTIC.search(line)
                kind = ('compiler-diagnostic' if diagnostic else 'log-exception' if exception else
                        'test-failure' if TEST_FAILURE.search(line) else 'log-signal')
                severity = diagnostic[1] if diagnostic else 'error' if exception else signal[1]
                add('warning' if severity.lower() == 'warning' else 'error', kind, line, location+':'+str(line_number))
            if wrapped:
                here = location+':'+str(line_number)
                if embedded:
                    add('error', 'embedded-log', 'nested embedded streams exceed depth limit; not inspected', here)
                else:
                    embedded_streams(line, here, depth)

    def walk(value, location, *, depth=0, embedded=False):
        if isinstance(value, list):
            for i, child in enumerate(value): walk(child, location+'['+str(i)+']', depth=depth, embedded=embedded)
        elif isinstance(value, dict):
            severity = value.get('severity')
            if severity in ('error', 'warning'):
                add(severity, 'diagnostic', value.get('formattedMessage', value.get('message', value.get('type', 'unspecified'))), location)
            status = value.get('status')
            if isinstance(status, str) and status in ('unsupported', 'rejected', 'inconclusive', 'failed', 'failure', 'error'):
                add('warning' if status in ('unsupported', 'rejected', 'inconclusive') else 'error', 'status', status, location)
            diagnostic_status = value.get('diagnosticStatus')
            if diagnostic_status in ('unsupported', 'inspection-failed', 'inconclusive-resource-limit'):
                details = str(value.get('failure') or '')
                if not details and isinstance(value.get('capabilities'), list):
                    details = ', '.join(map(str, value['capabilities']))
                add('error' if diagnostic_status == 'inspection-failed' else 'warning', 'coverage-root',
                    str(value.get('root', 'unspecified'))+': '+diagnostic_status+(' ('+details+')' if details else ''), location)
            if value.get('schema') == 'oksolc.chainwall.coverage-summary.v1':
                scope = value.get('scope', {})
                if not isinstance(scope, dict):
                    add('error', 'coverage-summary', 'malformed coverage scope', location)
                elif scope.get('kind') == 'declared-subset':
                    add('warning', 'coverage-scope', 'declared subset: '+str(value.get('sourceFiles'))+
                        ' source units; '+str(scope.get('omittedSourceFiles'))+' source units omitted; not complete coverage', location)
            for key in ('returncode', 'exitCode'):
                code = value.get(key)
                if isinstance(code, int) and not isinstance(code, bool) and code != 0:
                    add('error', 'process-exit', key+'='+str(code), location)
            for key in ('passed', 'exact', 'canonicalByteIdentical'):
                if value.get(key) is False: add('error', 'failed-check', key+'=false', location)
            expected = value.get('expected')
            actual = value.get('actual')
            has_pair = 'expected' in value and 'actual' in value
            if isinstance(value.get('case'), dict) and 'expected' in value['case'] and 'result' in value:
                expected, actual, has_pair = value['case']['expected'], value['result'], True
            if has_pair:
                difference = first_difference(expected, actual)
                if difference is not None:
                    add('error', 'observation-mismatch', difference_message(difference), location,
                        comparison_sha256=comparison_digest(expected, actual))
            for key, child in value.items():
                here = location+'.'+str(key)
                if key == 'diagnostics' and isinstance(child, list):
                    for i, diagnostic in enumerate(child):
                        if isinstance(diagnostic, dict) and diagnostic.get('severity') not in ('error', 'warning'):
                            message = str(diagnostic.get('capability', ''))+': '+str(diagnostic.get('message', diagnostic.get('reason', 'unspecified')))
                            add('warning', 'admission-diagnostic', message, here+'['+str(i)+']')
                        if isinstance(diagnostic, dict) and 'hint' in diagnostic:
                            operation_hint(diagnostic['hint'], here+'['+str(i)+'].hint', diagnostic.get('source'))
                if key == 'operationHints' and isinstance(child, list):
                    for i, hint in enumerate(child): operation_hint(hint, here+'['+str(i)+']')
                if isinstance(child, str):
                    if key == 'error' and child:
                        add('error', 'reported-error', child, here)
                    elif key.endswith('.json') and child.lstrip().startswith(('{', '[')):
                        structured(child, here, depth, embedded)
                    elif key in ('stdout', 'stderr', 'log', 'traceback') or key.endswith('.log'):
                        tool_stream(child, here, depth=depth, embedded=embedded)
                else: walk(child, here, depth=depth, embedded=embedded)

    for name in paths:
        path = Path(name)
        embedded_json_chars = embedded_json_documents = 0
        input_complete = True
        try:
            opener = gzip.open if path.suffix == '.gz' else open
            with opener(path, 'rb') as stream: raw = stream.read(max_bytes+1)
            if len(raw) > max_bytes: raise ValueError('decompressed input exceeds byte limit; not inspected')
            text = raw.decode('utf-8')
            if path.name.endswith(('.json', '.json.gz')): walk(json.loads(text), str(path))
            else: log(text, str(path))
            files.append({'path': str(path), 'bytes': len(raw), 'inspected': input_complete})
        except (OSError, UnicodeError, ValueError, RecursionError, EOFError) as error:
            files.append({'path': str(path), 'inspected': False})
            add('error', 'input-not-inspected', str(error), str(path))
    # Surface actionable failures ahead of repeated build scaffolding such as
    # "transitive failure". Ranking never changes retained counts or raw logs.
    priority = {'input-not-inspected': 0, 'observation-mismatch': 1, 'failed-check': 1,
                'compiler-diagnostic': 2, 'diagnostic': 2, 'log-exception': 2,
                'reported-error': 2, 'embedded-json': 0, 'embedded-log': 0, 'log-line-limit': 0,
                'test-failure': 2, 'admission-diagnostic': 3,
                'coverage-scope': 0, 'operation-hint': 2, 'coverage-root': 3}
    ordered = sorted(groups.values(), key=lambda row: (row['level'] != 'error', priority.get(row['kind'], 4),
                                                     -row['count'], row['kind'], row['message']))
    counts = Counter()
    for row in ordered: counts[row['level']] += row['count']
    selected = []
    for row in ordered[:max_items]:
        selected.append({**row, 'message': row['message'][:max_chars], 'messageTruncated': len(row['message']) > max_chars,
                         'firstLocation': row['firstLocation'][:max_chars]})
    return {'scope': 'diagnostic signals only; expected negatives may be included; raw files unchanged',
            'files': files, 'counts': dict(counts), 'uniqueSignals': len(ordered),
            'omittedSignalGroups': max(0, len(ordered)-max_items), 'signals': selected, 'completions': completions,
            'completionCount': completion_count, 'omittedCompletions': completion_count-len(completions)}


def cached_triage(paths, cache_dir, **limits):
    """Cache only diagnostic views, bound to raw bytes, this tool and its limits.

    Rehash before returning: an actively written log must not acquire a stable
    evidence identity. Cache trouble falls back to inspection, never to success.
    """
    paths = [str(Path(p).absolute()) for p in paths]

    def encode(value):
        return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()

    def hashes():
        result = []
        for name in paths:
            digest = hashlib.sha256()
            with open(name, 'rb') as stream:
                for chunk in iter(lambda: stream.read(1024*1024), b''): digest.update(chunk)
            result.append({'path': name, 'sha256': digest.hexdigest()})
        return result

    try:
        identity = {'schema': 'oksolc.evidence-triage-cache.v1', 'inputs': hashes(), 'limits': limits,
                    'toolSha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), 'python': sys.version}
    except OSError as error:
        return {**triage(paths, **limits), 'cache': {'status': 'unavailable', 'detail': str(error)[:240]}}
    key = hashlib.sha256(encode(identity)).hexdigest()
    entry = Path(cache_dir)/(key+'.json')
    result = None
    state = 'miss'
    try:
        with entry.open('rb') as stream: data = stream.read(8*1024*1024+1)
        if len(data) > 8*1024*1024: raise ValueError('cache entry exceeds limit')
        cached = json.loads(data)
        if (not isinstance(cached, dict) or cached.get('identity') != identity or
            not isinstance(cached.get('result'), dict) or
            hashlib.sha256(encode(cached['result'])).hexdigest() != cached.get('resultSha256')):
            raise ValueError('cache identity or integrity mismatch')
        result = cached['result']; state = 'hit'
    except FileNotFoundError:
        pass
    except (OSError, ValueError, RecursionError):
        state = 'rebuilt'
    if result is None: result = triage(paths, **limits)
    try:
        stable = hashes() == identity['inputs']
    except OSError:
        stable = False
    if not stable:
        # A cached view may be stale; inspect again and explicitly leave it unbound.
        if state == 'hit': result = triage(paths, **limits)
        return {**result, 'cache': {'status': 'input-changed', 'detail': 'input changed during triage; view is unbound; retry after completion'}}
    metadata = {'status': state, 'key': key, 'inputs': identity['inputs']}
    if state != 'hit' and all(row['inspected'] for row in result['files']):
        temporary = None
        try:
            entry.parent.mkdir(parents=True, exist_ok=True)
            data = encode({'identity': identity, 'result': result,
                           'resultSha256': hashlib.sha256(encode(result)).hexdigest()})
            with tempfile.NamedTemporaryFile(dir=entry.parent, prefix='.triage-', delete=False) as stream:
                temporary = Path(stream.name); stream.write(data)
            os.replace(temporary, entry)
        except OSError as error:
            metadata.update(status='not-saved', detail=str(error)[:240])
        finally:
            if temporary is not None: temporary.unlink(missing_ok=True)
    return {**result, 'cache': metadata}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('paths', nargs='+')
    parser.add_argument('--max-items', type=int, default=12)
    parser.add_argument('--max-completions', type=int, default=12,
                        help='display at most this many completion lines; retain total and omitted counts (0..100)')
    parser.add_argument('--max-chars', type=int, default=240)
    parser.add_argument('--max-mib', type=int, default=128)
    parser.add_argument('--compact', action='store_true', help='emit single-line JSON with the same fields and counts')
    parser.add_argument('--cache-dir', type=Path, help='optional local cache of content-bound diagnostic views (not acceptance evidence)')
    parser.add_argument('--if-changed', metavar='PREVIOUS_VIEW_KEY',
                        help='with --cache-dir, omit repeated details only for this previously inspected view key; retain counts')
    args = parser.parse_args()
    if (not 1 <= args.max_items <= 100 or not 0 <= args.max_completions <= 100 or
            not 80 <= args.max_chars <= 2000 or not 1 <= args.max_mib <= 1024):
        parser.error('limits: items 1..100, completions 0..100, chars 80..2000, MiB 1..1024')
    if args.if_changed is not None and (args.cache_dir is None or not re.fullmatch(r'[0-9a-f]{64}', args.if_changed)):
        parser.error('--if-changed requires --cache-dir and a previous 64-character lowercase cache.key')
    limits = dict(max_items=args.max_items, max_completions=args.max_completions,
                  max_chars=args.max_chars, max_bytes=args.max_mib*1024*1024)
    result = (cached_triage(args.paths, args.cache_dir, **limits) if args.cache_dir else triage(args.paths, **limits))
    cache = result.get('cache', {})
    code = 0 if all(row['inspected'] for row in result['files']) and cache.get('status') != 'input-changed' else 2
    if code == 0 and cache.get('status') == 'hit' and cache['key'] == args.if_changed:
        # A cache hit alone does not mean the caller has seen this view. Require
        # its last displayed identity, not any historical hit. Cache trouble or
        # unstable/uninspected input always keeps the full bounded diagnostics.
        result = {'scope': 'unchanged diagnostic view; not test acceptance', 'display': 'unchanged',
                  'cache': {'status': 'hit', 'key': cache['key']}, 'inspectedInputs': len(result['files']),
                  'counts': result['counts'], 'uniqueSignals': result['uniqueSignals'],
                  'omittedSignalGroups': result['uniqueSignals'],
                  'completionCount': result['completionCount'], 'omittedCompletions': result['completionCount']}
    print(json.dumps(result, separators=(',', ':')) if args.compact else json.dumps(result, indent=2))
    return code


if __name__ == '__main__': raise SystemExit(main())
