#!/usr/bin/env python3
"""Run one verification job with a sampled aggregate resident-memory limit.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

The tree includes children that create new sessions (e.g. fresh kernel replay).
RSS sums can count shared pages more than once. This is a conservative sampled
watchdog, not an OS reservation or a hard instantaneous allocation limit. Run
only one such verification job at a time; its harness still bounds Lean workers.
The launched job must not deliberately detach children before they are observed.
"""
import argparse
import json
import os
from pathlib import Path
import signal
import subprocess
import time


def snapshot():
    """Read process identities and sizes, never command arguments/environment."""
    result = subprocess.run(["/bin/ps", "-axo", "pid=,ppid=,rss=,lstart="],
                            capture_output=True, text=True, check=True,
                            env={**os.environ, "LC_ALL": "C"}, timeout=5)
    rows = {}
    for line in result.stdout.splitlines():
        pid, parent, kib, started = line.split(maxsplit=3)
        rows[int(pid)] = (int(parent), int(kib) * 1024, started)
    if not rows:
        raise RuntimeError("process inspection returned no rows")
    return rows


def descendants(rows, known):
    """Retain observed descendants across reparenting; reject reused PIDs."""
    selected = {pid: row for pid, row in rows.items() if known.get(pid) == row[2]}
    while True:
        more = {pid: row for pid, row in rows.items() if row[0] in selected and pid not in selected}
        if not more:
            return selected
        selected.update(more)


def terminate(child, known):
    # Freeze the known tree before killing it, so interrupted harnesses cannot
    # start another phase. Verify each identity immediately before signalling.
    # A new-session child is still selected by parentage, not process group.
    for sig in (signal.SIGSTOP, signal.SIGKILL):
        rows = snapshot()
        selected = descendants(rows, known)
        known.update({pid: row[2] for pid, row in selected.items()})
        for pid, row in selected.items():
            current = snapshot().get(pid)
            if current is not None and current[2] == row[2]:
                try:
                    os.kill(pid, sig)
                except ProcessLookupError:
                    pass
    child.wait(timeout=10)


def run(command, output, *, rss_mib=8192, timeout=1800, interval=0.25):
    if not command or rss_mib <= 0 or timeout <= 0 or not 0 < interval <= 1:
        raise ValueError("command and positive limits required; sample interval at most one second")
    output = Path(output)
    output.mkdir(parents=True, exist_ok=False)
    report = {"status": "failed", "command": command, "rssLimitBytes": rss_mib * 1024**2,
              "sampleIntervalSeconds": interval, "timeoutSeconds": timeout,
              "peakSampledTreeRssBytes": 0, "peakProcesses": 0, "samples": 0,
              "exitCode": None, "resourceLimit": None}
    child = None
    known = {}
    started = time.monotonic()
    try:
        snapshot()  # Fail before launching work if process inspection is unavailable.
        with (output / "stdout.log").open("wb") as out, (output / "stderr.log").open("wb") as err:
            child = subprocess.Popen(command, stdout=out, stderr=err, start_new_session=True)
            rows = snapshot()
            if child.pid in rows:
                known[child.pid] = rows[child.pid][2]
            elif child.poll() is None:
                raise RuntimeError("cannot inspect running verification process")
            while True:
                selected = descendants(rows, known)
                known.update({pid: row[2] for pid, row in selected.items()})
                rss = sum(row[1] for row in selected.values())
                report["samples"] += 1
                report["peakSampledTreeRssBytes"] = max(report["peakSampledTreeRssBytes"], rss)
                report["peakProcesses"] = max(report["peakProcesses"], len(selected))
                if rss > report["rssLimitBytes"]:
                    report["resourceLimit"] = "aggregateRss"
                    break
                if time.monotonic() - started > timeout:
                    report["resourceLimit"] = "timeout"
                    break
                if child.poll() is not None:
                    live = descendants(snapshot(), known)
                    live.pop(child.pid, None)
                    if live:
                        raise RuntimeError("verification process left observed descendants running")
                    report["status"] = "passed" if child.returncode == 0 else "failed"
                    break
                time.sleep(interval)
                rows = snapshot()
    except BaseException as error:
        report["error"] = type(error).__name__ + ": " + str(error)
        raise
    finally:
        try:
            if child is not None:
                try:
                    if child.poll() is None or descendants(snapshot(), known):
                        terminate(child, known)
                except BaseException as error:
                    report["status"] = "failed"
                    report["cleanupError"] = type(error).__name__ + ": " + str(error)
                    # Inspection failure must at least stop the still-owned root
                    # session. Previously observed detached sessions may need
                    # investigation; the receipt must not report clean success.
                    if child.poll() is None:
                        try:
                            os.killpg(child.pid, signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                    raise
                report["exitCode"] = child.wait(timeout=10)
        finally:
            report["seconds"] = time.monotonic() - started
            (output / "receipt.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--rss-mib", type=int, default=8192)
    parser.add_argument("--timeout", type=float, default=1800)
    parser.add_argument("--interval", type=float, default=0.25)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    result = run(command, args.output, rss_mib=args.rss_mib, timeout=args.timeout, interval=args.interval)
    raise SystemExit(0 if result["status"] == "passed" else 1)
