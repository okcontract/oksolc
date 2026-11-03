"""Invocation-owned scheduling for independent, frozen Lean controls.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from concurrent.futures import FIRST_EXCEPTION, ThreadPoolExecutor, wait
from dataclasses import dataclass, replace
import hashlib
import json
from pathlib import Path
import re
import resource
import time


@dataclass(frozen=True)
class PendingControl:
    plan: "ControlPlan"
    index: int

    def checked_by(self, output, check):
        self.plan.add_check(self, output, check)


@dataclass(frozen=True)
class _Task:
    name: str
    source: str
    expected: bool
    execute: object
    checks: tuple = ()


class ControlPlan:
    """Collect once, then execute with one bounded pool and ordered results.

    Collection runs the existing source/anchor checks without starting Lean.
    Diagnostic validators are deferred explicitly with their original tasks.
    No module globals or nested executors are used. Serial execution retains
    the previous four-thread Lean setting; parallel controls use one thread.
    """

    def __init__(self, output, env, lean):
        self.output = Path(output)
        self.env = dict(env)
        self.lean = lean
        self._tasks = []
        self._names = set()
        self._sealed = False
        self._started = False

    def add(self, output, name, source, expected, env, execute):
        if self._sealed or Path(output) != self.output or dict(env) != self.env:
            raise ValueError("control collection changed its execution boundary")
        if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.-]*", name) or name in self._names:
            raise ValueError("invalid or duplicate control name: " + name)
        if not isinstance(source, str) or type(expected) is not bool:
            raise TypeError("control source and acceptance must be explicit")
        pending = PendingControl(self, len(self._tasks))
        self._tasks.append(_Task(name, source, expected, execute))
        self._names.add(name)
        return pending

    def add_check(self, pending, output, check):
        if self._sealed or pending.plan is not self or Path(output) != self.output:
            raise ValueError("diagnostic check belongs to a different or sealed plan")
        task = self._tasks[pending.index]
        self._tasks[pending.index] = replace(task, checks=task.checks + (check,))

    def seal(self, records):
        if (self._sealed or any(not isinstance(r, PendingControl) or r.plan is not self for r in records)
                or sorted(r.index for r in records) != list(range(len(self._tasks)))):
            raise ValueError("control collection lost or duplicated a task")
        # Existing builders can return their records in a different order from
        # source construction. Preserve that declared report order exactly.
        self._tasks = tuple(self._tasks[r.index] for r in records)
        self._sealed = True
        return self

    def manifest(self):
        return [{"name": task.name, "expectedAcceptance": task.expected,
                 "sourceSha256": hashlib.sha256(task.source.encode()).hexdigest(),
                 "diagnosticChecks": [check.__module__ + "." + check.__qualname__ for check in task.checks]}
                for task in self._tasks]

    def run(self, workers=4):
        if not self._sealed or self._started or type(workers) is not int or not 1 <= workers <= 4:
            raise ValueError("a sealed control plan runs once with one to four workers")
        self._started = True
        for task in self._tasks:
            for suffix in (".lean", ".stdout", ".stderr", ".process.json"):
                if (self.output / (task.name + suffix)).exists():
                    raise ValueError("control output already exists: " + task.name + suffix)
        manifest = self.manifest()
        (self.output / "control-plan.json").write_text(json.dumps(manifest, indent=2) + "\n")
        env = dict(self.env)
        env["LEAN_NUM_THREADS"] = "4" if workers == 1 else "1"
        records = [None] * len(self._tasks)
        states = ["not-started"] * len(self._tasks)
        failures = [None] * len(self._tasks)

        def execute(index):
            task = self._tasks[index]
            states[index] = "running"
            try:
                record = task.execute(self.output, task.name, task.source, task.expected, dict(env), self.lean)
                for check in task.checks:
                    check(self.output, record)
                records[index] = record
                states[index] = "passed"
                return record
            except BaseException as error:
                states[index] = "failed"
                failures[index] = type(error).__name__ + ": " + str(error)
                raise

        started = time.monotonic()
        cpu = resource.getrusage(resource.RUSAGE_CHILDREN)
        futures = []
        status = "failed"
        try:
            with ThreadPoolExecutor(max_workers=workers, thread_name_prefix="lean-control") as pool:
                try:
                    for i in range(len(self._tasks)):
                        futures.append(pool.submit(execute, i))
                    wait(futures, return_when=FIRST_EXCEPTION)
                finally:
                    for future in futures:
                        future.cancel()
                    # The context joins every started process before returning or raising.
            # Choose failures and publish results in declaration order, after all
            # started work is joined. Pending work was cancelled at the first failure.
            for future in futures:
                if not future.cancelled():
                    future.result()
            if any(future.cancelled() for future in futures):
                raise RuntimeError("control matrix contains cancelled work")
            status = "passed"
        finally:
            for i, future in enumerate(futures):
                if future.cancelled():
                    states[i] = "cancelled"
            after = resource.getrusage(resource.RUSAGE_CHILDREN)
            summary = {"status": status, "workers": workers, "leanThreadsPerControl": int(env["LEAN_NUM_THREADS"]),
                       "seconds": time.monotonic() - started,
                       "childUserSeconds": after.ru_utime - cpu.ru_utime,
                       "childSystemSeconds": after.ru_stime - cpu.ru_stime,
                       "controls": [{"name": task.name, "status": states[i], "failure": failures[i]}
                                    for i, task in enumerate(self._tasks)]}
            (self.output / "control-matrix.json").write_text(json.dumps(summary, indent=2) + "\n")
        return records, summary
