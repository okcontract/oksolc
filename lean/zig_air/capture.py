#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Capture a standalone Zig fixture with the pinned, patched LLVM toolchain.
// Copyright (C) 2026 OKcontract Pte. Ltd.

This checks capture provenance and completion, not program semantics. Every
record remains outside a compiler-correctness claim, including decoded scalars.
"""

import argparse
import hashlib
import json
from pathlib import Path
import posixpath
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from extract_storage import lex

from build_toolchain import REVISION, VERSION, digest, run, source_identity, write_json


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate JSON field: " + key)
        result[key] = value
    return result


def read_json(path):
    if path.stat().st_size > 16 * 1024 * 1024:
        raise ValueError("capture record exceeds inspection limit: " + str(path))
    def nonfinite(value):
        raise ValueError("nonfinite JSON: " + value)
    return json.loads(path.read_text(), object_pairs_hook=unique_object, parse_constant=nonfinite)


def inspect_records(directory, roots, source_sha, mode):
    """Require all requested roots and retain unsupported instructions/tags."""
    if not roots or len(set(roots)) != len(roots):
        raise ValueError("expected roots must be nonempty and unique")
    records = {}
    for path in sorted(directory.iterdir()):
        if path.is_symlink() or not path.is_file() or path.suffix != ".json":
            raise ValueError("unexpected capture entry: " + str(path))
        record = read_json(path)
        if record.get("schema") != "oksolc.fresh-air.v3" or record.get("capturePoint") != "after-sema-before-legalize":
            raise ValueError("unexpected capture schema or phase")
        name = record.get("name")
        if not isinstance(name, str) or not name or name in records:
            raise ValueError("missing or duplicate captured function name")
        # The source-operation inventory is a rejection aid, not a claim that
        # the original, control-dependent source conditions have been modeled.
        if record.get("sourceValidityConditionsPreserved") is not False:
            raise ValueError("unexpected source-validity claim")
        validity = record.get("sourceValidity")
        if (not isinstance(validity, dict) or set(validity) != {"schema", "coverage", "complete", "slices"} or
                validity["schema"] != "oksolc.source-validity.v1" or validity["coverage"] != "runtime-slice-results" or
                validity["complete"] is not False or not isinstance(validity["slices"], list)):
            raise ValueError("missing or unsupported source-validity inventory")
        tags = record.get("sourceOperationTags")
        if not isinstance(tags, list) or not tags or any(not isinstance(t, str) for t in tags) or len(set(tags)) != len(tags):
            raise ValueError("missing or invalid source-operation inventory")
        instructions, body = record.get("instructions"), record.get("body")
        if not isinstance(instructions, list) or not isinstance(body, list):
            raise ValueError("missing AIR body or instruction inventory")
        for i, inst in enumerate(instructions):
            if type(inst.get("index")) is not int or inst["index"] != i or not isinstance(inst.get("tag"), str):
                raise ValueError("malformed AIR instruction index or tag")
        if any(type(i) is not int or not 0 <= i < len(instructions) for i in body):
            raise ValueError("out-of-range AIR body reference")
        if name in roots:
            if record.get("sourceSha256") != source_sha:
                raise ValueError("requested root source hash mismatch")
            config = record.get("configuration", {})
            if config.get("optimize") != mode or config.get("useLlvm") is not True or config.get("isTest") is not False:
                raise ValueError("requested root build configuration mismatch")
        records[name] = {"file": path.name, "sha256": digest(path), "requested": name in roots,
                         "instructionCount": len(instructions), "sourceOperationTags": tags,
                         "sourceValiditySliceCount": len(validity["slices"]),
                         "unsupportedPayloadCount": sum(i.get("unsupportedPayload") is True for i in instructions)}
    missing = set(roots) - records.keys()
    if missing:
        raise ValueError("missing requested AIR roots: " + ", ".join(sorted(missing)))
    return {name: records[name] for name in sorted(records)}


def module_bindings(entries):
    """Explicit root imports; named modules are self-contained leaf sources."""
    modules = {}
    for entry in entries:
        name, separator, path = entry.partition("=")
        target = Path(path)
        if (not separator or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name) or
                name in {"root", "std", "builtin"} or name in modules or
                target.is_absolute() or ".." in target.parts or target.suffix != ".zig"):
            raise ValueError("invalid or duplicate capture module binding")
        modules[name] = target.as_posix()
    if len(set(modules.values())) != len(modules):
        raise ValueError("capture module source has multiple identities")
    return dict(sorted(modules.items()))


def source_files(source, extra_sources, modules=None):
    """Bind explicit production imports for caller capture, without rewriting.

    Extra paths are relative to the invocation directory and retain that layout
    next to the root fixture. Only static local imports and the pinned std/builtin
    modules and explicitly named leaf modules are admitted. This inventories
    inputs, not semantic dependencies. Module files must be listed explicitly.
    """
    files = {source.name: source.read_bytes()}
    for path in extra_sources:
        if path.is_absolute() or ".." in path.parts or path.suffix != ".zig" or path.as_posix() in files:
            raise ValueError("invalid or duplicate capture source path: " + str(path))
        files[path.as_posix()] = path.read_bytes()
    modules = modules or {}
    if any(path not in files or path == source.name for path in modules.values()):
        raise ValueError("capture module missing from explicit source closure")
    if extra_sources or modules:
        for name, data in files.items():
            items = lex(data.decode("utf-8"))
            for position, item in enumerate(items):
                if item != "@import":
                    continue
                call = items[position:position + 4]
                if len(call) != 4 or call[1] != "(" or call[3] != ")" or not call[2].startswith('"'):
                    raise ValueError("nonstatic capture source import: " + name)
                imported = json.loads(call[2])
                if imported in {"std", "builtin"}:
                    continue
                if name in modules.values():
                    raise ValueError("capture named modules must be self-contained leaves: " + name)
                if imported in modules:
                    continue
                resolved = posixpath.normpath(posixpath.join(posixpath.dirname(name), imported))
                if resolved not in files:
                    raise ValueError("capture source import missing from explicit closure: " + name + ": " + imported)
                if resolved in modules.values():
                    raise ValueError("capture module imported by both name and path: " + resolved)
    return files


def module_arguments(fixture, modules, mode):
    if not modules:
        return ["-O" + mode, fixture]
    result = ["-O" + mode, "-fstrip"]
    for name in modules:
        result += ["--dep", name]
    result += ["-Mroot=" + str(fixture)]
    for name, path in modules.items():
        # Zig resets per-module settings after each -M argument.
        result += ["-O" + mode, "-fstrip", "-M" + name + "=" + str(fixture.parent / path)]
    return result


def capture(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "oksolc.fresh-air-capture.v1", "status": "failed", "captureComplete": False,
              "compilerVerified": False, "semanticExportImplemented": False, "sourceClosureComplete": False}
    try:
        if args.source.suffix != ".zig" or not args.root or len(set(args.root)) != len(args.root):
            raise ValueError("expected a Zig source and unique, nonempty requested roots")
        toolchain = read_json(args.toolchain)
        if toolchain.get("status") not in ("built", "built-with-diagnostics") or toolchain.get("freshAirCaptureImplemented") is not True:
            raise ValueError("toolchain has no completed fresh-AIR capture build")
        if toolchain.get("zigRevision") != REVISION or toolchain["compiler"].get("version") != VERSION:
            raise ValueError("toolchain is not the pinned Zig " + VERSION + " revision")
        compiler = Path(toolchain["compiler"]["path"])
        lib = Path(toolchain["compiler"]["zigLibDir"])
        if digest(compiler) != toolchain["compiler"]["sha256"] or source_identity(lib.parent) != toolchain["sourceTree"]:
            raise ValueError("toolchain input hash mismatch")
        report["toolchainReportSha256"] = digest(args.toolchain)
        report["compilerSha256"] = digest(compiler)
        extra_sources = getattr(args, "source_file", [])
        modules = module_bindings(getattr(args, "module", []))
        sources = source_files(args.source, extra_sources, modules)
        if modules:
            report["sourceModules"] = modules
        report["sourceFiles"] = {name: hashlib.sha256(data).hexdigest() for name, data in sorted(sources.items())}
        for name, data in sources.items():
            destination = output / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(data)
        fixture = output / args.source.name
        report["sourceSha256"] = digest(fixture)
        directory = output / "air"
        directory.mkdir()
        common = ["build-obj", "--zig-lib-dir", lib, "-fllvm", "-fno-incremental", "-fstrip",
                  *module_arguments(fixture, modules, args.mode), "--global-cache-dir", output / "global-cache"]
        run(output, "capture", [compiler, *common, "--cache-dir", output / "capture-cache",
            "-femit-bin=" + str(output / "captured.o"), "--semantic-export=" + str(directory)])
        report["functions"] = inspect_records(directory, args.root, report["sourceSha256"], args.mode)
        run(output, "ordinary", [compiler, *common, "--cache-dir", output / "ordinary-cache",
            "-femit-bin=" + str(output / "ordinary.o")])
        report["objects"] = {name: digest(output / (name + ".o")) for name in ("ordinary", "captured")}
        if report["objects"]["ordinary"] != report["objects"]["captured"]:
            raise ValueError("capture changed native object bytes")
        if (module_bindings(getattr(args, "module", [])) != modules or
                source_files(args.source, extra_sources, modules) != sources or
                any((output / name).read_bytes() != data for name, data in sources.items()) or
                digest(compiler) != report["compilerSha256"] or source_identity(lib.parent) != toolchain["sourceTree"]):
            raise ValueError("capture inputs changed during compilation")
        report["captureComplete"] = True
        report["status"] = "captured"
    except Exception as error:
        report["error"] = str(error)
        raise
    finally:
        write_json(output / "report.json", report)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", type=Path, required=True)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--source-file", type=Path, action="append", default=[], help="explicit production dependency, relative to the invocation directory; repeat for the complete local import closure")
    parser.add_argument("--module", action="append", default=[], help="named leaf import NAME=path.zig; its source must also be listed with --source-file")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--root", action="append", required=True, help="fully qualified requested function; repeat as needed")
    parser.add_argument("--mode", choices=("Debug", "ReleaseSafe", "ReleaseFast"), default="ReleaseFast")
    capture(parser.parse_args())


if __name__ == "__main__":
    main()
