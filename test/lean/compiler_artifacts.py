#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Shared exact-artifact binding, fresh-package proof audit and kernel replay.
Profiles supply closed data admission and theorem statements, never acceptance.
"""
import argparse
import json
import os
from pathlib import Path
import sys

import check_compiler as gate
from common import decode_json, read_bounded

ROOT = gate.ROOT
MAX_BYTES = 1024 * 1024


def audit_commands(claims, schema):
    return ["open Lean Elab Command Contract.Check in", "run_cmd do",
        "  let roots := #[" + ", ".join("``" + name for name in claims) + "]",
        "  let .ok dependencies := Declarations.closure (← getEnv) roots | throwError \"invalid dependency closure\"",
        "  let .ok axioms := Declarations.axioms dependencies | throwError \"disallowed axiom\"",
        "  let mut claims := #[]", "  for root in roots do",
        "    let some info := (← getEnv).find? root | throwError \"missing theorem\"",
        "    unless info matches .thmInfo _ do throwError \"not a theorem\"",
        "    claims := claims.push <| Json.mkObj [(\"theorem\", .str root.toString),",
        "      (\"statement\", Declarations.expression info.type)]",
        "  liftIO <| IO.println (Json.mkObj [(\"schema\", .str \"" + schema + "\"),",
        "    (\"claims\", .arr claims), (\"axioms\", toJson axioms),",
        "    (\"dependencies\", toJson (dependencies.map (·.name.toString)))]).compress", ""]


def audit_source(module, claims, schema):
    return ["end " + module, "", *audit_commands(claims, schema)]


def compiled_audit_source(module, claims, schema):
    """Inspect the fresh package's declarations without elaborating their proofs again."""
    return ("\n".join(["import Lean.Elab.Command", "import Contract.Check.Declarations", "import " + module, "",
                       *audit_commands(claims, schema)])).encode()

def audit(data, claims, schema):
    value = decode_json(data)
    if (value.get("schema") != schema or
            [c["theorem"] for c in value.get("claims", [])] != claims or
            not set(value.get("axioms", [])) <= {"propext", "Classical.choice", "Quot.sound"} or
            not value.get("dependencies")):
        raise ValueError("incomplete or invalid artifact proof audit")
    return value


def matching_audit(preflight, compiled, claims, schema):
    checked = audit(compiled, claims, schema)
    if checked != audit(preflight, claims, schema):
        raise ValueError("fresh compiled declarations differ from the preflight proof audit")
    return checked


def package_inputs(root):
    paths = [p for p in root.rglob("*.lean") if ".lake" not in p.relative_to(root).parts]
    paths += [root / "lean-toolchain", root / "lake-manifest.json"]
    return {str(p.relative_to(root)): gate.source.file_digest(p) for p in sorted(paths)}


def proof_batches(profile, pairs, fuel):
    batches = (profile.proof_batches(pairs, fuel) if hasattr(profile, "proof_batches")
               else [profile.proof_source(pairs, fuel)])
    if not batches or any(not isinstance(code, bytes) or not code or not names or
                          any(not isinstance(name, str) or not name for name in names)
                          for code, names in batches):
        raise ValueError("empty or malformed artifact proof batch")
    claims = [name for _, names in batches for name in names]
    if len(claims) != len(pairs) or len(set(claims)) != len(claims):
        raise ValueError("every artifact pair must have its own theorem")
    return batches, claims


def is_semantic_rejection(profile, exit_code, diagnostic):
    """Resource exhaustion must not turn a broken control into proof rejection."""
    expected = getattr(profile, "NEGATIVE_DIAGNOSTICS", ("is false",))
    forbidden = (*getattr(profile, "NEGATIVE_FORBIDDEN_DIAGNOSTICS", ()),
                 "excessive memory", "out of memory")
    return (exit_code == 1 and any(message in diagnostic for message in expected) and
            not any(message in diagnostic.lower() for message in forbidden))


def main(profile):
    parser = argparse.ArgumentParser(description=profile.__doc__)
    selection = parser.add_mutually_exclusive_group(required=True)
    selection.add_argument("--request", type=Path, action="append")
    selection.add_argument("--corpus", action="store_true", help="generate and check the production-rule corpus")
    parser.add_argument("--response", type=Path, action="append", help="optional paired retained responses; no native execution")
    parser.add_argument("--compiler", type=Path, default=ROOT / "zig-out/bin" / profile.BINARY_NAME)
    parser.add_argument("--output", type=Path, required=True, help="new evidence directory")
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--jobs", type=int, default=4, choices=range(1, 5),
                        help="Lean build workers; native requests run sequentially")
    parser.add_argument("--fuel", type=int, default=8, choices=range(0, 17))
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args()
    args.request = args.request or []
    if ((not args.corpus and not 1 <= len(args.request) <= 128) or args.timeout <= 0 or
            (args.corpus and args.response) or
            (args.response is not None and len(args.response) != len(args.request))):
        parser.error("provide 1..128 requests, matching responses when supplied, and a positive timeout")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": profile.REPORT_SCHEMA, "status": "failed", "accepted": False,
        "proofScope": profile.PROOF_SCOPE, "wholeCompilerVerified": False, "emittedEvmProof": False,
        "jobs": args.jobs, "fuel": args.fuel, "requestedCases": len(args.request),
        "freshPackage": False, "freshKernelReplay": False,
        "corpusRequested": args.corpus, "corpusComplete": False,
        "origin": "providedResponse" if args.response else "productionPass", "cases": [], "negativeControls": [],
        **profile.REPORT_METADATA}
    try:
        def inputs():
            snapshot = gate.snapshot()
            for relative in getattr(profile, "EXTRA_INPUTS", ()):
                snapshot[relative] = gate.source.file_digest(ROOT / relative)
            return snapshot

        before = inputs()
        report["sourceSha256"] = before
        if args.corpus:
            args.request = profile.write_cases(output / "requests")
            report.update(requestedCases=len(args.request), corpusComplete=True)
            if not 1 <= len(args.request) <= 128:
                raise ValueError("corpus exceeds the supported proof batch")
        env, sysroot, tools = gate.source.toolchain(args.lean_bin, args.jobs)
        tools["leanchecker"] = {"path": str(sysroot / "bin/leanchecker"),
            "sha256": gate.source.file_digest(sysroot / "bin/leanchecker")}
        tools["python"] = {"path": str(Path(sys.executable).resolve()),
            "sha256": gate.source.file_digest(Path(sys.executable))}
        compiler = args.compiler.resolve()
        if not args.response:
            tools["compiler"] = {"path": str(compiler), "sha256": gate.source.file_digest(compiler)}
        report["tools"] = tools
        originals = {}

        def remember(path, raw):
            path, digest = path.resolve(), gate.digest(raw)
            if path in originals and originals[path] != digest:
                raise ValueError("repeated input changed while being read")
            originals[path] = digest

        requests = []
        for i, path in enumerate(args.request):
            path = path.resolve()
            raw = read_bounded(path, MAX_BYTES)
            remember(path, raw)
            (output / f"case-{i}.request.json").write_bytes(raw)
            requests.append((raw, profile.request(raw)))

        def native(item):
            i, (raw, _) = item
            return gate.require_success(output, f"native-{i}",
                [str(compiler), *getattr(profile, "NATIVE_ARGS", ())], env, args.timeout, data=raw)

        if args.response:
            responses = []
            for path in args.response:
                path = path.resolve()
                raw = read_bounded(path, MAX_BYTES)
                remember(path, raw)
                responses.append(raw)
        else:
            responses = [native(item) for item in enumerate(requests)]
        pairs = []
        for i, ((request_raw, req), response_raw) in enumerate(zip(requests, responses)):
            (output / f"case-{i}.response.json").write_bytes(response_raw)
            if len(response_raw) > MAX_BYTES:
                raise ValueError("native response exceeds artifact size limit")
            res = profile.response(response_raw, request_raw)
            pairs.append((req, res))
            report["cases"].append({"case": i, "requestSha256": gate.digest(request_raw),
                "requestPath": str(args.request[i].resolve()),
                "responseSha256": gate.digest(response_raw), **profile.case_metadata(req, res), "accepted": False})
        batches, claims = proof_batches(profile, pairs, args.fuel)
        batch_records = []
        report["proofBatches"] = batch_records
        # Cheap elaboration against cached model imports catches rejection before
        # any fresh package build. Retain and bound each object here too, so an
        # oversized certificate rejects before expensive fresh replay.
        first_case = 0
        for index, (code, names) in enumerate(batches):
            directory = "." if len(batches) == 1 else f"proof-{index}"
            batch_output = output / directory
            batch_output.mkdir(exist_ok=True)
            record = {"directory": directory, "cases": list(range(first_case, first_case + len(names))),
                      "claims": names, "proofSourceSha256": gate.digest(code),
                      "freshPackage": False, "freshKernelReplay": False}
            batch_records.append(record)
            first_case += len(names)
            (batch_output / "Artifact.lean").write_bytes(code)
            preflight = gate.require_success(batch_output, "preflight", [tools["lean"]["path"],
                "-DwarningAsError=true", "-o", str(batch_output / "Preflight.olean"), "--stdin"],
                env, args.timeout, data=code, cwd=ROOT / "lean")
            if gate.read(batch_output, "preflight.stderr").strip():
                raise ValueError("unexpected preflight stderr")
            audit(preflight, names, profile.AUDIT_SCHEMA)
            read_bounded(batch_output / "Preflight.olean", 64 * MAX_BYTES)
        if args.corpus:
            negatives = [(name, negative, {"origin": "mutation"}) for name, negative in profile.negative_pairs(pairs)]
            for name, req in getattr(profile, "rejection_cases", lambda: [])():
                raw = (json.dumps(req, sort_keys=True, separators=(",", ":")) + "\n").encode()
                (output / ("rejected-native-" + name + ".request.json")).write_bytes(raw)
                admitted = profile.request(raw)
                response_raw = gate.require_success(output, "rejected-native-" + name,
                    [str(compiler), *getattr(profile, "NATIVE_ARGS", ())], env, args.timeout, data=raw)
                if len(response_raw) > MAX_BYTES:
                    raise ValueError("native rejection response exceeds artifact size limit")
                res = profile.response(response_raw, raw)
                negatives.append((name, [(admitted, res)], {"origin": "productionPass",
                    "requestSha256": gate.digest(raw), "responseSha256": gate.digest(response_raw)}))
            for name, negative, provenance in negatives:
                (output / ("negative-" + name + ".pairs.json")).write_text(
                    json.dumps(negative, sort_keys=True, indent=2) + "\n")
                rejected_code, _ = profile.proof_source(negative, args.fuel)
                exit_code = gate.run(output, "negative-" + name, [tools["lean"]["path"],
                    "-DwarningAsError=true", "--stdin"], env, args.timeout,
                    data=rejected_code, cwd=ROOT / "lean")
                diagnostic = gate.read(output, "negative-" + name + ".stdout").decode(errors="replace")
                if not is_semantic_rejection(profile, exit_code, diagnostic):
                    raise ValueError("expected kernel rejection missing: " + name)
                report["negativeControls"].append({"case": name, "rejected": True,
                    "exitCode": exit_code, **provenance})

        all_axioms = set()
        for (code, names), record in zip(batches, batch_records):
            batch_output = output / record["directory"]
            package = batch_output / "package/lean"
            package.mkdir(parents=True)
            for relative in gate.source.source_inputs():
                original = ROOT / "lean" / relative
                data = original.read_bytes()
                if gate.digest(data) != before["lean/" + relative]:
                    raise ValueError("source changed while preparing fresh package")
                target = package / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(data)
            artifact_path = package / (profile.MODULE.replace(".", "/") + ".lean")
            if artifact_path.exists():
                raise ValueError("generated artifact module would overwrite a model source")
            artifact_path.write_bytes(code)
            copied = package_inputs(package)
            record["packageInputs"] = copied
            fresh_env = {**env, "LEAN_PATH": str(package / ".lake/build/lib/lean"),
                "LEAN_SRC_PATH": os.pathsep.join(map(str, [package, sysroot / "src/lean/lake", sysroot / "src/lean"]))}
            gate.require_success(batch_output, "fresh-build", [tools["lake"]["path"], "--quiet", "--rehash", "build", profile.MODULE],
                fresh_env, args.timeout, cwd=package)
            record["freshPackage"] = True
            audit_code = compiled_audit_source(profile.MODULE, names, profile.AUDIT_SCHEMA)
            (batch_output / "Audit.lean").write_bytes(audit_code)
            record["auditSourceSha256"] = gate.digest(audit_code)
            record["auditMode"] = "compiledDeclarations"
            audited = gate.require_success(batch_output, "audit", [tools["lean"]["path"], "-DwarningAsError=true",
                "--stdin"], fresh_env, args.timeout, data=audit_code, cwd=package)
            if gate.read(batch_output, "audit.stderr").strip():
                raise ValueError("unexpected audit stderr")
            checked = matching_audit(gate.read(batch_output, "preflight.stdout"), audited,
                                     names, profile.AUDIT_SCHEMA)
            gate.require_success(batch_output, "replay", [tools["leanchecker"]["path"], "--fresh", profile.MODULE],
                {**fresh_env, "LEAN_NUM_THREADS": "1"}, args.timeout, cwd=package)
            if gate.read(batch_output, "replay.stderr").strip():
                raise ValueError("unexpected fresh replay stderr")
            record["freshKernelReplay"] = True
            gate.require_stable(copied, package_inputs(package))
            all_axioms.update(checked["axioms"])
            record["axioms"] = checked["axioms"]
            proof_object = read_bounded(package / (".lake/build/lib/lean/" + profile.MODULE.replace(".", "/") + ".olean"), 64 * MAX_BYTES)
            (batch_output / "Artifact.olean").write_bytes(proof_object)
            record["proofObjectSha256"] = gate.digest(proof_object)
        report.update(freshPackage=True, freshKernelReplay=True)
        # Preserve the established single-package fields for existing profiles.
        # Multiple-package identities and case coverage are explicit in proofBatches.
        if len(batch_records) == 1:
            for key in ("packageInputs", "proofSourceSha256", "proofObjectSha256"):
                report[key] = batch_records[0][key]
        gate.require_stable(before, inputs())
        for path, expected in originals.items():
            if gate.source.file_digest(path) != expected:
                raise ValueError("request or response changed during validation")
        for tool in tools.values():
            if gate.source.file_digest(Path(tool["path"])) != tool["sha256"]:
                raise ValueError("tool changed during validation")
        report["claims"] = claims
        report["axioms"] = sorted(all_axioms)
        for case, claim in zip(report["cases"], claims):
            case.update(accepted=True, theorem=claim)
        report.update(status="passed", accepted=True, emittedEvmProof=profile.EMITTED_EVM)
        if getattr(profile, "DEPLOYMENT_PROOF", False):
            report["deploymentVerified"] = True
    except (Exception, KeyboardInterrupt) as error:
        report["failure"] = {"kind": type(error).__name__, "message": str(error)}
    finally:
        accepted_cases = {case["case"] for case in report["cases"] if case["accepted"]}
        report["unvalidatedCases"] = [i for i in range(len(args.request)) if i not in accepted_cases]
        (output / "report.json").write_text(json.dumps(report, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "accepted": report["accepted"], "output": str(output)}))
    return 0 if report["accepted"] else 1
