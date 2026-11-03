#!/usr/bin/env python3
"""Derive publication host-trace erasure through the existing owned-key caller.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import json
from pathlib import Path

import check_native_resource_trace as native
from check_zig_air_memory_proofs import without_imports

MODULE = "Compiler.Extraction.InternerPublicationHostTraceTests"
KEYS = "Compiler.Extraction.OwnedKeys."
PUB = native.OWNED + "Publication."
TRACE = PUB + "Recording."
FILES = ["OwnedKeysEffects.lean", "OwnedKeysPhysicalEffects.lean", "InternerPublicationEffects.lean",
    "InternerPublicationHostTrace.lean", "InternerPhysicalDispatchEffects.lean", "InternerPublicationHostTraceTests.lean"]
CLAIMS = native.CLAIMS + [KEYS + "Operations.Transport." + name for name in ("complete", "execute")]
CLAIMS += [KEYS + "Physical." + name for name in ("operations_transport", "run_transport")]
CLAIMS += [PUB + name for name in ("forget_mapEffects", "external_transport", "probe_transport", "admit_transport", "commit_transport")]
CLAIMS += [PUB + "EffectTransport." + name for name in ("body", "publish", "callbacks", "find")]
CLAIMS += [TRACE + name for name in ("probe_observation", "probe_transport", "probe_prefix", "publish_erases", "publish_prefix", "find_erases")]
CLAIMS += [native.OWNED + "Recursive." + name for name in ("constructors_erase", "simplify_erases")]
CLAIMS += [TRACE + "Tests." + name for name in (
    "capture_erases", "replacement_erases", "replacement_events", "replacement_reached", "refused_probe",
    "release_fault_keeps_probe", "admission_rejects_before_probe", "empty_key_skips_native_release",
    "replacement_prefix", "fixture_child_transport", "simplify_transport", "caller_erases",
    "caller_success", "caller_oom_cleanup", "caller_success_events", "caller_oom_events")]
CLAIMS += [PUB + "Tests." + name for name in ("coupled", "production_contract", "replacement_success", "replacement_oom")]


def dependencies(output):
    checked = native.dependencies(output)
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    required = {
        KEYS + "Physical.run_transport": {KEYS + "Operations.Transport.execute", KEYS + "Code.execute",
            KEYS + "Code.complete", native.NS + "External.Transport.free"},
        PUB + "EffectTransport.publish": {KEYS + "Physical.run_transport", PUB + "admit_transport",
            PUB + "commit_transport", PUB + "external_transport", PUB + "probe_transport"},
        PUB + "EffectTransport.find": {PUB + "EffectTransport.publish", native.OWNED + "Caller.EffectTransport.find",
            "Compiler.Extraction.Interner.FindCode.controlRun"},
        TRACE + "find_erases": {PUB + "EffectTransport.find", TRACE + "recordProbe", TRACE + "probe_transport",
            native.TRACE + "record", native.TRACE + "transport"},
        native.OWNED + "Recursive.simplify_erases": {"Compiler.Extraction.Dispatch.Effects.simplify",
            native.OWNED + "Recursive.constructors_erase", "Compiler.Algebraic.Effect.Transport.bind"},
        TRACE + "Tests.caller_erases": {TRACE + "find_erases", TRACE + "Tests.simplify_transport",
            native.OWNED + "Recursive.simplify_erases", PUB + "Tests.physicalFindWith"},
        TRACE + "Tests.caller_oom_events": {TRACE + "recordProbe", native.TRACE + "record",
            native.OWNED + "Caller.find", PUB + "publish", KEYS + "Physical.run"},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError("publication host trace lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return checked + sorted(required)


def controls(output, env, lean):
    # Retain the normalization controls; publication mutations use its imported
    # proved recorder and compile all new composition proofs and consumers anew.
    records = native.controls(output, env, lean)
    source = "import Compiler.Extraction.NormalizationHostTraceTests\nimport Compiler.Extraction.InternerPublicationTests\n"
    source += "\n".join(without_imports((native.ROOT / "lean/Compiler/Extraction" / name).read_text()) for name in FILES)
    variants = []
    for name, before, after in (
        ("lost-probe", "before.effects.events ++ [.publicationProbe key result]", "before.effects.events"),
        ("wrong-key", "before.effects.events ++ [.publicationProbe key result]",
            "before.effects.events ++ [.publicationProbe { key with sequence := key.sequence + 1 } result]"),
        ("wrong-decision", "before.effects.events ++ [.publicationProbe key result]",
            "before.effects.events ++ [.publicationProbe key (!result)]"),
        ("lost-effects", "(result, ⟨reached, before.effects.events", "(result, ⟨before.effects.effects, before.effects.events"),
        ("changed-response", "(result, ⟨reached, before.effects.events", "(true, ⟨reached, before.effects.events"),
        ("lost-history", "before.effects.events ++ [.publicationProbe key result]", "[.publicationProbe key result]"),
        ("reordered-history", "before.effects.events ++ [.publicationProbe key result]", "[.publicationProbe key result] ++ before.effects.events"),
        ("lost-key-ownership", "⟨before.keys, project before.allocator⟩", "⟨fun _ => none, project before.allocator⟩"),
    ):
        if source.count(before) != 1:
            raise ValueError("ambiguous publication host trace mutation: " + name)
        variants.append((name, source.replace(before, after)))
    return records + native.check_controls(output, env, lean, source, variants, prefix="publication-")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--preflight", action="store_true")
    native.check(parser.parse_args(), module=MODULE, claims=CLAIMS, dependency_check=dependencies,
        control_check=controls, publication=True)
