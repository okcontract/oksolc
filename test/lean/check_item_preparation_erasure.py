#!/usr/bin/env python3
"""Audit native item/clone callback transport and exact host request recording.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import json
from pathlib import Path
import re

import check_recursive_entry_erasure as entries
from check_zig_air_memory_proofs import without_imports

native = entries.native
MODULE = "Compiler.Extraction.InternerItemPreparationEffectsTests"
EXTRACTION = "Compiler.Extraction."
CREATE = EXTRACTION + "AssemblyItem.Creation."
CLONE = EXTRACTION + "AssemblyClone."
INSERT = native.OWNED + "Insertion."
TESTS = INSERT + "Native.ItemEffectTests."
CLAIMS = entries.CLAIMS.copy()
for namespace, names in (
    (CREATE, ["create_transport", "Insertion.attempt_transport", "NativeFields.installResult_transport",
              "NativeFields.finish_transport", "NativeFields.attempt_transport"]),
    (CLONE, ["Physical.copyAt_transport", "Physical.duplicate_transport", "Physical.run_transport", "NativeFields.install_transport"]),
    (INSERT, ["memory_mapEffects", "observe_transport", "Native.items_attempt_transport", "Native.preparation_callback_transport"]),
    (native.TRACE, ["request_observation", "request_transport", "request_prefix", "create_transport", "copy_transport",
                    "create_erases", "clone_erases", "create_prefix", "clone_prefix"]),
    (TESTS, ["native_callbacks_erase", "actual_creation_and_clone", "item_refusal", "clone_refusal_keeps_item",
             "invalid_item_response", "source_fault_precedes_copy", "failed_read_retains_allocation", "refusal_skips_payload_read",
             "assignment_fault_retains_clone", "collision_retains_typed_allocation", "absent_payload_skips_host",
             "empty_payload_skips_host", "history_retained"]),
    (CREATE + "NativeFields.Tests.", ["source_mismatch_rejects", "oom_precedes_payload_reads",
        "failed_assignment_retains_clone", "absent_and_empty_payloads", "overwritten_target"]),
):
    CLAIMS += [namespace + name for name in names]


def dependencies(output):
    checked = entries.dependencies(output)
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    required = {
        CREATE + "create_transport": {CREATE + "create", native.NS + "HostTransport"},
        CLONE + "Physical.duplicate_transport": {CLONE + "Physical.copyAt_transport", CLONE + "Physical.duplicate"},
        CLONE + "Physical.run_transport": {CLONE + "Physical.duplicate_transport", CLONE + "Physical.run"},
        CREATE + "Insertion.attempt_transport": {CREATE + "create_transport", CLONE + "Physical.run_transport", CREATE + "Insertion.operations"},
        CREATE + "NativeFields.finish_transport": {CLONE + "NativeFields.install_transport", CREATE + "NativeFields.installResult_transport"},
        CREATE + "NativeFields.attempt_transport": {CREATE + "Insertion.attempt_transport", CREATE + "NativeFields.finish_transport",
            CLONE + "NativeFields.checkSource", CREATE + "NativeFields.operations"},
        INSERT + "Native.items_attempt_transport": {INSERT + "observe_transport", CREATE + "NativeFields.attempt_transport", INSERT + "Native.items"},
        INSERT + "Native.preparation_callback_transport": {INSERT + "Native.items_attempt_transport", INSERT + "Native.callbacks"},
        native.TRACE + "create_erases": {native.TRACE + "request_transport", native.TRACE + "recordCreate", CREATE + "create_transport"},
        native.TRACE + "clone_erases": {native.TRACE + "request_transport", native.TRACE + "recordCopy", CLONE + "Physical.run_transport"},
        TESTS + "native_callbacks_erase": {INSERT + "Native.preparation_callback_transport", native.TRACE + "create_transport", native.TRACE + "copy_transport"},
        TESTS + "actual_creation_and_clone": {INSERT + "Native.callbacks", CREATE + "create", CLONE + "Physical.run",
            CLONE + "NativeFields.install", native.TRACE + "recordRequest"},
        TESTS + "failed_read_retains_allocation": {CLONE + "Physical.copyAt", native.TRACE + "recordCopy"},
        TESTS + "assignment_fault_retains_clone": {CLONE + "NativeFields.install", native.TRACE + "recordCopy"},
        TESTS + "collision_retains_typed_allocation": {CREATE + "create", native.TRACE + "recordCreate"},
    }
    for name, needed in required.items():
        if missing := needed - claims[name]:
            raise ValueError("item preparation erasure lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return list(dict.fromkeys(checked + sorted(required)))


def source_parts():
    directory = native.ROOT / "lean/Compiler/Extraction"
    parts = [without_imports((directory / (name + ".lean")).read_text()) for name in (
        "AssemblyPreparationEffects", "AssemblyPreparationCallbacks", "InternerItemPreparationEffects",
        "AssemblyPreparationTrace", "InternerItemPreparationEffectsTests")]
    # Recheck proof bodies against the same native executors and projections.
    # Only the new request recorder is copied as executable instrumentation.
    parts[0] = parts[0].split("/-- Project only the existing session.")[0] + "end Compiler.Extraction\n"
    before, after = parts[2].split("def State.mapEffects", 1)
    parts[2] = before + "theorem memory_mapEffects" + after.split("theorem memory_mapEffects", 1)[1]
    names = set(re.findall(r"^theorem (\w+)", "\n".join(parts), re.M))
    for index, source in enumerate(parts):
        source = source.replace("HostTransport", "PreparationMutationHostTransport")
        source = source.replace("Normalization.HostTrace", "Normalization.PreparationTraceMutation")
        source = source.replace("namespace " + native.NS + "PreparationTraceMutation\n",
            "namespace " + native.NS + "PreparationTraceMutation\nopen " + native.TRACE[:-1] + "\n")
        source = source.replace("open Normalization.PreparationTraceMutation\n",
            "open Normalization.HostTrace (Recorded Event)\nopen Normalization.PreparationTraceMutation\n")
        source = source.replace("HostTrace.create_transport", "PreparationTraceMutation.create_transport")
        source = source.replace("HostTrace.copy_transport", "PreparationTraceMutation.copy_transport")
        source = source.replace("Native.ItemEffectTests", "Native.PreparationEffectMutationTests")
        source = re.sub(r"\b(" + "|".join(sorted(names)) + r")\b", lambda m: m[0] + "_preparationMutation", source)
        parts[index] = source
    return parts


def controls(output, env, lean):
    records = entries.controls(output, env, lean)
    parts = source_parts()
    def program(parts):
        return "import " + MODULE + "\n" + "\n".join(parts)
    variants = []
    for name, index, before, after in (
        ("host-empty-registry-only", 0, "∀ argument before, original argument", "∀ argument before, before.memory.nextId = 0 → original argument"),
        ("rewound-assignment", 1, "(installResult result reached).2.mapEffects project", "reached.mapEffects project"),
        ("item-in-place-of-clone", 2, "rightGraph rightGrowth).attempt site owner", "rightGraph rightGrowth).attempt .item owner"),
        ("lost-reached-effects", 3, "(result, ⟨reached, before.events", "(result, ⟨before.effects, before.events"),
        ("lost-request-event", 3, "before.events ++ [event result]", "before.events"),
        ("lost-request-history", 3, "before.events ++ [event result]", "[event result]"),
        ("wrong-item-alignment", 3, ".itemAllocate layout.bytes layout.alignment response", ".itemAllocate layout.bytes (layout.alignment + 1) response"),
        ("erased-item-response", 3, ".itemAllocate layout.bytes layout.alignment response", ".itemAllocate layout.bytes layout.alignment none"),
        ("wrong-payload-length", 3, "recordRequest Event.payloadAllocate host", "recordRequest (fun bytes response => Event.payloadAllocate (bytes + 1) response) host"),
    ):
        if parts[index].count(before) != 1:
            raise ValueError("ambiguous item preparation mutation: " + name)
        changed = parts.copy()
        changed[index] = changed[index].replace(before, after)
        if name == "rewound-assignment":
            # Isolate the invalid helper equation. Its failed elaboration would
            # otherwise cause a secondary reduction-limit error in `finish`.
            # The unchanged consumer uses the independently imported theorem.
            changed[1] = changed[1].replace("exact installResult_transport_preparationMutation project",
                "exact installResult_transport project")
        variants.append((name, program(changed)))
    return records + native.check_controls(output, env, lean, program(parts), variants, prefix="item-preparation-")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--preflight", action="store_true")
    native.check(parser.parse_args(), module=MODULE, claims=CLAIMS, dependency_check=dependencies,
        control_check=controls, publication=True, native_dispatch=True, recursive_entries=True, item_preparation=True)
