"""Complete capture binding from local hosts to the finite native step.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import json
import re

import check_native_resource_trace as native
from check_zig_air_memory_proofs import without_imports

NORMALIZATION = "Compiler.Extraction.Memory.Arguments.Normalization."
RESOURCE = NORMALIZATION + "ResourceAdapter."
NORMALIZATION_TRACE = "Compiler.Extraction.Cache.NormalizationOwnership.Trace."
STORAGE_TRACE = "Compiler.Extraction.Storage.Trace."
CALLER = native.OWNED + "Caller."
PROTOCOL = CALLER + "ProtocolTrace."
CONSTRUCTOR = native.OWNED + "ConstructorItem.ProtocolTrace."
RECURSIVE = native.OWNED + "ConstructorItem.NativeRecursion.ProtocolTrace."
HOSTS = native.OWNED + "Insertion.Native.HostBindings."

REQUIRED = {
    RESOURCE + "EffectTransport.allocate": {NORMALIZATION + "External.Transport.reserve", NORMALIZATION + "External.Transport.takeOwned"},
    RESOURCE + "EffectTransport.release": {NORMALIZATION + "External.Transport.free", RESOURCE + "release"},
    RESOURCE + "prepare_transport": {NORMALIZATION + "External.Transport.prepare", RESOURCE + "prepare"},
    RESOURCE + "primitives_transport": {RESOURCE + "EffectTransport.allocate", RESOURCE + "EffectTransport.release", RESOURCE + "prepare_transport"},
    NORMALIZATION_TRACE + "record_map": {NORMALIZATION_TRACE + "record", NORMALIZATION_TRACE + "Recorded.mapEffects"},
    PROTOCOL + "map_scope": {PROTOCOL + "Recorded.mapEffects", PROTOCOL + "scopeView"},
    PROTOCOL + "record_transport": {PROTOCOL + "record", PROTOCOL + "Recorded.mapEffects"},
    PROTOCOL + "EffectTransport.graph": {PROTOCOL + "record_transport", native.OWNED + "EffectTransport.graph"},
    PROTOCOL + "EffectTransport.findBody": {PROTOCOL + "record_transport", PROTOCOL + "EffectTransport.graph",
        PROTOCOL + "EffectTransport.initialization", PROTOCOL + "EffectTransport.taking", "Compiler.Extraction.Interner.FindCode.controlRun"},
    PROTOCOL + "EffectTransport.finish": {PROTOCOL + "record_transport", PROTOCOL + "EffectTransport.closing", native.OWNED + "EffectTransport.cleanup"},
    PROTOCOL + "EffectTransport.invoke": {PROTOCOL + "EffectTransport.finish", PROTOCOL + "invoke"},
    PROTOCOL + "EffectTransport.find": {PROTOCOL + "EffectTransport.findBody", PROTOCOL + "EffectTransport.invoke"},
    CONSTRUCTOR + "mapReturn_outcome": {CONSTRUCTOR + "mapReturn", CONSTRUCTOR + "outcome"},
    CONSTRUCTOR + "retire_transport": {CONSTRUCTOR + "retire", CONSTRUCTOR + "mapReturn", native.OWNED + "TemporaryArguments.unwind"},
    CONSTRUCTOR + "EffectTransport.frame": {PROTOCOL + "EffectTransport.find", CONSTRUCTOR + "retire_transport"},
    CONSTRUCTOR + "EffectTransport.item": {CONSTRUCTOR + "EffectTransport.frame", native.OWNED + "ConstructorItem.EffectTransport.prepare"},
    CONSTRUCTOR + "EffectTransport.literal": {CONSTRUCTOR + "EffectTransport.item", native.OWNED + "ConstructorItem.Arguments.EffectTransport.prepare"},
    CONSTRUCTOR + "EffectTransport.namedLocal": {CONSTRUCTOR + "EffectTransport.item", native.OWNED + "LocalArguments.EffectTransport.zigLocal"},
    CONSTRUCTOR + "EffectTransport.constructors": {CONSTRUCTOR + "EffectTransport.item", CONSTRUCTOR + "EffectTransport.literal", CONSTRUCTOR + "EffectTransport.namedLocal"},
    STORAGE_TRACE + "record_map": {STORAGE_TRACE + "record", STORAGE_TRACE + "Recorded.mapEffects"},
    HOSTS + "obligations": {native.OWNED + "Insertion.Native.callback_obligations", native.OWNED + "Insertion.Native.residual_obligations", native.OWNED + "Insertion.Native.append_transport"},
    HOSTS + "observedCalls": {HOSTS + "obligations", native.OWNED + "Insertion.Native.callbacks_transport"},
    HOSTS + "recordExecution": {HOSTS + "observedCalls", STORAGE_TRACE + "record_map", "Compiler.Extraction.Storage.Operations.Transport.execute"},
    HOSTS + "callerBase": {HOSTS + "obligations", native.OWNED + "Publication.EffectTransport.publish", native.OWNED + "Insertion.Native.insert_transport"},
    PROTOCOL + "Native.graphObservations_traced": {PROTOCOL + "Native.dispatch_history", native.OWNED + "Publication.admit_transport", HOSTS + "recordExecution"},
    RECURSIVE + "step_traced": {CONSTRUCTOR + "EffectTransport.constructors", HOSTS + "callerBase", PROTOCOL + "Native.graphObservations_traced",
        native.OWNED + "ConstructorItem.NativeRecursion.context_erases", native.OWNED + "ConstructorItem.NativeRecursion.ChildTrace.constructors_erase"},
    RECURSIVE + "unfold_step_traced": {RECURSIVE + "step_traced", RECURSIVE + "unfold", RECURSIVE + "children"},
    RECURSIVE + "materialize_forwarded": {RECURSIVE + "unfold", CONSTRUCTOR + "constructors"},
    RECURSIVE + "materialize_miss_bound": {RECURSIVE + "constant_miss_bound", RECURSIVE + "materialize_forwarded", RECURSIVE + "unfold"},
    RECURSIVE + "EffectsTests.hosts": {native.OWNED + "Insertion.Native.HostBindings", RECURSIVE + "EffectsTests.operations", RECURSIVE + "EffectsTests.backing"},
    RECURSIVE + "EffectsTests.parent_binding": {RECURSIVE + "unfold_step_traced", RECURSIVE + "EffectsTests.hosts"},
    RECURSIVE + "EffectsTests.recursive_oom": {RECURSIVE + "EffectsTests.parent_binding", RECURSIVE + "Tests.recursive_oom"},
}
for segment, observation in (("Initialization", "initialization"), ("Take", "taking"), ("Close", "closing")):
    REQUIRED[CALLER + segment + ".capture_transport"] = {RESOURCE + "primitives_transport", NORMALIZATION_TRACE + "record_map"}
    REQUIRED[PROTOCOL + "EffectTransport." + observation] = {CALLER + segment + ".capture_transport", PROTOCOL + observation}
for entry in ("borrowed", "constant", "operation", "local"):
    REQUIRED[RECURSIVE + entry + "_miss_bound"] = {RECURSIVE + "unfold_step_traced", RECURSIVE + entry + "_miss_projected",
        CONSTRUCTOR + "prepared_miss_map", CONSTRUCTOR + "mapReturn_outcome", RECURSIVE + "unfold"}
CLAIMS = list(REQUIRED)


def dependencies(output):
    claims = {c["theorem"]: set(c["dependencies"]) for c in json.loads((output / "audit.json").read_bytes())["claims"]}
    for name, needed in REQUIRED.items():
        if missing := needed - claims[name]:
            raise ValueError("captured step lost dependencies: " + name + ": " + ", ".join(sorted(missing)))
    return sorted(REQUIRED)


def controls(output, env, lean):
    directory = native.ROOT / "lean/Compiler/Extraction"
    # Recheck semantic conclusions against the imported implementations. Rename
    # declarations only: their proof clients consume the same audited helpers.
    parts = [without_imports((directory / (name + ".lean")).read_text()) for name in (
        "InternerCallerProtocolEffects", "InternerRecursiveProtocolEffects", "InternerRecursiveProtocolBoundReturn")]
    marker = "\nnamespace ProtocolTrace\n"
    if parts[0].count(marker) != 1:
        raise ValueError("ambiguous local capture contract boundary")
    parts[0] = parts[0].split(marker)[0] + "\nend " + CALLER.rstrip(".") + "\n"
    parts = [re.sub(r"\btheorem ([A-Za-z0-9_.]+)", lambda m: "theorem " + m[1] + "ContractControl", part) for part in parts]
    parts.append("""
namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.ContractControls
open Compiler.Algebraic Compiler.Extraction.Cache
theorem metadata (project : σ → τ) (before : Recorded σ) :
    (before.mapEffects project).tokens = before.tokens ∧
    (before.mapEffects project).events = before.events ∧
    (before.mapEffects project).native.scope = before.native.scope := ⟨rfl, rfl, rfl⟩
theorem resourceDescriptors (project : σ → τ) (before : ResourceAdapter.State σ) :
    (before.mapEffects project).handle = before.handle ∧
    (before.mapEffects project).transferred = before.transferred ∧
    (before.mapEffects project).rejected = before.rejected := ⟨rfl, rfl, rfl⟩
theorem normalizationHistory (project : σ → τ) (before : NormalizationOwnership.Trace.Recorded σ ε) :
    (before.mapEffects project).events = before.events := rfl
theorem insertionHistory (project : σ → τ) (before : Storage.Trace.Recorded σ ε) :
    (before.mapEffects project).events = before.events := rfl
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.ContractControls
""")

    def program(sources):
        return "import Compiler.Extraction.InternerRecursiveProtocolEffectsTests\n" + "\n".join(sources)

    variants = []
    for name, index, before, after, count in (
        ("initializer-wrong-budget", 0,
         "Initialization.capture right budget allocator commutative source buffer values",
         "Initialization.capture right (budget + 1) allocator commutative source buffer values", 1),
        ("take-wrong-allocator", 0, "Take.capture right allocator origin handle", "Take.capture right (allocator + 1) origin handle", 1),
        ("close-wrong-phase", 0, "Close.capture right allocator lookup phase handle", "Close.capture right allocator lookup .lookup handle", 1),
        ("observations-wrong-owner", 1,
         "Native.graphObservations ops allocate safety owner meaning base growth usizeBits children observations debug source address input)",
         "Native.graphObservations ops allocate safety (owner + 1) meaning base growth usizeBits children observations debug source address input)", 1),
        ("step-drops-leading-history", 1,
         "(fun action before leading => action (ChildTrace.erase before) leading)",
         "(fun action before leading => action (ChildTrace.erase before) [])", 2),
        ("successor-wrong-depth", 2,
         "(unfold ops allocate safety owner meaning base growth usizeBits (depth + 1))",
         "(unfold ops allocate safety owner meaning base growth usizeBits depth)", 5),
        ("borrowed-wrong-address", 2,
         "source.address opcode source.items debug (ChildTrace.erase before))",
         "0 opcode source.items debug (ChildTrace.erase before))", 1),
        ("constant-wrong-value", 2,
         ").constant value debug (ChildTrace.erase before))",
         ").constant (value + 1) debug (ChildTrace.erase before))", 1),
        ("materialize-wrong-value", 2,
         ").materialize id value debug (ChildTrace.erase before))",
         ").materialize id (value + 1) debug (ChildTrace.erase before))", 1),
        ("literal-repeats-preparation", 2,
         ").operation opcode values debug (ChildTrace.erase before))",
         ").operation opcode values debug (ChildTrace.erase prepared))", 1),
        ("literal-wrong-cleanup", 2,
         "(if values.isEmpty then result else retire before.memory.memory.nextId result))",
         "(if values.isEmpty then result else retire prepared.memory.memory.nextId result))", 1),
        ("local-wrong-slot", 2,
         "opcode source selected repeated first debug (ChildTrace.erase before))",
         "opcode source (selected + 1) repeated first debug (ChildTrace.erase before))", 1),
        ("local-wrong-cleanup", 2,
         "(retire before.memory.memory.nextId result)) := by",
         "(retire prepared.memory.memory.nextId result)) := by", 1),
        ("lost-parent-token", 3, ".tokens = before.tokens", ".tokens = {}", 1),
        ("lost-native-scope", 3, ".native.scope = before.native.scope", ".native.scope = ⟨none, none, false⟩", 1),
        ("lost-protocol-history", 3, ".events = before.events ∧", ".events = [] ∧", 1),
        ("lost-transfer", 3, ".transferred = before.transferred", ".transferred = none", 1),
        ("lost-rejection", 3, ".rejected = before.rejected", ".rejected = none", 1),
        ("lost-normalization-history", 3,
         "(before : NormalizationOwnership.Trace.Recorded σ ε) :\n    (before.mapEffects project).events = before.events",
         "(before : NormalizationOwnership.Trace.Recorded σ ε) :\n    (before.mapEffects project).events = []", 1),
        ("lost-insertion-history", 3,
         "(before : Storage.Trace.Recorded σ ε) :\n    (before.mapEffects project).events = before.events",
         "(before : Storage.Trace.Recorded σ ε) :\n    (before.mapEffects project).events = []", 1),
    ):
        if parts[index].count(before) != count:
            raise ValueError("ambiguous captured step mutation: " + name)
        changed = parts.copy()
        changed[index] = changed[index].replace(before, after)
        variants.append((name, program(changed)))
    records = native.check_controls(output, env, lean, program(parts), variants, prefix="protocol-effects-")
    for record in records:
        if not record["expectedAcceptance"] and not re.search(
                r"error: (?:Not a definitional equality|Application type mismatch|Type mismatch|Tactic[^\n]*failed|unsolved goals)",
                (output / (record["name"] + ".stdout")).read_text()):
            raise ValueError("captured step control lacks a semantic proof failure: " + record["name"])
    return records
