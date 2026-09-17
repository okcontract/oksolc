// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Inspection records never serve as compiler-cache entries.
pub const application_id = 0x4f4b5549;
pub const version = 4;
// A receipt permits reusing an inspection snapshot after checking its inputs;
// it is never consumed by compiler caches.
pub const upgrade_v1 =
    \\CREATE TABLE live_receipt (
    \\ compilation INTEGER PRIMARY KEY REFERENCES compilation(id) ON DELETE CASCADE,
    \\ context TEXT NOT NULL, manifest TEXT NOT NULL CHECK(json_valid(manifest)), seal TEXT NOT NULL
    \\) STRICT;
    \\PRAGMA user_version=2;
;
pub const create =
    \\CREATE TABLE compilation (
    \\ id INTEGER PRIMARY KEY, label TEXT NOT NULL, origin TEXT NOT NULL,
    \\ created_at TEXT NOT NULL DEFAULT (strftime('%Y-%m-%dT%H:%M:%fZ','now')),
    \\ request TEXT NOT NULL CHECK(json_valid(request)),
    \\ output TEXT NOT NULL CHECK(json_valid(output)),
    \\ request_sha256 TEXT NOT NULL, output_sha256 TEXT NOT NULL
    \\) STRICT;
    \\CREATE TABLE source (
    \\ compilation INTEGER NOT NULL REFERENCES compilation(id) ON DELETE CASCADE,
    \\ name TEXT NOT NULL, compiler_id INTEGER, content TEXT, ast TEXT,
    \\ PRIMARY KEY(compilation,name)
    \\) STRICT;
    \\CREATE INDEX source_id ON source(compilation,compiler_id);
    \\CREATE TABLE contract (
    \\ compilation INTEGER NOT NULL REFERENCES compilation(id) ON DELETE CASCADE,
    \\ source TEXT NOT NULL, name TEXT NOT NULL, data TEXT NOT NULL CHECK(json_valid(data)),
    \\ PRIMARY KEY(compilation,source,name)
    \\) STRICT;
    \\CREATE TABLE diagnostic (
    \\ compilation INTEGER NOT NULL REFERENCES compilation(id) ON DELETE CASCADE,
    \\ ordinal INTEGER NOT NULL, source TEXT, severity TEXT, data TEXT NOT NULL CHECK(json_valid(data)),
    \\ PRIMARY KEY(compilation,ordinal)
    \\) STRICT;
    \\CREATE INDEX diagnostic_source ON diagnostic(compilation,source);
    \\CREATE TABLE node (
    \\ compilation INTEGER NOT NULL REFERENCES compilation(id) ON DELETE CASCADE,
    \\ id INTEGER NOT NULL, source TEXT NOT NULL, kind TEXT NOT NULL, name TEXT,
    \\ src TEXT, name_src TEXT, reference INTEGER, import_path TEXT,
    \\ PRIMARY KEY(compilation,id)
    \\) STRICT;
    \\CREATE INDEX node_source ON node(compilation,source);
    \\CREATE INDEX node_reference ON node(compilation,reference);
    \\CREATE INDEX node_name ON node(compilation,name);
    \\CREATE VIEW symbol AS SELECT * FROM node WHERE name IS NOT NULL AND name <> '' AND kind IN (
    \\ 'ContractDefinition','FunctionDefinition','ModifierDefinition','EventDefinition',
    \\ 'ErrorDefinition','StructDefinition','EnumDefinition','EnumValue',
    \\ 'VariableDeclaration','UserDefinedValueTypeDefinition');
    \\PRAGMA application_id=0x4f4b5549;
    \\PRAGMA user_version=1;
++ upgrade_v1 ++ "PRAGMA user_version=4;";
