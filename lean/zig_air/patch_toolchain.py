#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Apply the opt-in fresh-AIR hooks to an isolated pinned Zig source archive.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""

from pathlib import Path
import hashlib


def apply(source):
    changes = {}

    def replace(file, old, new):
        content = changes.get(file, (source / file).read_text())
        if content.count(old) != 1:
            raise ValueError("fresh-AIR patch anchor is not unique: " + file + ": " + old[:100])
        changes[file] = content.replace(old, new)

    replace("src/main.zig", "    var debug_incremental = false;",
            "    var debug_incremental = false;\n    var semantic_export_dir: ?[]const u8 = null;")
    replace("src/main.zig", '                    } else if (mem.eql(u8, arg, "--verbose-air")) {',
            '                    } else if (mem.cutPrefix(u8, arg, "--semantic-export=")) |path| {\n'
            '                        if (path.len == 0) fatal("empty semantic export directory", .{});\n'
            '                        semantic_export_dir = path;\n'
            '                    } else if (mem.eql(u8, arg, "--verbose-air")) {')
    replace("src/main.zig", "    const incremental = create_module.resolved_options.incremental;",
            "    const incremental = create_module.resolved_options.incremental;\n"
            '    if (semantic_export_dir != null and incremental) fatal("semantic export does not support incremental compilation", .{});')
    replace("src/main.zig", "        .cache_mode = cache_mode,",
            "        .cache_mode = if (semantic_export_dir != null) .none else cache_mode,\n"
            "        .semantic_export_dir = semantic_export_dir,")
    replace("src/Compilation.zig", "verbose_air: bool,", "verbose_air: bool,\nsemantic_export_dir: ?[]const u8,")
    replace("src/Compilation.zig", "    verbose_air: bool = false,",
            "    verbose_air: bool = false,\n    semantic_export_dir: ?[]const u8 = null,")
    replace("src/Compilation.zig", "            .verbose_air = options.verbose_air,",
            "            .verbose_air = options.verbose_air,\n            .semantic_export_dir = options.semantic_export_dir,")
    replace("src/Compilation.zig", "pub const MiscTask = enum {", "pub const MiscTask = enum {\n    semantic_export,")
    replace("src/Air.zig", "extra: std.ArrayList(u32),",
            "extra: std.ArrayList(u32),\nsemantic_export_zir: std.enums.EnumSet(std.zig.Zir.Inst.Tag) = .empty,\n"
            'semantic_export_slices: std.ArrayList(@import("SemanticValidity.zig").Slice) = .empty,')
    replace("src/Air.zig", "    air.extra.deinit(gpa);",
            "    air.extra.deinit(gpa);\n    air.semantic_export_slices.deinit(gpa);")
    replace("src/Sema.zig", "air_extra: std.ArrayList(u32) = .empty,",
            "air_extra: std.ArrayList(u32) = .empty,\nsemantic_export_zir: std.enums.EnumSet(Zir.Inst.Tag) = .empty,\n"
            'semantic_export_slices: std.ArrayList(@import("SemanticValidity.zig").Slice) = .empty,')
    replace("src/Sema.zig", "    sema.air_extra.deinit(gpa);",
            "    sema.air_extra.deinit(gpa);\n    sema.semantic_export_slices.deinit(gpa);")
    replace("src/Sema.zig", "        const inst = body[i];\n",
            "        const inst = body[i];\n"
            "        if (zcu.comp.semantic_export_dir != null) sema.semantic_export_zir.insert(tags[@intFromEnum(inst)]);\n")
    replace("src/Zcu/PerThread.zig", "        .instructions = sema.air_instructions.slice(),\n        .extra = sema.air_extra,",
            "        .instructions = sema.air_instructions.slice(),\n        .extra = sema.air_extra,\n"
            "        .semantic_export_zir = sema.semantic_export_zir,\n"
            "        .semantic_export_slices = sema.semantic_export_slices,")
    replace("src/Zcu/PerThread.zig", "        sema.air_instructions = .empty;\n        sema.air_extra = .empty;",
            "        sema.air_instructions = .empty;\n        sema.air_extra = .empty;\n"
            "        sema.semantic_export_slices = .empty;")
    slice_hook = ('try @import("SemanticValidity.zig").recordSlice(sema, block.isComptime(), src, result,\n'
                  '                semantic_first_result, ptr_or_slice, slice_ty, array_ty, start, end, slice_sentinel != null);')
    replace("src/Sema.zig", "            const result = try block.addTyOp(.ptr_cast, return_ty, new_ptr);",
            "            const semantic_first_result = sema.air_instructions.len;\n"
            "            const result = try block.addTyOp(.ptr_cast, return_ty, new_ptr);\n            " + slice_hook)
    replace("src/Sema.zig", "    const result = try block.addInst(.{\n        .tag = .slice,",
            "    const semantic_first_result = sema.air_instructions.len;\n"
            "    const result = try block.addInst(.{\n        .tag = .slice,")
    replace("src/Sema.zig", "    if (block.wantSafety()) {\n        // requirement: result[new_len] == slice_sentinel",
            "    " + slice_hook + "\n    if (block.wantSafety()) {\n        // requirement: result[new_len] == slice_sentinel")
    replace("src/Zcu/PerThread.zig", "    defer if (air_owned) air.deinit(gpa);",
            "    defer if (air_owned) air.deinit(gpa);\n\n"
            "    if (zcu.comp.semantic_export_dir != null) {\n"
            '        @import("../SemanticExport.zig").captureFunction(pt, func_index, &air) catch |err| {\n'
            '            zcu.comp.lockAndSetMiscFailure(.semantic_export, "fresh AIR capture failed: {s}", .{@errorName(err)});\n'
            "        };\n    }")
    modules = [Path(__file__).with_name(name) for name in ("SemanticExport.zig", "SemanticValidity.zig")]
    if any((source / "src" / module.name).exists() for module in modules):
        raise ValueError("semantic capture module already present")
    manifest = []
    for file, content in changes.items():
        path = source / file
        original = path.read_bytes()
        path.write_text(content)
        manifest.append({"file": file, "beforeSha256": hashlib.sha256(original).hexdigest(),
                         "afterSha256": hashlib.sha256(path.read_bytes()).hexdigest()})
    for module in modules:
        (source / "src" / module.name).write_bytes(module.read_bytes())
        manifest.append({"file": "src/" + module.name, "beforeSha256": None,
                         "afterSha256": hashlib.sha256(module.read_bytes()).hexdigest()})
    return manifest
