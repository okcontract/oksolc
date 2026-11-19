// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
//! Synchronous capture of fresh AIR, before legalization or ownership transfer.
//! Unsupported payloads are explicit. This file does not assert preservation.
const std = @import("std");
const Air = @import("Air.zig");
const Type = @import("Type.zig");
const Value = @import("Value.zig");
const Zcu = @import("Zcu.zig");
const InternPool = @import("InternPool.zig");
const SemanticValidity = @import("SemanticValidity.zig");
const Writer = std.Io.Writer;

fn json(w: *Writer, value: anytype) Writer.Error!void {
    try std.json.Stringify.value(value, .{}, w);
}

fn writeType(w: *Writer, ty: Type, zcu: *Zcu) Writer.Error!void {
    var remaining: usize = 1024;
    return writeTypeDepth(w, ty, zcu, 0, &remaining);
}

// Capturing must not trigger analysis or read unresolved container layout storage.
// Struct callers additionally exclude packed fields, whose offsets are not bytes.
fn resolvedLayout(ty: Type, zcu: *Zcu) bool {
    const unit: InternPool.AnalUnit = .wrap(.{ .type_layout = ty.toIntern() });
    if (std.debug.runtime_safety) zcu.outdated_lock.lockSharedUncancelable(zcu.comp.io);
    defer if (std.debug.runtime_safety) zcu.outdated_lock.unlockShared(zcu.comp.io);
    if (zcu.outdated.contains(unit) or zcu.potentially_outdated.contains(unit) or
        zcu.analysis_in_progress.contains(unit) or zcu.failed_analysis.contains(unit) or
        zcu.transitive_failed_analysis.contains(unit)) return false;
    return true;
}

fn resolvedStruct(ty: Type, zcu: *Zcu) ?InternPool.LoadedStructType {
    if (zcu.intern_pool.indexToKey(ty.toIntern()) != .struct_type) return null;
    const loaded = zcu.intern_pool.loadStructType(ty.toIntern());
    if (!loaded.want_layout or loaded.layout == .@"packed" or !resolvedLayout(ty, zcu)) return null;
    return loaded;
}

fn resolvedEnum(ty: Type, zcu: *Zcu) ?InternPool.LoadedEnumType {
    if (zcu.intern_pool.indexToKey(ty.toIntern()) != .enum_type) return null;
    const loaded = zcu.intern_pool.loadEnumType(ty.toIntern());
    if (!loaded.want_layout or !resolvedLayout(ty, zcu)) return null;
    return loaded;
}

fn layoutKnown(ty: Type, zcu: *Zcu, depth: u8, remaining: *usize) bool {
    if (depth >= 16 or remaining.* == 0) return false;
    remaining.* -= 1;
    return switch (ty.zigTypeTag(zcu)) {
        .int, .bool, .void, .pointer => true,
        .@"enum" => known: {
            const loaded = resolvedEnum(ty, zcu) orelse break :known false;
            break :known layoutKnown(.fromInterned(loaded.int_tag_type), zcu, depth + 1, remaining);
        },
        .array => layoutKnown(ty.childType(zcu), zcu, depth + 1, remaining),
        .@"struct" => known: {
            const loaded = resolvedStruct(ty, zcu) orelse break :known false;
            if (loaded.field_types.len > 64) break :known false;
            for (loaded.field_types.get(&zcu.intern_pool)) |field_ty| {
                if (!layoutKnown(.fromInterned(field_ty), zcu, depth + 1, remaining)) break :known false;
            }
            break :known true;
        },
        else => false,
    };
}

fn writeLayout(w: *Writer, ty: Type, zcu: *Zcu) Writer.Error!void {
    var remaining: usize = 1024;
    if (!layoutKnown(ty, zcu, 0, &remaining))
        return json(w, .{ .kind = "unsupported", .reason = "non-scalar-layout" });
    try json(w, .{ .kind = "abi", .bytes = ty.abiSize(zcu), .alignment = ty.abiAlignment(zcu).toByteUnits().? });
}

fn writeTypeDepth(w: *Writer, ty: Type, zcu: *Zcu, depth: u8, remaining: *usize) Writer.Error!void {
    if (depth >= 16) return json(w, .{ .kind = "unsupported", .reason = "type-depth-limit" });
    if (remaining.* == 0) return json(w, .{ .kind = "unsupported", .reason = "type-node-limit" });
    remaining.* -= 1;
    switch (ty.zigTypeTag(zcu)) {
        .int => {
            const info = ty.intInfo(zcu);
            try json(w, .{ .kind = "int", .bits = info.bits, .signedness = @tagName(info.signedness) });
        },
        .bool => try json(w, .{ .kind = "bool" }),
        .void => try json(w, .{ .kind = "void" }),
        .noreturn => try json(w, .{ .kind = "noreturn" }),
        .@"enum" => {
            const loaded = resolvedEnum(ty, zcu) orelse
                return json(w, .{ .kind = "unsupported", .reason = "unresolved-enum" });
            const declaration = loaded.zir_index.unwrap() orelse
                return json(w, .{ .kind = "unsupported", .reason = "generated-enum" });
            if (loaded.is_reified)
                return json(w, .{ .kind = "unsupported", .reason = "reified-enum" });
            const tag_type: Type = .fromInterned(loaded.int_tag_type);
            if (tag_type.zigTypeTag(zcu) != .int or tag_type.intInfo(zcu).bits > 512)
                return json(w, .{ .kind = "unsupported", .reason = "enum-backing-type" });
            if (loaded.field_names.len > 64 or loaded.field_names.len > remaining.*)
                return json(w, .{ .kind = "unsupported", .reason = "enum-field-limit" });
            remaining.* -= loaded.field_names.len;
            const ip = &zcu.intern_pool;
            const file = zcu.fileByIndex(declaration.resolveFile(ip));
            const source = file.source orelse
                return json(w, .{ .kind = "unsupported", .reason = "missing-enum-source" });
            var hash: [32]u8 = undefined;
            std.crypto.hash.sha2.Sha256.hash(source, &hash, .{});
            const hex = std.fmt.bytesToHex(hash, .lower);
            try w.writeAll("{\"kind\":\"enum\",\"identity\":");
            try json(w, .{ .name = loaded.fqn.toSlice(ip), .sourceFile = file.sub_file_path, .sourceSha256 = @as([]const u8, &hex) });
            try w.writeAll(",\"backingType\":");
            try writeTypeDepth(w, tag_type, zcu, depth + 1, remaining);
            try w.writeAll(",\"layout\":");
            try writeLayout(w, ty, zcu);
            try w.print(",\"nonexhaustive\":{},\"fields\":[", .{loaded.nonexhaustive});
            for (loaded.field_names.get(ip), 0..) |name, i| {
                if (i != 0) try w.writeByte(',');
                try w.print("{{\"index\":{d},\"name\":", .{i});
                try json(w, name.toSlice(ip));
                try w.writeAll(",\"value\":");
                if (loaded.field_value_map.unwrap() != null) {
                    var space: Value.BigIntSpace = undefined;
                    const value: Value = .fromInterned(loaded.field_values.get(ip)[i]);
                    try w.print("{f}", .{value.toBigInt(&space, zcu)});
                } else try w.print("{d}", .{i});
                try w.writeByte('}');
            }
            try w.writeAll("]}");
        },
        .pointer => {
            const info = ty.ptrInfo(zcu);
            try w.writeAll("{\"kind\":\"pointer\",\"flags\":");
            try json(w, .{
                .size = @tagName(info.flags.size),
                .alignment = info.flags.alignment.toByteUnits(),
                .isConst = info.flags.is_const,
                .isVolatile = info.flags.is_volatile,
                .allowZero = info.flags.is_allowzero,
                .addressSpace = @tagName(info.flags.address_space),
                .vectorIndex = if (info.flags.vector_index == .none) null else @as(?u16, @backingInt(info.flags.vector_index)),
                .hostSizeBytes = info.packed_offset.host_size,
                .bitOffset = info.packed_offset.bit_offset,
            });
            try w.writeAll(",\"child\":");
            try writeTypeDepth(w, ty.childType(zcu), zcu, depth + 1, remaining);
            try w.writeAll(",\"layout\":");
            try writeLayout(w, ty, zcu);
            try w.writeAll(",\"pointeeLayout\":");
            try writeLayout(w, ty.childType(zcu), zcu);
            try w.writeAll(",\"sentinel\":");
            if (ty.sentinel(zcu)) |sentinel| try writeRef(w, Air.internedToRef(sentinel.toIntern()), zcu) else try w.writeAll("null");
            try w.writeByte('}');
        },
        .array => {
            try w.print("{{\"kind\":\"array\",\"length\":{d},\"child\":", .{ty.arrayLen(zcu)});
            try writeTypeDepth(w, ty.childType(zcu), zcu, depth + 1, remaining);
            try w.writeAll(",\"layout\":");
            try writeLayout(w, ty, zcu);
            try w.writeAll(",\"sentinel\":");
            if (ty.sentinel(zcu)) |sentinel| try writeRef(w, Air.internedToRef(sentinel.toIntern()), zcu) else try w.writeAll("null");
            try w.writeByte('}');
        },
        .@"struct" => {
            const loaded = resolvedStruct(ty, zcu) orelse
                return json(w, .{ .kind = "unsupported", .reason = "unresolved-or-packed-struct" });
            const ip = &zcu.intern_pool;
            if (loaded.field_types.len > 64)
                return json(w, .{ .kind = "unsupported", .reason = "struct-field-limit" });
            for (0..loaded.field_types.len) |i| {
                if (loaded.field_is_comptime_bits.get(ip, i))
                    return json(w, .{ .kind = "unsupported", .reason = "comptime-struct-field" });
            }
            const file = zcu.fileByIndex(loaded.zir_index.resolveFile(ip));
            const source = file.source orelse
                return json(w, .{ .kind = "unsupported", .reason = "missing-struct-source" });
            var hash: [32]u8 = undefined;
            std.crypto.hash.sha2.Sha256.hash(source, &hash, .{});
            const hex = std.fmt.bytesToHex(hash, .lower);
            try w.writeAll("{\"kind\":\"struct\",\"identity\":");
            try json(w, .{ .name = loaded.fqn.toSlice(ip), .sourceFile = file.sub_file_path, .sourceSha256 = @as([]const u8, &hex) });
            try w.writeAll(",\"containerLayout\":");
            try json(w, @tagName(loaded.layout));
            try w.writeAll(",\"layout\":");
            try writeLayout(w, ty, zcu);
            try w.writeAll(",\"fields\":[");
            for (loaded.field_types.get(ip), 0..) |field_ty, i| {
                if (i != 0) try w.writeByte(',');
                try w.print("{{\"index\":{d},\"name\":", .{i});
                try json(w, loaded.field_names.get(ip)[i].toSlice(ip));
                try w.print(",\"offset\":{d},\"explicitAlignment\":", .{ty.structFieldOffset(i, zcu)});
                try json(w, ty.explicitFieldAlignment(i, zcu).toByteUnits());
                try w.writeAll(",\"type\":");
                try writeTypeDepth(w, .fromInterned(field_ty), zcu, depth + 1, remaining);
                try w.writeByte('}');
            }
            try w.writeAll("]}");
        },
        else => try json(w, .{ .kind = "unsupported", .zigTypeTag = @tagName(ty.zigTypeTag(zcu)) }),
    }
}

fn writeRef(w: *Writer, ref: Air.Inst.Ref, zcu: *Zcu) Writer.Error!void {
    if (ref == .none) return json(w, .{ .kind = "unsupported", .reason = "none-reference" });
    if (ref.toIndex()) |index| return json(w, .{ .kind = "instruction", .index = @backingInt(index) });
    var remaining: usize = 1024;
    return writeValue(w, .fromInterned(ref.toInterned().?), zcu, 0, &remaining);
}

// Preserve the actual anonymous zero-sized object behind an empty slice.
// A zero length alone does not admit null, undefined or arbitrary pointers.
fn emptySliceOrigin(value: Value, zcu: *Zcu) ?InternPool.Key.Ptr.BaseAddr.Uav {
    const slice = switch (zcu.intern_pool.indexToKey(value.toIntern())) {
        .slice => |slice| slice,
        else => return null,
    };
    if (value.sliceLen(zcu) != 0) return null;
    const pointer = switch (zcu.intern_pool.indexToKey(slice.ptr)) {
        .ptr => |pointer| pointer,
        else => return null,
    };
    if (pointer.byte_offset != 0) return null;
    const origin = switch (pointer.base_addr) {
        .uav => |origin| origin,
        else => return null,
    };
    const object: Value = .fromInterned(origin.val);
    const ty = object.typeOf(zcu);
    if (object.isUndef(zcu) or ty.zigTypeTag(zcu) != .array or ty.arrayLenIncludingSentinel(zcu) != 0)
        return null;
    return origin;
}

fn writeValue(w: *Writer, value: Value, zcu: *Zcu, depth: u8, remaining: *usize) Writer.Error!void {
    if (depth >= 16 or remaining.* == 0)
        return json(w, .{ .kind = "unsupported", .reason = "constant-expansion-limit" });
    remaining.* -= 1;
    const ty = value.typeOf(zcu);
    if (value.isUndef(zcu)) {
        // Preserve undefinedness as data. A decoder must explicitly support
        // partial aggregate copies; this is never an initialized scalar value.
        try w.writeAll("{\"kind\":\"undefined\",\"type\":");
        try writeType(w, ty, zcu);
        return w.writeByte('}');
    }
    if (ty.zigTypeTag(zcu) == .@"fn") {
        // Coerced/extern/indirect callees remain explicit unsupported values.
        // A local build name is only a join key; the source identity must agree
        // with the separately captured body before a consumer can use it.
        const func = switch (zcu.intern_pool.indexToKey(value.toIntern())) {
            .func => |func| func,
            else => return json(w, .{ .kind = "unsupported", .reason = "non-body-function" }),
        };
        try w.writeAll("{\"kind\":\"function\",\"identity\":");
        try writeFunctionIdentity(w, func, zcu);
        return w.writeByte('}');
    }
    if (ty.zigTypeTag(zcu) == .void) return json(w, .{ .kind = "unit" });
    if (ty.zigTypeTag(zcu) == .@"struct") {
        const loaded = resolvedStruct(ty, zcu) orelse
            return json(w, .{ .kind = "unsupported", .reason = "aggregate-type" });
        const aggregate = switch (zcu.intern_pool.indexToKey(value.toIntern())) {
            .aggregate => |aggregate| aggregate,
            else => return json(w, .{ .kind = "unsupported", .reason = "aggregate-storage" }),
        };
        if (loaded.field_types.len > 64 or aggregate.storage == .bytes)
            return json(w, .{ .kind = "unsupported", .reason = "aggregate-storage" });
        try w.writeAll("{\"kind\":\"aggregate\",\"type\":");
        try writeType(w, ty, zcu);
        try w.writeAll(",\"fields\":[");
        for (0..loaded.field_types.len) |i| {
            if (i != 0) try w.writeByte(',');
            const child = switch (aggregate.storage) {
                .elems => |elems| elems[i],
                .repeated_elem => |elem| elem,
                .bytes => unreachable,
            };
            try writeValue(w, .fromInterned(child), zcu, depth + 1, remaining);
        }
        return w.writeAll("]}");
    }
    if (ty.zigTypeTag(zcu) == .pointer and ty.ptrInfo(zcu).flags.size == .slice) {
        if (emptySliceOrigin(value, zcu)) |origin| {
            try w.writeAll("{\"kind\":\"emptySlice\",\"type\":");
            try writeType(w, ty, zcu);
            try w.writeAll(",\"length\":0,\"origin\":{\"kind\":\"unnamedConstant\",\"byteOffset\":0,\"objectType\":");
            try writeType(w, Value.fromInterned(origin.val).typeOf(zcu), zcu);
            try w.writeAll(",\"pointerType\":");
            try writeType(w, .fromInterned(origin.orig_ty), zcu);
            return w.writeAll("}}");
        }
    }
    if (ty.zigTypeTag(zcu) != .int and ty.zigTypeTag(zcu) != .bool)
        return json(w, .{ .kind = "unsupported", .reason = "constant-type" });
    // BigInt.format is exact below its fixed scratch capacity (at least 2048
    // bits on supported hosts). Keep a smaller explicit bound; never accept its
    // fallback "(BigInt)" text as an integer or truncate to a machine word.
    if (ty.zigTypeTag(zcu) == .int and ty.intInfo(zcu).bits > 512)
        return json(w, .{ .kind = "unsupported", .reason = "constant-width-above-512" });
    var space: Value.BigIntSpace = undefined;
    const number = value.toBigInt(&space, zcu);
    try w.writeAll("{\"kind\":\"constant\",\"type\":");
    try writeType(w, ty, zcu);
    try w.print(",\"value\":{f}}}", .{number});
}

fn writeFunctionIdentity(w: *Writer, func: InternPool.Key.Func, zcu: *Zcu) Writer.Error!void {
    // indexToKey folds func_coerced into Key.Func; its original type is the
    // discriminator. Do not bind a coerced call to an uncoerced captured body.
    if (func.ty != func.uncoerced_ty)
        return json(w, .{ .kind = "unsupported", .reason = "coerced-function" });
    const ip = &zcu.intern_pool;
    const nav = ip.getNav(func.owner_nav);
    const declaration = if (func.generic_owner == .none) nav else ip.getNav(zcu.funcInfo(func.generic_owner).owner_nav);
    const analysis = declaration.analysis orelse
        return json(w, .{ .kind = "unsupported", .reason = "missing-function-source" });
    const file = zcu.fileByIndex(analysis.zir_index.resolveFile(ip));
    const source = file.source orelse
        return json(w, .{ .kind = "unsupported", .reason = "missing-function-source" });
    var hash: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(source, &hash, .{});
    const hex = std.fmt.bytesToHex(hash, .lower);
    try json(w, .{ .name = nav.fqn.toSlice(ip), .sourceFile = file.sub_file_path, .sourceSha256 = @as([]const u8, &hex) });
}

fn writeSpecialization(w: *Writer, func: InternPool.Key.Func, zcu: *Zcu) Writer.Error!void {
    const ip = &zcu.intern_pool;
    const owner = zcu.funcInfo(func.generic_owner);
    const signature = zcu.typeToFunc(.fromInterned(owner.ty)).?;
    try w.writeAll("{\"schema\":\"oksolc.generic-instance.v1\",\"owner\":");
    try writeFunctionIdentity(w, owner, zcu);
    try w.print(",\"sourceNoaliasBits\":{d},\"sourceComptimeBits\":{d},\"sourceParameterCount\":{d},\"arguments\":[", .{
        signature.noalias_bits, signature.comptime_bits, signature.param_types.len,
    });
    var runtime_index: usize = 0;
    for (func.comptime_args.get(ip), 0..) |arg, i| {
        if (i != 0) try w.writeByte(',');
        if (arg == .none) {
            try json(w, .{ .kind = "runtime", .runtimeIndex = runtime_index });
            runtime_index += 1;
        } else {
            const value: Value = .fromInterned(arg);
            if (value.typeOf(zcu).zigTypeTag(zcu) == .type) {
                try w.writeAll("{\"kind\":\"type\",\"value\":");
                try writeType(w, value.toType(), zcu);
                try w.writeByte('}');
            } else {
                try w.writeAll("{\"kind\":\"value\",\"value\":");
                try writeRef(w, Air.internedToRef(arg), zcu);
                try w.writeByte('}');
            }
        }
    }
    try w.writeAll("]}");
}

fn writeIndices(w: *Writer, indices: []const Air.Inst.Index) Writer.Error!void {
    try w.writeByte('[');
    for (indices, 0..) |index, i| {
        if (i != 0) try w.writeByte(',');
        try json(w, @backingInt(index));
    }
    try w.writeByte(']');
}

fn writeSliceValidity(w: *Writer, item: SemanticValidity.Slice, visited: std.bit_set.Dynamic, zcu: *Zcu) !void {
    if (item.src.offset == .unneeded) return error.MissingValiditySource;
    const source = item.src.upgradeOrLost(zcu) orelse return error.MissingValiditySource;
    const span = try source.span(zcu);
    const bytes = try source.file_scope.getSource(zcu);
    if (span.start > span.main or span.main > span.end or span.end > bytes.len)
        return error.InvalidValiditySourceSpan;
    var hash: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(bytes, &hash, .{});
    const hex = std.fmt.bytesToHex(hash, .lower);
    try w.writeAll("{\"source\":");
    try json(w, .{ .file = source.file_scope.sub_file_path, .sha256 = @as([]const u8, &hex), .span = span });
    try w.writeAll(",\"anchor\":");
    if (item.anchor) |anchor| {
        const index = @backingInt(anchor);
        if (index >= visited.bit_length) return error.InvalidValidityAnchor;
        try json(w, .{ .kind = "beforeInstruction", .index = index, .inSupportedBody = visited.isSet(index) });
    } else {
        try json(w, .{ .kind = "unsupported", .reason = "result-has-no-unique-instruction" });
    }
    try w.writeAll(",\"start\":");
    try writeRef(w, item.start, zcu);
    try w.writeAll(",\"end\":");
    try writeRef(w, item.end, zcu);
    try w.writeAll(",\"upperBound\":");
    switch (item.bound) {
        .array => |length| try json(w, .{ .kind = "arrayLength", .value = length }),
        .slice => |original| {
            try w.writeAll("{\"kind\":\"sliceLength\",\"original\":");
            try writeRef(w, original, zcu);
            try w.writeByte('}');
        },
        .unbounded => try json(w, .{ .kind = "unboundedPointer", .requiresMemoryValidity = true }),
        .unsupported => try json(w, .{ .kind = "unsupported" }),
    }
    try w.writeAll(",\"unsupportedReason\":");
    if (item.unsupported) |reason| try json(w, @tagName(reason)) else try w.writeAll("null");
    try w.writeByte('}');
}

fn collectBodyEntries(air: *const Air, gpa: std.mem.Allocator) !std.bit_set.Dynamic {
    var visited = try std.bit_set.Dynamic.initEmpty(gpa, air.instructions.len);
    errdefer visited.deinit(gpa);
    var pending: std.ArrayList(Air.Inst.Index) = .empty;
    defer pending.deinit(gpa);
    try pending.appendSlice(gpa, air.getMainBody());
    while (pending.pop()) |index| {
        const i = @backingInt(index);
        if (i >= air.instructions.len) return error.InvalidBodyIndex;
        if (visited.isSet(i)) continue;
        visited.set(i);
        switch (air.instructions.items(.tag)[i]) {
            .block, .loop => try pending.appendSlice(gpa, air.unwrapBlock(index).body),
            .cond_br => {
                const branch = air.unwrapCondBr(index);
                try pending.appendSlice(gpa, branch.then_body);
                try pending.appendSlice(gpa, branch.else_body);
            },
            // Other containers are unsupported. Their unvisited descendants
            // cannot be treated as unreachable by a semantic consumer.
            else => {},
        }
    }
    return visited;
}

fn writeInstruction(w: *Writer, air: *const Air, index: Air.Inst.Index, visited: bool, zcu: *Zcu) Writer.Error!void {
    const inst = air.instructions.get(@backingInt(index));
    try w.print("{{\"index\":{d},\"tag\":", .{@backingInt(index)});
    try json(w, @tagName(inst.tag));
    try w.print(",\"payloadVisited\":{}", .{visited});
    if (!visited) {
        // Sema can leave unused placeholders in the instruction table. Their
        // data union must not be decoded as a runtime instruction payload.
        return w.writeAll(",\"unsupportedPayload\":true,\"reason\":\"outside-decoded-body-closure\"}");
    }
    try w.writeAll(",\"type\":");
    try writeType(w, air.typeOfIndex(index, &zcu.intern_pool), zcu);
    switch (inst.tag) {
        .arg => try w.print(",\"zirParameterIndex\":{d}", .{inst.data.arg.zir_param_index}),
        .call, .call_always_tail, .call_never_tail, .call_never_inline => {
            const call = air.unwrapCall(index);
            try w.writeAll(",\"callee\":");
            try writeRef(w, call.callee, zcu);
            try w.writeAll(",\"arguments\":[");
            for (call.args, 0..) |arg, i| {
                if (i != 0) try w.writeByte(',');
                try writeRef(w, arg, zcu);
            }
            try w.writeByte(']');
        },
        .add,
        .add_safe,
        .add_wrap,
        .sub,
        .sub_safe,
        .sub_wrap,
        .mul,
        .mul_safe,
        .mul_wrap,
        .bit_and,
        .bit_or,
        .xor,
        .shr,
        .shl,
        .cmp_eq,
        .cmp_neq,
        .cmp_lt,
        .cmp_lte,
        .cmp_gt,
        .cmp_gte,
        .store,
        .store_safe,
        .memcpy,
        => {
            try w.writeAll(",\"lhs\":");
            try writeRef(w, inst.data.bin_op.lhs, zcu);
            try w.writeAll(",\"rhs\":");
            try writeRef(w, inst.data.bin_op.rhs, zcu);
        },
        .ret, .ret_safe, .ret_load => {
            try w.writeAll(",\"operand\":");
            try writeRef(w, inst.data.un_op, zcu);
        },
        .int_cast, .int_cast_safe, .bit_cast, .ptr_cast, .array_to_slice, .trunc, .load, .slice_len, .slice_ptr, .ptr_slice_len_ptr, .ptr_slice_ptr_ptr, .not => {
            try w.writeAll(",\"operand\":");
            try writeRef(w, inst.data.ty_op.operand, zcu);
        },
        .alloc => try w.writeAll(",\"allocationKind\":\"stack\""),
        .unreach => {},
        .struct_field_ptr => {
            const field = air.extraData(Air.StructField, inst.data.ty_pl.payload).data;
            try w.writeAll(",\"operand\":");
            try writeRef(w, field.struct_operand, zcu);
            try w.print(",\"fieldIndex\":{d}", .{field.field_index});
        },
        .struct_field_ptr_index_0, .struct_field_ptr_index_1, .struct_field_ptr_index_2, .struct_field_ptr_index_3 => {
            try w.writeAll(",\"operand\":");
            try writeRef(w, inst.data.ty_op.operand, zcu);
            const field: u32 = switch (inst.tag) {
                .struct_field_ptr_index_0 => 0,
                .struct_field_ptr_index_1 => 1,
                .struct_field_ptr_index_2 => 2,
                .struct_field_ptr_index_3 => 3,
                else => unreachable,
            };
            try w.print(",\"fieldIndex\":{d}", .{field});
        },
        .ptr_add, .ptr_sub, .ptr_elem_ptr, .slice_elem_ptr, .slice => {
            const bin = air.extraData(Air.Bin, inst.data.ty_pl.payload).data;
            try w.writeAll(",\"lhs\":");
            try writeRef(w, bin.lhs, zcu);
            try w.writeAll(",\"rhs\":");
            try writeRef(w, bin.rhs, zcu);
        },
        .block, .loop => {
            try w.writeAll(",\"body\":");
            try writeIndices(w, air.unwrapBlock(index).body);
        },
        .repeat => try w.print(",\"target\":{d}", .{@backingInt(inst.data.repeat.loop_inst)}),
        .br => {
            try w.print(",\"target\":{d},\"operand\":", .{@backingInt(inst.data.br.block_inst)});
            try writeRef(w, inst.data.br.operand, zcu);
        },
        .cond_br => {
            const branch = air.unwrapCondBr(index);
            try w.writeAll(",\"condition\":");
            try writeRef(w, branch.condition, zcu);
            try w.writeAll(",\"thenBody\":");
            try writeIndices(w, branch.then_body);
            try w.writeAll(",\"elseBody\":");
            try writeIndices(w, branch.else_body);
        },
        .dbg_stmt, .dbg_var_val, .dbg_var_ptr, .dbg_arg_inline => {
            try w.writeAll(",\"debugOnly\":true");
        },
        else => try w.writeAll(",\"unsupportedPayload\":true"),
    }
    try w.writeByte('}');
}

pub fn captureFunction(pt: Zcu.PerThread, func_index: InternPool.Index, air: *const Air) !void {
    const zcu = pt.zcu;
    const comp = zcu.comp;
    const ip = &zcu.intern_pool;
    const func = zcu.funcInfo(func_index);
    const nav = ip.getNav(func.owner_nav);
    const name = nav.fqn.toSlice(ip);
    const declaration = if (func.generic_owner == .none) nav else ip.getNav(zcu.funcInfo(func.generic_owner).owner_nav);
    const file = zcu.fileByIndex(declaration.analysis.?.zir_index.resolveFile(ip));
    const mod = file.mod.?;
    const target = mod.resolved_target.result;
    const signature = zcu.typeToFunc(.fromInterned(func.ty)).?;
    var visited = try collectBodyEntries(air, comp.gpa);
    defer visited.deinit(comp.gpa);
    const dir = try std.Io.Dir.cwd().openDir(comp.io, comp.semantic_export_dir.?, .{});
    defer dir.close(comp.io);
    // Names are local to this build. Specialization/source metadata enables
    // checked joins; it does not prove specialization or parameter contracts.
    var hash: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(name, &hash, .{});
    var path_buffer: [69]u8 = undefined;
    const path = try std.mem.print(&path_buffer, "{x}.json", .{&hash});
    const output = try dir.createFile(comp.io, path, .{ .exclusive = true });
    defer output.close(comp.io);
    var buffer: [4096]u8 = undefined;
    var file_writer = output.writer(comp.io, &buffer);
    const w = &file_writer.interface;
    try w.writeAll("{\"schema\":\"oksolc.fresh-air.v3\",\"capturePoint\":\"after-sema-before-legalize\",\"name\":");
    try json(w, name);
    try w.writeAll(",\"sourceFile\":");
    try json(w, file.sub_file_path);
    try w.writeAll(",\"sourceSha256\":");
    std.crypto.hash.sha2.Sha256.hash(file.source orelse return error.SourceUnavailable, &hash, .{});
    const hex = std.fmt.bytesToHex(hash, .lower);
    try json(w, @as([]const u8, &hex));
    try w.writeAll(",\"configuration\":");
    try json(w, .{
        .optimize = switch (mod.optimize_mode) {
            .debug => "Debug",
            .safe => "ReleaseSafe",
            .fast => "ReleaseFast",
            .small => "ReleaseSmall",
        },
        .useLlvm = comp.config.use_llvm,
        .isTest = comp.config.is_test,
        .arch = @tagName(target.cpu.arch),
        .pointerBits = target.ptrBitWidth(),
        .endianness = @tagName(target.cpu.arch.endian()),
        .cpu = target.cpu.model.name,
        .cpuFeatures = target.cpu.features.ints,
        .os = @tagName(target.os.tag),
        .osVersionRange = target.os.versionRange(),
        .abi = @tagName(target.abi),
        .objectFormat = @tagName(target.ofmt),
    });
    try w.writeAll(",\"signature\":{\"callingConvention\":");
    try json(w, signature.cc);
    try w.print(",\"genericInstance\":{},\"varArgs\":{},\"noaliasBits\":{d},\"parameters\":[", .{
        func.generic_owner != .none, signature.is_var_args, signature.noalias_bits,
    });
    for (signature.param_types.get(ip), 0..) |ty, i| {
        if (i != 0) try w.writeByte(',');
        try writeType(w, .fromInterned(ty), zcu);
    }
    try w.writeAll("],\"returnType\":");
    try writeType(w, .fromInterned(signature.return_type), zcu);
    try w.writeByte('}');
    // The v1 extension is emitted only for previously unsupported generic
    // instances. Existing strict decoders continue to reject these records.
    if (func.generic_owner != .none) {
        try w.writeAll(",\"specialization\":");
        try writeSpecialization(w, func, zcu);
    }
    try w.writeAll(",\"sourceOperationTags\":[");
    var tags = air.semantic_export_zir.iterator();
    var first = true;
    while (tags.next()) |tag| {
        if (!first) try w.writeByte(',');
        first = false;
        try json(w, @tagName(tag));
    }
    try w.writeAll("],\"sourceValidityConditionsPreserved\":false,\"sourceValidity\":{\"schema\":\"oksolc.source-validity.v1\",\"coverage\":\"runtime-slice-results\",\"complete\":false,\"slices\":[");
    for (air.semantic_export_slices.items, 0..) |item, i| {
        if (i != 0) try w.writeByte(',');
        try writeSliceValidity(w, item, visited, zcu);
    }
    try w.writeAll("]},\"body\":");
    try writeIndices(w, air.getMainBody());
    try w.writeAll(",\"bodyTraversal\":\"supported-structured-containers-only\",\"instructions\":[");
    for (0..air.instructions.len) |i| {
        if (i != 0) try w.writeByte(',');
        try writeInstruction(w, air, @fromBackingInt(@intCast(i)), visited.isSet(i), zcu);
    }
    try w.writeAll("]}\n");
    // Failure is a compilation error, including final buffered writes. Partial
    // files never form accepted exports: the owner must require process success.
    try w.flush();
}
