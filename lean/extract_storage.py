#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Extract the production insertion ownership protocol, failing closed on changes
outside its primitive contracts. Parsing and primitive identification are trusted;
cleanup and transfer control flow are emitted as executable Lean program data.
"""
import argparse
import hashlib
from pathlib import Path
import re

from extract_compiler import Parser, Unsupported

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "src/libevmasm/expression_classes.zig"
OUTPUT = ROOT / "lean/Compiler/Extraction/StorageProgram.lean"
LEXER = re.compile(r"'(?:[^'\\\n]|\\.)'|" + r'\s+|//[^\n]*|@?"(?:[^"\\\n]|\\.)*"|@[A-Za-z_][A-Za-z_0-9]*|'
                   r'[A-Za-z_][A-Za-z_0-9]*|0x[0-9a-fA-F]+|[0-9]+|>=|<=|-=|==|!=|=>|'
                   r'[{}()\[\].,:;?!=~*+&|<>/%^\-]')
FLAGS = {"normalized_owned": "normalized", "representative_arguments_owned": "arguments",
         "item_allocation_owned": "allocation", "item_value_owned": "value"}
CAPACITY_FIELD = "test_id_limit: if (builtin.is_test) Id else void = if (builtin.is_test) invalid_id else {},"


def lex(source):
    result, pos = [], 0
    for match in LEXER.finditer(source):
        if match.start() != pos:
            raise Unsupported("unrecognized storage source token at " + str(pos))
        pos = match.end()
        value = match.group()
        if not value.isspace() and not value.startswith("//"):
            result.append(value)
    if pos != len(source):
        raise Unsupported("unrecognized storage source suffix")
    return result


class StorageParser(Parser):
    def __init__(self, items):
        self.items, self.pos = items, 0

    def expect(self, source):
        for expected in lex(source):
            actual = self.pop()
            if actual != expected:
                raise Unsupported(f"storage expected {expected!r}, found {actual!r} at token {self.pos}")

    def flag(self):
        name = self.ident()
        if name not in FLAGS:
            raise Unsupported("unmodeled storage flag: " + name)
        return FLAGS[name]

    def boolean(self):
        value = self.pop()
        if value not in ("true", "false"):
            raise Unsupported("storage flag requires a boolean literal")
        return value

    def cleanup(self):
        if self.take("if"):
            self.expect("(")
            flag = self.flag()
            self.expect(")")
            release = self.release()
            return f"(.guarded .{flag} .{release})"
        self.expect("{")
        releases = []
        while not self.take("}"):
            releases.append("." + self.release())
        return "(.sequence [" + ", ".join(releases) + "])"

    def release(self):
        first = self.pop()
        if first == "owned_item":
            self.expect(".deinit(self.allocator);")
            return "value"
        if first != "self":
            raise Unsupported("unsupported cleanup receiver")
        self.expect(".")
        field = self.pop()
        if field == "allocator":
            self.expect(".")
            method = self.pop()
            self.expect("(")
            arg = self.pop()
            self.expect(");")
            known = {("free", "normalized"): "normalized", ("free", "representative_arguments"): "arguments",
                     ("destroy", "owned_item"): "allocation"}
            if (method, arg) not in known:
                raise Unsupported("unmodeled storage release")
            return known[method, arg]
        if field == "representatives":
            self.expect(".items")
            if self.take("["):
                self.expect("self.representatives.items.len - 1].deinit(self.allocator);")
                return "lastValue"
            self.expect(".len -= 1;")
            return "pop"
        raise Unsupported("unsupported cleanup field")

    def block(self):
        self.expect("{")
        result = self.sequence()
        self.expect("}")
        return result

    def sequence(self):
        if self.peek() == "}":
            return ".done"
        head = self.pop()
        if head in ("defer", "errdefer"):
            cleanup = self.cleanup()
            return f"(.scope {'true' if head == 'errdefer' else 'false'} {cleanup} {self.sequence()})"
        if head == "if":
            self.expect("(")
            condition = self.pop()
            if condition == "deterministic":
                self.expect(")")
                yes = self.block()
                no = self.block() if self.take("else") else ".done"
                return f"(.branch .deterministic {yes} {no} {self.sequence()})"
            if condition == "self":
                self.expect(".representatives.items.len >= self.idLimit()) return error.ExpressionCapacity;")
                return "(.branch .noRoom .capacityError .done " + self.sequence() + ")"
            raise Unsupported("unsupported storage branch")
        if head == "var" or head in FLAGS:
            if head == "var":
                flag = self.flag()
            else:
                flag = FLAGS[head]
            self.expect("=")
            value = self.boolean()
            self.expect(";")
            return f"(.command (.flag .{flag} {value}) {self.sequence()})"
        if head == "const":
            name = self.ident()
            if name == "representative_arguments":
                self.expect("= if (deterministic) try self.allocator.dupe(Id, normalized) else blk: {")
                flag = self.flag()
                self.expect("=")
                value = self.boolean()
                self.expect("; break :blk normalized; };")
                yes = "(.command .duplicateArguments .done)"
                no = f"(.command (.flag .{flag} {value}) (.command .aliasArguments .done))"
                return f"(.branch .deterministic {yes} {no} {self.sequence()})"
            if name == "owned_item":
                self.expect("= try self.allocator.create(AssemblyItem);")
                return "(.command .createItem " + self.sequence() + ")"
            if name == "id":
                self.expect(": Id = @intCast(self.representatives.items.len);")
                return "(.command .captureId " + self.sequence() + ")"
            raise Unsupported("unmodeled storage local: " + name)
        if head == "owned_item":
            self.expect(".* = try item.clone(self.allocator);")
            return "(.command .cloneItem " + self.sequence() + ")"
        if head == "try":
            self.expect("self.")
            field = self.pop()
            if field == "representatives":
                self.expect(".append(self.allocator, .{ .id = id, .item = owned_item,"
                            " .arguments = representative_arguments, .sequence_number = sequence_number, });")
                operation = "append"
            elif field == "publishOwned":
                self.expect("(makeKey(item, normalized, sequence_number), id);")
                operation = "publish"
            else:
                raise Unsupported("unmodeled storage try target")
            return "(.command ." + operation + " " + self.sequence() + ")"
        if head == "return":
            self.expect("id;")
            if self.peek() != "}":
                raise Unsupported("unreachable storage suffix")
            return ".ret"
        raise Unsupported("unmodeled storage statement: " + head)


def function(data, header):
    items = lex(data.decode("utf-8"))
    signature = lex(header)
    positions = [i for i in range(len(items)) if items[i:i + len(signature)] == signature]
    if len(positions) != 1:
        raise Unsupported("missing or ambiguous storage function signature")
    parser = StorageParser(items[positions[0] + len(signature):])
    return parser


def struct_member(data, header, fields, name, signature):
    """Admit one member and the owner's complete reviewed instance fields.

    Methods may precede later fields in Zig. Scan the entire owning struct so
    an added field cannot silently escape initialization/ownership admission.
    """
    return struct_member_body(function(data, header), fields, name, signature)


def struct_member_body(owner, fields, name, signature):
    """Read one member from an already selected owning struct token view."""
    owner.expect('struct { ' + fields)
    bodies, depth, parens = [], 1, 0
    while depth:
        if depth == 1 and parens == 0 and owner.items[owner.pos + 1:owner.pos + 2] == [':']:
            raise Unsupported('unreviewed struct field or typed declaration')
        if depth == 1 and owner.items[owner.pos:owner.pos + 3] == ['pub', 'fn', name]:
            owner.expect(signature + ' {')
            body, nested = [], 1
            while nested:
                token = owner.pop()
                nested += (token == '{') - (token == '}')
                if nested:
                    body.append(token)
            bodies.append(body)
        else:
            token = owner.pop()
            depth += (token == '{') - (token == '}')
            parens += (token == '(') - (token == ')')
    owner.expect(';')
    if len(bodies) != 1:
        raise Unsupported('missing or ambiguous struct member: ' + name)
    return StorageParser(bodies[0])


def check_capacity_limit(data):
    # Only Zig test binaries carry the small-graph limit. The admitted
    # production guard still reserves exactly the maximum u32 ID.
    function(data, "const std =").expect('@import("std");')
    function(data, "const builtin =").expect('@import("builtin");')
    function(data, "pub const invalid_id =").expect("std.math.maxInt(Id);")
    function(data, CAPACITY_FIELD)
    function(data, "fn idLimit(self: *const ExpressionClasses) Id").expect(
        "{ return if (builtin.is_test) self.test_id_limit else invalid_id; }")


def check_publication(data):
    # This contract consumes the incoming key even on replacement. A plain
    # HashMap.put retains the old key and does not satisfy that contract.
    p = function(data, "fn publishOwned(self: *ExpressionClasses, key: ExpressionKey, id: Id) std.mem.Allocator.Error!void")
    p.expect("{ const entry = try self.expressions.getOrPut(self.allocator, key);"
             " if (entry.found_existing) self.allocator.free(entry.key_ptr.arguments);"
             " entry.key_ptr.* = key; entry.value_ptr.* = id; }")


def extract(data):
    check_capacity_limit(data)
    check_publication(data)
    for header, body in [
        ('const AssemblyItemModule =', '@import("assembly_item.zig");'),
        ('const InstructionModule =', '@import("instruction.zig");'),
        ('const AssemblyItem =', 'AssemblyItemModule.AssemblyItem;'),
        ('const Instruction =', 'InstructionModule.Instruction;'),
        ('pub const Expression = struct',
         '{ id: Id, item: *AssemblyItem, arguments: []Id, sequence_number: u32 = 0,'),
    ]:
        function(data, header).expect(body)
    items = lex(data.decode("utf-8"))
    binding = lex("pub const Id = u32;")
    if sum(items[i:i+len(binding)] == binding for i in range(len(items))) != 1:
        raise Unsupported("storage ID width changed")
    parser = function(data, "fn insertOwned(self: *ExpressionClasses, item: *const AssemblyItem,"
                      " normalized: []Id, deterministic: bool, sequence_number: u32,) ExpressionError!Id")
    program = parser.block()
    lookup = function(data, "pub fn representative(self: *const ExpressionClasses, id: Id) ExpressionError!*const Expression")
    lookup.expect("{ if (id")
    bound = lookup.pop()
    if bound not in (">=", ">"):
        raise Unsupported("unmodeled representative bound")
    lookup.expect("self.representatives.items.len) return error.InvalidExpressionId; return &self.representatives.items[")
    index = lookup.pop()
    if index != "id" and not re.fullmatch(r"[0-9]+", index):
        raise Unsupported("unmodeled representative index")
    lookup.expect("]; }")
    reader = function(data, "pub fn knownConstant(self: *const ExpressionClasses, id: Id) ?*const u256")
    reader.expect("{ const expression = self.representative(id) catch return null; if (expression.item.item_type")
    comparison = reader.pop()
    if comparison not in ("!=", "=="):
        raise Unsupported("unmodeled constant discriminator")
    reader.expect(".Push) return null; return &expression.item.data_value; }")
    copied = function(data, "pub fn knownConstantValue(self: *const ExpressionClasses, id: Id) ?u256")
    copied.expect("{ const value = self.knownConstant(id) orelse return null; return value.*; }")
    operation = function(data, "pub fn operationArguments(self: *const ExpressionClasses, id: Id, instruction: Instruction,) ?[]const Id")
    operation.expect("{ const expression = self.representative(id) catch return null; if (expression.item.item_type")
    kind_comparison = operation.pop()
    operation.expect(".Operation or expression.item.instruction_value.?")
    opcode_comparison = operation.pop()
    if kind_comparison not in ("!=", "==") or opcode_comparison not in ("!=", "=="):
        raise Unsupported("unmodeled operation discriminator")
    operation.expect("instruction) return null; return")
    if operation.take("expression"):
        operation.expect(".arguments;")
        returned_arguments = "stored"
    else:
        operation.expect("&.{};")
        returned_arguments = "empty"
    operation.expect("}")
    lookup_code = "{ bound := ." + ("ge" if bound == ">=" else "gt") + ", index := " + (
        ".requested" if index == "id" else ".literal " + index) + " }"
    return ("/-\n// SPDX-License-Identifier: GPL-3.0\n"
            "// Copyright (C) 2026 OKcontract Pte. Ltd.\n-/\n"
            "import Compiler.Extraction.StorageRead\n\nnamespace Compiler.Extraction.Storage\n\n"
            "-- Generated from the production insertOwned body.\n"
            "-- Source SHA-256: " + hashlib.sha256(data).hexdigest() + "\n"
            "def insertProgram : Program :=\n  " + program + "\n\n"
            "def representativeProgram : Lookup := " + lookup_code + "\n\n"
            "def constantProgram : ConstantRead := { lookup := representativeProgram, rejectOnPush := " +
            ("true" if comparison == "==" else "false") + " }\n\n"
            "def operationProgram : OperationRead := { lookup := representativeProgram, rejectOnOperation := " +
            ("true" if kind_comparison == "==" else "false") + ", rejectOnEqualOpcode := " +
            ("true" if opcode_comparison == "==" else "false") + ", arguments := ." + returned_arguments + " }\n\n"
            "end Compiler.Extraction.Storage\n").encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=SOURCE)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = extract(args.source.read_bytes())
    if args.check:
        if args.output.read_bytes() != result:
            parser.error("storage extraction is stale; review its source and manual proofs")
    else:
        args.output.write_bytes(result)


if __name__ == "__main__":
    main()
