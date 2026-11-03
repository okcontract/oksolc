#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Serialize parsed Zig into typed IR data, independently of the Lean-code backend.
The lexer, parser, admission/type checks and specialization are trusted. The
IR interpreter and correspondence to the readable generated code are checked.
"""
import hashlib
from pathlib import Path

from extract_compiler import Expr, Unsupported, expression, parse_module, construction_expression

OUTPUT = Path(__file__).resolve().parent / "Compiler/Extraction/Program.lean"
TYPES = {"Bool": "boolean", "Word": "word", "Opcode": "opcode", "NodeId": "node",
         "Guard": "guard", "Stage": "stage", "Replacement": "replacement",
         "Rule": "rule", "Facts": "facts"}


def ty(name):
    if name.startswith("Option "):
        return "(.optional " + ty(name[7:]) + ")"
    if name.startswith("List "):
        return "(.array " + ty(name[5:]) + ")"
    return "." + TYPES[name]


def infer(node, ctx, expected=None):
    return expression(node, {name: (name, typ) for name, typ in ctx}, expected)[1]


def variable(index):
    return "(.var " + "(.there " * index + ".here" + ")" * index + ")"


def pure(node, ctx, expected=None):
    tag, args = node.tag, node.args
    actual = infer(node, ctx, expected)
    if tag == "name":
        name = args[0]
        if name in ("true", "false"):
            return "(.boolean " + name + ")"
        if name == "null":
            return ".none"
        if name == "max_word":
            code, actual = "(.word (BitVec.allOnes 256))", "Word"
        else:
            index = next(i for i, (key, _) in enumerate(ctx) if key == name)
            code, actual = variable(index), ctx[index][1]
    elif tag == "number":
        code, actual = "(.word " + str(args[0]) + ")", "Word"
    elif tag == "enum":
        actual = actual.removeprefix("Option ")
        code = "(." + TYPES[actual] + " ." + args[0] + ")"
    elif tag == "field":
        actual = infer(node, ctx)
        owner = pure(args[0], ctx)
        kind = infer(args[0], ctx)
        field = {("Facts", "left"): "left", ("Facts", "right"): "right",
                 ("Facts", "equal"): "equal", ("Rule", "guard"): "ruleGuard",
                 ("Rule", "replacement"): "ruleReplacement"}.get((kind, args[1]))
        if field is None:
            raise Unsupported("IR field needs its explicit conversion: " + args[1])
        code = f"(.{field} {owner})"
    elif tag == "call":
        actual = infer(node, ctx)
        callee, arguments = args
        if callee == Expr("name", ("@backingInt",)):
            value = arguments[0]
            if value.tag == "field" and value.args[1] == "instruction":
                code = "(.ruleOpcode " + pure(value.args[0], ctx, "Rule") + ")"
            else:
                code = pure(value, ctx, "Opcode")
        elif callee == Expr("name", ("matches",)):
            code = "(.matches " + pure(arguments[0], ctx, "Guard") + " " + pure(arguments[1], ctx, "Facts") + ")"
        else:
            raise Unsupported("IR unsupported pure call")
    elif tag in ("==", "!=", "and", "or"):
        kind = "Bool" if tag in ("and", "or") else infer(args[0], ctx)
        a, b = pure(args[0], ctx, kind), pure(args[1], ctx, kind)
        code = f"(.{tag} {a} {b})" if tag in ("and", "or") else f"(.eq {ty(kind)} {a} {b})"
        if tag == "!=":
            code = "(.not " + code + ")"
    elif tag == "if":
        code = "(.ite " + pure(args[0], ctx, "Bool") + " " + pure(args[1], ctx, actual) + " " + pure(args[2], ctx, actual) + ")"
    elif tag == "switch":
        kind = infer(args[0], ctx)
        arms = " ".join("| ." + name + " => " + pure(value, ctx, actual)
                        for names, value in args[1] for name in names)
        code = "(." + TYPES[kind] + "Switch " + pure(args[0], ctx) + " (fun " + arms + "))"
    else:
        raise Unsupported("IR unsupported pure expression: " + tag)
    return "(.some " + code + ")" if expected == "Option " + actual else code


def block(body, ctx):
    if not body:
        return ".done"
    stmt, rest = body[0], body[1:]
    tag = stmt[0]
    if tag == "return":
        return "(.ret " + pure(stmt[1], ctx, "Option Replacement") + ")"
    if tag == "quota":
        return block(rest, ctx)
    if tag == "let":
        _, name, typ, value = stmt
        return "(.letE " + pure(value, ctx, typ) + " " + block(rest, [(name, typ)] + ctx) + ")"
    if tag == "capture":
        _, name, value, inner = stmt
        # Extend the environment while evaluating the continuation. Shared
        # admission has already checked that it cannot reference this capture.
        return "(.letE " + pure(value, ctx, "Opcode") + " " + block(inner + rest, [(name, "Opcode")] + ctx) + ")"
    if tag == "if":
        return "(.branch " + pure(stmt[1], ctx, "Bool") + " " + block(stmt[2], ctx) + " " + block(stmt[3], ctx) + " " + block(rest, ctx) + ")"
    if tag == "for":
        return "(.loop " + pure(stmt[1], ctx, "List Rule") + " " + block(stmt[3], [(stmt[2], "Rule")] + ctx) + " " + block(rest, ctx) + ")"
    raise Unsupported("IR unsupported statement: " + tag)


def build(root):
    # Apply the shared closed admission checks; discard their generated code.
    construction_expression(root)
    serial = 0

    def visit(node, ctx, continuation=None):
        nonlocal serial
        tag, args = node.tag, node.args
        if tag == "try":
            _, arguments = args[0].args
            method = args[0].args[0].args[1]
            if arguments[-1] != Expr("name", ("debug_data",)):
                raise Unsupported("IR requires the unchanged debug borrow")

            def finish(action, scope):
                nonlocal serial
                if continuation is None:
                    return action
                name = "ir_temporary_" + str(serial)
                serial += 1
                if any(key == name for key, _ in scope):
                    raise Unsupported("IR temporary collision")
                return "(.bind " + action + " " + continuation(Expr("name", (name,)), [(name, "NodeId")] + scope) + ")"

            if method == "makeConstant":
                return finish("(.constant " + pure(arguments[0], ctx, "Word") + ")", ctx)
            op, operands, _ = arguments

            def elements(index, values, scope):
                if index == len(operands.args[0]):
                    ids = ".nil"
                    for value in reversed(values):
                        ids = "(.cons " + pure(value, scope, "NodeId") + " " + ids + ")"
                    return finish("(.operation ." + op.args[0] + " " + ids + ")", scope)
                return visit(operands.args[0][index], scope,
                             lambda value, inner: elements(index + 1, values + [value], inner))
            return elements(0, [], ctx)
        if tag == "if":
            return "(.branch " + pure(args[0], ctx, "Bool") + " " + visit(args[1], ctx, continuation) + " " + visit(args[2], ctx, continuation) + ")"
        if tag == "switch":
            arms = " ".join("| ." + name + " => " + visit(value, ctx, continuation)
                            for names, value in args[1] for name in names)
            return "(.switch " + pure(args[0], ctx, "Replacement") + " (fun " + arms + "))"
        if tag == "block":
            label, body = args

            def statements(rest, scope):
                stmt = rest[0]
                if stmt[0] == "break" and stmt[1] == label:
                    return visit(stmt[2], scope, continuation)
                if stmt[0] == "let":
                    def resume(value, inner):
                        # Substitute a lexical alias, retaining the binding's
                        # scope index (the value is always a named node here).
                        if value.tag != "name":
                            raise Unsupported("IR local requires a named node")
                        renamed = [(stmt[1] if key == value.args[0] else key, typ)
                                   for key, typ in inner]
                        return statements(rest[1:], renamed)
                    return visit(stmt[3], scope, resume)
                raise Unsupported("IR unsupported construction statement")
            return statements(body, ctx)
        return continuation(node, ctx) if continuation else "(.ret " + pure(node, ctx, "NodeId") + ")"

    return visit(root, [("replacement", "Replacement"), ("left", "NodeId"), ("right", "NodeId")])


def extract(data):
    matcher, selection, construction = parse_module(data, raw=True)
    header = ("/-\n// SPDX-License-Identifier: GPL-3.0\n"
              "// Copyright (C) 2026 OKcontract Pte. Ltd.\n-/\n"
              "import Compiler.Extraction.IR\n\nnamespace Compiler.Extraction.IR\n"
              "open Compiler.Algebraic Contract.Yul\n\n"
              "-- Generated typed program data; manual proofs live in Correspondence.lean.\n"
              "-- Source SHA-256: " + hashlib.sha256(data).hexdigest() + "\n")
    return (header + "def matcher : Expr [.guard, .facts] .boolean :=\n  " +
            pure(matcher, [("guard", "Guard"), ("facts", "Facts")], "Bool") + "\n\n" +
            "def selection : Block [.opcode, .stage, .facts, .array .rule] :=\n  " +
            block(selection, [("instruction", "Opcode"), ("stage", "Stage"),
                              ("facts", "Facts"), ("rules", "List Rule")]) + "\n\n" +
            "def construction : Build [.replacement, .node, .node] :=\n  " + build(construction) +
            "\n\nend Compiler.Extraction.IR\n").encode()
