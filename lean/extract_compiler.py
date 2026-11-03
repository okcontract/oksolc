#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Restricted, fail-closed extraction of production matching and graph construction.
This parser/translator is a reviewed trust boundary, not a verified Zig frontend.
The native gate separately typechecks the same module with pinned Zig 0.17.0.
"""
import argparse
from dataclasses import dataclass
import hashlib
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "src/libevmasm/algebraic_rules.zig"
OUTPUT = ROOT / "lean/Compiler/Extraction/Matcher.lean"
CONSTRUCTION = ROOT / "lean/Compiler/Extraction/Construction.lean"
TOKEN = re.compile(r'\s+|//[^\n]*|"(?:[^"\\\n]|\\["\\])*"|@[A-Za-z_][A-Za-z_0-9]*|'
                   r'[A-Za-z_][A-Za-z_0-9]*|0x[0-9a-fA-F]+|[0-9]+|==|!=|=>|[{}()\[\].,:;?!=~*+&|]')


class Unsupported(ValueError):
    pass


def tokens(text):
    result, pos = [], 0
    for match in TOKEN.finditer(text):
        if match.start() != pos:
            raise Unsupported("unrecognized source token at character " + str(pos))
        pos = match.end()
        token = match.group()
        if not token.isspace() and not token.startswith("//"):
            result.append(token)
    if pos != len(text):
        raise Unsupported("unrecognized source suffix at character " + str(pos))
    return result


@dataclass(frozen=True)
class Expr:
    tag: str
    args: tuple


class Parser:
    def __init__(self, source):
        self.items, self.pos = tokens(source), 0

    def peek(self):
        return self.items[self.pos] if self.pos < len(self.items) else "<eof>"

    def pop(self):
        value = self.peek()
        if value == "<eof>":
            raise Unsupported("unexpected end of source")
        self.pos += 1
        return value

    def take(self, value):
        if self.peek() == value:
            self.pos += 1
            return True
        return False

    def expect(self, text):
        for expected in tokens(text):
            actual = self.pop()
            if actual != expected:
                raise Unsupported(f"expected {expected!r}, found {actual!r} at token {self.pos}")

    def ident(self):
        name = self.pop()
        if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", name):
            raise Unsupported("expected identifier: " + name)
        return name

    def expression(self, priority=0):
        token = self.pop()
        if token == "try":
            left = Expr("try", (self.expression(4),))
        elif token == "&":
            self.expect(".{")
            values = []
            while not self.take("}"):
                values.append(self.expression())
                if self.take("}"):
                    break
                self.expect(",")
            left = Expr("array", (tuple(values),))
        elif token == "if":
            self.expect("(")
            condition = self.expression()
            self.expect(")")
            yes = self.expression()
            self.expect("else")
            left = Expr("if", (condition, yes, self.expression()))
        elif token == "switch":
            self.expect("(")
            subject = self.expression()
            self.expect(") {")
            arms = []
            while not self.take("}"):
                self.expect(".")
                names = [self.ident()]
                while self.take(","):
                    self.expect(".")
                    names.append(self.ident())
                self.expect("=>")
                arms.append((tuple(names), self.expression()))
                self.expect(",")
            left = Expr("switch", (subject, tuple(arms)))
        elif token == "(":
            left = self.expression()
            self.expect(")")
        elif token == ".":
            left = Expr("enum", (self.ident(),))
        elif re.fullmatch(r"[0-9]+|0x[0-9a-fA-F]+", token):
            left = Expr("number", (int(token, 16 if token.startswith("0x") else 10),))
        elif re.fullmatch(r"@?[A-Za-z_][A-Za-z_0-9]*", token):
            left = Expr("block", (token, self.block())) if self.take(":") else Expr("name", (token,))
        else:
            raise Unsupported("unsupported expression token: " + token)
        while True:
            if self.take("."):
                left = Expr("field", (left, self.ident()))
            elif self.take("("):
                arguments = []
                if not self.take(")"):
                    while True:
                        arguments.append(self.expression())
                        if self.take(")"):
                            break
                        self.expect(",")
                left = Expr("call", (left, tuple(arguments)))
            else:
                break
        precedences = {"or": 1, "and": 2, "==": 3, "!=": 3}
        while precedences.get(self.peek(), 0) > priority:
            operator = self.pop()
            left = Expr(operator, (left, self.expression(precedences[operator])))
        return left

    def block(self):
        self.expect("{")
        result = []
        while not self.take("}"):
            result.append(self.statement())
        return result

    def statement(self):
        token = self.pop()
        if token == "return":
            value = self.expression()
            self.expect(";")
            return ("return", value)
        if token == "const":
            name = self.ident()
            typ = self.ident() if self.take(":") else None
            self.expect("=")
            value = self.expression()
            self.expect(";")
            return ("let", name, typ, value)
        if token == "break":
            self.expect(":")
            label = self.ident()
            value = self.expression()
            self.expect(";")
            return ("break", label, value)
        if token == "if":
            self.expect("(")
            self.take("comptime")  # Pure, total condition; native typechecking checks staging.
            condition = self.expression()
            self.expect(")")
            yes = self.block() if self.peek() == "{" else [self.statement()]
            no = []
            if self.take("else"):
                no = self.block() if self.peek() == "{" else [self.statement()]
            return ("if", condition, yes, no)
        if token == "inline":
            self.expect("for (")
            values = self.expression()
            self.expect(") |")
            name = self.ident()
            self.expect("|")
            return ("for", values, name, self.block())
        if token == "switch":
            self.expect("(")
            value = self.expression()
            self.expect(") { inline else => |")
            name = self.ident()
            self.expect("|")
            body = self.block()
            self.expect(", }")
            return ("capture", name, value, body)
        if token == "@setEvalBranchQuota":
            # Compilation resource metadata only; no arbitrary ignored expression.
            self.expect("(256 * (rules.len + 1) * 4);")
            return ("quota",)
        raise Unsupported("unsupported statement: " + token)


ENUMS = {
    "Guard": "left_zero right_zero left_one right_one left_max right_max equal".split(),
    "Replacement": "left right zero one max not_right neg_left neg_right iszero_left iszero_right bool_left bool_right".split(),
    "Stage": ["constants", "equal"],
}
BUILD_OPS = {"NOT": 1, "SUB": 2, "ISZERO": 1}
FIELDS = {("Facts", "left"): ("left", "Option Word"),
          ("Facts", "right"): ("right", "Option Word"),
          ("Facts", "equal"): ("equal", "Bool"),
          ("Rule", "instruction"): ("op", "Binary"),
          ("Rule", "guard"): ("guard", "Guard"),
          ("Rule", "replacement"): ("replacement", "Replacement")}


def expression(node, env, expected=None):
    tag, args = node.tag, node.args
    if tag == "name":
        name = args[0]
        if name in env:
            result = env[name]
        elif name in ("true", "false"):
            result = (name, "Bool")
        elif name == "null" and expected and expected.startswith("Option "):
            result = ("none", expected)
        elif name == "max_word":
            result = ("(BitVec.allOnes 256)", "Word")
        else:
            raise Unsupported("unbound name: " + name)
    elif tag == "number":
        if expected not in ("Word", "Option Word") or not 0 <= args[0] < 2**256:
            raise Unsupported("unsupported integer context/range")
        result = (str(args[0]), "Word")
    elif tag == "enum":
        enum_type = expected.removeprefix("Option ") if expected else None
        members = BUILD_OPS if enum_type == "BuildOp" else ENUMS.get(enum_type, [])
        if args[0] not in members:
            raise Unsupported("unknown or untyped enum literal: " + args[0])
        result = ("." + args[0], enum_type)
    elif tag == "field":
        owner, typ = expression(args[0], env)
        if (typ, args[1]) not in FIELDS:
            raise Unsupported("unsupported field: " + typ + "." + args[1])
        field, typ = FIELDS[typ, args[1]]
        result = (owner + "." + field, typ)
    elif tag == "call":
        callee, arguments = args
        if callee == Expr("name", ("@backingInt",)) and len(arguments) == 1:
            value, typ = expression(arguments[0], env)
            if typ == "Opcode":
                result = (value, "Opcode")
            elif typ == "Binary":
                result = ("(productionOpcode " + value + ")", "Opcode")
            else:
                raise Unsupported("unsupported enum integer conversion")
        elif callee == Expr("name", ("matches",)) and len(arguments) == 2:
            guard, _ = expression(arguments[0], env, "Guard")
            facts, _ = expression(arguments[1], env, "Facts")
            result = (f"(zigMatches {guard} {facts})", "Bool")
        else:
            raise Unsupported("unsupported call")
    elif tag in ("==", "!=", "and", "or"):
        left, typ = expression(args[0], env, "Bool" if tag in ("and", "or") else None)
        right, _ = expression(args[1], env, typ)
        operator = {"==": "==", "!=": "!=", "and": "&&", "or": "||"}[tag]
        result = (f"({left} {operator} {right})", "Bool")
    elif tag == "if":
        condition, _ = expression(args[0], env, "Bool")
        yes, typ = expression(args[1], env, expected)
        no, _ = expression(args[2], env, typ)
        result = (f"(if {condition} then {yes} else {no})", typ)
    elif tag == "switch":
        subject, typ = expression(args[0], env)
        arms = args[1]
        if typ not in ENUMS or sorted(n for names, _ in arms for n in names) != sorted(ENUMS[typ]):
            raise Unsupported("switch must cover exactly the admitted enum")
        rendered = []
        for names, value in arms:
            code, value_type = expression(value, env, expected)
            if expected is None:
                expected = value_type
            rendered.extend(f"| .{name} => {code}" for name in names)
        result = ("(match " + subject + " with " + " ".join(rendered) + ")", expected)
    else:
        raise Unsupported("unsupported expression: " + tag)
    code, actual = result
    if expected == "Option " + actual:
        return "(some " + code + ")", expected
    if expected is not None and expected != actual:
        raise Unsupported(f"type mismatch: expected {expected}, got {actual}")
    return result


def bind(env, name, typ):
    if name in env or name in ("max_word", "true", "false", "null", "matches"):
        raise Unsupported("shadowed binding: " + name)
    return {**env, name: ("z_" + name, typ)}


def statements(body, env, continuation="none"):
    """First return exits the function, including returns inside inline loops."""
    if not body:
        return continuation
    stmt, rest = body[0], body[1:]
    tag = stmt[0]
    if tag == "return":
        if rest:
            raise Unsupported("unreachable statements after return")
        return expression(stmt[1], env, "Option Replacement")[0]
    if tag == "quota":
        return statements(rest, env, continuation)
    if tag == "let":
        _, name, typ, value = stmt
        if typ not in ENUMS:
            raise Unsupported("unsupported local type: " + str(typ))
        code, _ = expression(value, env, typ)
        child = bind(env, name, typ)
        return f"(let z_{name} : {typ} := {code}; {statements(rest, child, continuation)})"
    if tag == "if":
        condition = expression(stmt[1], env, "Bool")[0]
        after = statements(rest, env, continuation)
        yes = statements(stmt[2], env, after)
        no = statements(stmt[3], env, after)
        return f"(if {condition} then {yes} else {no})"
    if tag == "capture":
        _, name, value, inner = stmt
        code, typ = expression(value, env, "Opcode")
        child = bind(env, name, typ)
        after = statements(rest, env, continuation)
        return f"(let z_{name} := {code}; {statements(inner, child, after)})"
    if tag == "for":
        _, values, name, inner = stmt
        code, _ = expression(values, env, "List Rule")
        child = bind(env, name, "Rule")
        iteration = statements(inner, child)
        after = statements(rest, env, continuation)
        return f"(firstReturn {code} (fun z_{name} => {iteration}) {after})"
    raise Unsupported("unsupported statement node: " + tag)


def parse_module(data, *, raw=False):
    p = Parser(data.decode("utf-8"))
    p.expect('const Instruction = @import("instruction.zig").Instruction;')
    p.expect('const DebugData = @import("../liblangutil/debug_data.zig").DebugData;')
    for name, members in ENUMS.items():
        p.expect("pub const " + name + " = enum { " + ", ".join(members) + " };")
    p.expect("pub const Rule = struct { instruction: Instruction, guard: Guard, replacement: Replacement };")
    p.expect("pub const Facts = struct { left: ?u256 = null, right: ?u256 = null, equal: bool = false };")
    p.expect("const max_word = ~@as(u256, 0);")
    p.expect("pub const rules = [_]Rule{")
    # Values are provided by the separately compiled native exporter. Parse all
    # entries so new executable declarations cannot hide in an ignored prefix.
    while not p.take("}"):
        p.expect(".{ .instruction = .")
        instruction = p.ident()
        if instruction.lower() not in "add sub mul div mod and or xor shl shr lt gt eq".split():
            raise Unsupported("unmodeled rule opcode: " + instruction)
        p.expect(", .guard = .")
        if p.ident() not in ENUMS["Guard"]:
            raise Unsupported("unmodeled guard")
        p.expect(", .replacement = .")
        if p.ident() not in ENUMS["Replacement"]:
            raise Unsupported("unmodeled replacement")
        p.expect("},")
    p.expect(";")
    p.expect("pub fn matches(guard: Guard, facts: Facts) bool")
    matcher = p.block()
    if len(matcher) != 1 or matcher[0][0] != "return":
        raise Unsupported("matches must return one pure expression")
    match_code = expression(matcher[0][1], {"guard": ("guard", "Guard"),
                                           "facts": ("facts", "Facts")}, "Bool")[0]
    p.expect("pub fn select(instruction: Instruction, stage: Stage, facts: Facts) ?Replacement")
    selection = p.block()
    select_code = statements(selection, {"instruction": ("instruction", "Opcode"),
        "stage": ("stage", "Stage"), "facts": ("facts", "Facts"), "rules": ("rules", "List Rule")})
    p.expect("pub fn apply(replacement: Replacement, classes: anytype, left: u32, right: u32, debug_data: DebugData) !u32")
    construction = p.block()
    if len(construction) != 1 or construction[0][0] != "return":
        raise Unsupported("apply must return one construction expression")
    if p.peek() != "<eof>":
        raise Unsupported("unexpected top-level declaration")
    if raw:
        return matcher[0][1], selection, construction[0][1]
    return match_code, select_code, construction[0][1]


def extract(data):
    match_code, select_code, _ = parse_module(data)
    return ("/-\n// SPDX-License-Identifier: GPL-3.0\n"
        "// Copyright (C) 2026 OKcontract Pte. Ltd.\n-/\n"
        "import Compiler.Extraction.Control\nimport Compiler.Algebraic.Rules\n\n"
        "namespace Compiler.Algebraic\nopen Contract.Yul\n\n"
        "-- Generated by lean/extract_compiler.py from actual Zig function bodies.\n"
        "-- Source SHA-256: " + hashlib.sha256(data).hexdigest() + "\n"
        "-- apply is extracted separately in Construction.lean.\n"
        "def zigMatches (guard : Guard) (facts : Facts) : Bool :=\n  " + match_code + "\n\n"
        "def zigSelectFrom (rules : List Rule) (instruction : BitVec 8)\n"
        "    (stage : Stage) (facts : Facts) : Option Replacement :=\n  " + select_code + "\n\n"
        "def zigSelect := zigSelectFrom productionRules\n\nend Compiler.Algebraic\n").encode()


def construction_expression(root):
    serial = 0

    def effects(value):
        if isinstance(value, Expr):
            return (value.tag == "try") + effects(value.args)
        if isinstance(value, (tuple, list)):
            return sum(effects(item) for item in value)
        return 0

    def build(node, env, expected="NodeId", then=None):
        nonlocal serial
        def finish(code):
            return then(code) if then else "(pure " + code + ")"
        tag, args = node.tag, node.args
        if tag == "try":
            call = args[0]
            if expected != "NodeId" or call.tag != "call":
                raise Unsupported("try requires an admitted node-building callback")
            callee, arguments = call.args
            if callee.tag != "field" or callee.args[0] != Expr("name", ("classes",)):
                raise Unsupported("unsupported callback receiver")
            method = callee.args[1]
            if method == "makeConstant" and len(arguments) == 2:
                types = ["Word", "Debug"]
            elif method == "makeOperation" and len(arguments) == 3:
                op, operands, _ = arguments
                if (op.tag != "enum" or op.args[0] not in BUILD_OPS or operands.tag != "array"
                        or len(operands.args[0]) != BUILD_OPS[op.args[0]] or effects(operands) > 1):
                    raise Unsupported("unsupported operation or operand arity")
                types = ["BuildOp", "List NodeId", "Debug"]
            else:
                raise Unsupported("unsupported graph callback: " + method)

            def invoke(values):
                nonlocal serial
                action = "(classes." + method + " " + " ".join(values) + ")"
                if then is None:
                    return action
                name = "extracted_" + str(serial)
                serial += 1
                return f"({action} >>= fun {name} => {finish(name)})"
            return sequence(arguments, types, env, invoke)
        if tag == "array":
            if expected != "List NodeId":
                raise Unsupported("array used outside operand arguments")
            return sequence(args[0], ["NodeId"] * len(args[0]), env,
                            lambda values: finish("[" + ", ".join(values) + "]"))
        if tag == "if":
            condition = expression(args[0], env, "Bool")[0]
            yes = build(args[1], env, expected, then)
            no = build(args[2], env, expected, then)
            return f"(if {condition} then {yes} else {no})"
        if tag == "switch":
            subject, typ = expression(args[0], env)
            arms = args[1]
            if typ not in ENUMS or sorted(n for ns, _ in arms for n in ns) != sorted(ENUMS[typ]):
                raise Unsupported("construction switch must cover exactly its enum")
            rendered = []
            for names, value in arms:
                code = build(value, env, expected, then)
                rendered.extend(f"| .{name} => {code}" for name in names)
            return "(match " + subject + " with " + " ".join(rendered) + ")"
        if tag == "block":
            label, body = args
            def block(rest, scope):
                if not rest:
                    raise Unsupported("construction block lacks its result")
                stmt = rest[0]
                if stmt[0] == "break" and stmt[1] == label and len(rest) == 1:
                    return build(stmt[2], scope, expected, then)
                if stmt[0] == "let" and stmt[2] in (None, "u32"):
                    child = bind(scope, stmt[1], "NodeId")
                    def resume(value):
                        child[stmt[1]] = (value, "NodeId")
                        return block(rest[1:], child)
                    return build(stmt[3], scope, "NodeId", resume)
                raise Unsupported("unsupported construction block statement")
            return block(body, env)
        return finish(expression(node, env, expected)[0])

    def sequence(nodes, types, env, then):
        def visit(index, values):
            if index == len(nodes):
                return then(values)
            return build(nodes[index], env, types[index], lambda value: visit(index + 1, values + [value]))
        return visit(0, [])

    return build(root, {"replacement": ("replacement", "Replacement"),
        "left": ("left", "NodeId"), "right": ("right", "NodeId"),
        "debug_data": ("debug_data", "Debug"), "classes": ("classes", "Builder")})


def extract_construction(data):
    _, _, root = parse_module(data)
    code = construction_expression(root)
    return ("/-\n// SPDX-License-Identifier: GPL-3.0\n"
        "// Copyright (C) 2026 OKcontract Pte. Ltd.\n-/\n"
        "import Compiler.Extraction.Builder\n\nnamespace Compiler.Algebraic\nopen Contract.Yul\n\n"
        "-- Generated from the actual Zig apply body by lean/extract_compiler.py.\n"
        "-- Source SHA-256: " + hashlib.sha256(data).hexdigest() + "\n"
        "def zigApply {m : Type → Type} [Monad m] {Debug : Type}\n"
        "    (replacement : Replacement) (classes : Builder m Debug)\n"
        "    (left right : NodeId) (debug_data : Debug) : m NodeId :=\n  " + code + "\n\n"
        "end Compiler.Algebraic\n").encode()


def main():
    import compiler_ir
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=SOURCE)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    parser.add_argument("--construction-output", type=Path, default=CONSTRUCTION)
    parser.add_argument("--ir-output", type=Path, default=compiler_ir.OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    data = args.source.read_bytes()
    outputs = [(args.output, extract(data)), (args.construction_output, extract_construction(data)),
               (args.ir_output, compiler_ir.extract(data))]
    for path, generated in outputs:
        if args.check:
            if path.read_bytes() != generated:
                parser.error("extracted implementation is stale; review changed definitions and proofs: " + str(path))
        else:
            path.write_bytes(generated)


if __name__ == "__main__":
    main()
