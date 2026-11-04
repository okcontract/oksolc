#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Independent, closed admission of an explicitly typed Solidity word function.
This small source parser is a trust boundary, not a verified Solidity frontend.
Integer expression operands require uint256(literal) or type(uint256).max.
A standalone bounded integer literal may also be converted by a uint256 return
context; literal arithmetic remains excluded because it has unbounded rational
semantics. Public functions admit only their message-call entry;
the closed grammar continues to reject internal calls and inheritance.
"""
import re

TOKEN = re.compile(r'[ \t\r\n]+|//[^\r\n]*|/\*[\s\S]*?\*/|"[^"\\\x00-\x1f\x7f]*"|0x[0-9a-fA-F]+|[0-9]+|'
                   r'[A-Za-z_][A-Za-z_0-9]*|<<|>>|==|!=|<=|>=|&&|\|\||[{}(),;.^|&~!+*=<>\-]')
OPERATORS = {"|": (10, "or"), "^": (20, "xor"), "&": (30, "and"),
             "<<": (40, "shl"), ">>": (40, "shr"), "+": (50, "add"),
             "-": (50, "sub"), "*": (60, "mul")}
# Conservative identifier admission, independent of compiler token exports.
# Includes reserved words and type families from the Solidity grammar.
KEYWORDS = set("""abstract address after alias anonymous apply as assembly auto bool break byte
    calldata case catch constant constructor continue contract copyof default define delete do else emit
    enum event external fallback false final for from function hex if immutable implements import in
    indexed inline interface internal is let library macro mapping match memory modifier mutable new
    null of override partial payable pragma private promise public pure receive reference relocatable
    return returns sealed sizeof solidity static storage struct super supports switch this throw true
    try type typedef typeof unchecked unicode using var view virtual while wei gwei ether seconds
    minutes hours days weeks years string leave error transient layout at""".split())


def tokenize(source):
    if not isinstance(source, str) or not source.isascii() or len(source) > 65536:
        raise ValueError("source exceeds the admitted size")
    result, pos = [], 0
    for match in TOKEN.finditer(source):
        if match.start() != pos:
            raise ValueError("unsupported Solidity token at character " + str(pos))
        pos = match.end()
        token = match.group()
        if not token.isspace() and not token.startswith(("//", "/*")):
            result.append(token)
    if pos != len(source):
        raise ValueError("unsupported or unterminated Solidity source suffix")
    return result


class Parser:
    def __init__(self, source):
        self.tokens, self.pos, self.nodes, self.parameters = tokenize(source), 0, [], []

    def peek(self):
        return self.tokens[self.pos] if self.pos < len(self.tokens) else "<eof>"

    def pop(self):
        value = self.peek()
        if value == "<eof>":
            raise ValueError("unexpected end of Solidity source")
        self.pos += 1
        return value

    def take(self, value):
        if self.peek() == value:
            self.pos += 1
            return True
        return False

    def expect(self, *values):
        for value in values:
            if self.pop() != value:
                raise ValueError("unsupported Solidity syntax; expected " + value)

    def ident(self):
        value = self.pop()
        if (value in KEYWORDS or re.fullmatch(r"(?:u?int|bytes)[0-9]*|u?fixed(?:[0-9]+x[0-9]+)?", value) or
                not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]{0,63}", value)):
            raise ValueError("invalid or unsupported source identifier")
        return value

    def node(self, value):
        if len(self.nodes) >= 128:
            raise ValueError("source expression exceeds node limit")
        self.nodes.append(value)
        return len(self.nodes) - 1

    def reference(self, name):
        return name in self.parameters

    def integer_literal(self, bits, type_name):
        literal = self.pop()
        if not re.fullmatch(r"0x[0-9a-fA-F]+|[0-9]+", literal) or len(literal) > 80:
            raise ValueError(type_name + " conversion must contain one bounded integer literal")
        if ((literal.startswith("0x") and 39 <= len(literal) - 2 <= 41) or
                (not literal.startswith("0x") and len(literal) > 1 and literal.startswith("0"))):
            raise ValueError("address-like hex and leading-zero decimal literals are not admitted")
        number = int(literal, 16 if literal.startswith("0x") else 10)
        if number >= 2**bits:
            raise ValueError("literal outside " + type_name)
        return number

    def expression(self, precedence=0, depth=0):
        if depth > 32:
            raise ValueError("source expression exceeds nesting limit")
        token = self.pop()
        if token == "(":
            left = self.expression(depth=depth + 1)
            self.expect(")")
        elif token == "~":
            left = self.node({"unary": {"op": "bitnot", "arg": self.expression(70, depth + 1)}})
        elif token == "uint256":
            self.expect("(")
            number = self.integer_literal(256, "uint256")
            self.expect(")")
            left = self.node({"literal": str(number)})
        elif token == "type":
            self.expect("(", "uint256", ")", ".", "max")
            left = self.node({"literal": str(2**256 - 1)})
        elif self.reference(token):
            left = self.node({"input": token})
        else:
            raise ValueError("operand must be a declared uint256 value, uint256(literal) or type(uint256).max")
        while self.peek() in OPERATORS and OPERATORS[self.peek()][0] > precedence:
            level, operation = OPERATORS[self.pop()]
            right = self.expression(level, depth + 1)
            left = self.node({"binary": {"op": operation, "left": left, "right": right}})
        return left

    def function_header(self, contract):
        self.nodes, self.parameters = [], []
        self.parameter_types = []
        self.expect("function")
        name = self.ident()
        if name == contract:
            raise ValueError("function name cannot equal its contract name")
        self.expect("(")
        if not self.take(")"):
            while True:
                self.parameter_types.append(self.parameter_type())
                parameter = self.parameter_name()
                if (parameter is not None and parameter in self.parameters) or len(self.parameters) == 8:
                    raise ValueError("duplicate parameter or more than eight parameters")
                self.parameters.append(parameter)
                if self.take(")"):
                    break
                self.expect(",")
        self.visibility = self.pop()
        if self.visibility not in ("external", "public"):
            raise ValueError("only external or public function entries are admitted")
        return name

    def parameter_name(self):
        return self.ident()

    def function(self, contract):
        name = self.function_header(contract)
        self.function_mutability()
        return self.function_body(contract, name)

    def parameter_type(self):
        self.expect("uint256")
        return "uint256"

    def function_body(self, contract, name):
        self.expect("returns", "(")
        result_type = self.result_type()
        self.expect(")", "{")
        unchecked = self.take("unchecked")
        if unchecked:
            self.expect("{")
        self.expect("return")
        root = self.return_expression(result_type)
        self.expect(";", "}")
        if unchecked:
            self.expect("}")
        return self.describe(contract, name, not unchecked, root)

    def function_mutability(self):
        self.expect("pure")

    def result_type(self):
        self.expect("uint256")
        return "uint256"

    def return_expression(self, result_type):
        if result_type == "uint256" and re.fullmatch(r"0x[0-9a-fA-F]+|[0-9]+", self.peek()):
            number = self.integer_literal(256, "uint256")
            if self.peek() != ";":
                raise ValueError("bare integer return must contain one literal without operators")
            return self.node({"literal": str(number)})
        return self.expression()

    def describe(self, contract, name, checked, root):
        return {"contract": contract, "name": name, "parameters": self.parameters, "checked": checked,
                "visibility": self.visibility,
                "nodes": self.nodes, "root": root,
                "signature": name + "(" + ",".join(self.parameter_types) + ")"}

    def contract_header(self):
        self.expect("pragma", "solidity")
        # A wildcard only admits the already pinned source/compiler semantics;
        # it does not select another language version or ignore other pragmas.
        if not self.take("*"):
            self.expect("^", "0", ".", "8", ".", "0")
        self.expect(";")
        return self.contract_declaration()

    def contract_declaration(self):
        self.expect("contract")
        contract = self.ident()
        self.expect("{")
        return contract

    def functions(self, contract, limit, *, allow_empty=False, final=True):
        functions, signatures = [], set()
        while not self.take("}"):
            if self.extra_declaration():
                continue
            if len(functions) == limit:
                raise ValueError("contract exceeds the admitted function limit")
            function = self.function(contract)
            if function["signature"] in signatures:
                raise ValueError("duplicate function signature")
            signatures.add(function["signature"])
            functions.append(function)
        if (not functions and not allow_empty) or (final and self.peek() != "<eof>"):
            raise ValueError("empty contract or extra declarations")
        return {"contract": contract, "functions": functions}

    def extra_declaration(self):
        return False

    def contract(self, limit):
        return self.functions(self.contract_header(), limit)

    def parse(self):
        return self.contract(1)["functions"][0]


def parse(source):
    return Parser(source).parse()


def parse_contract(source):
    return Parser(source).contract(8)
