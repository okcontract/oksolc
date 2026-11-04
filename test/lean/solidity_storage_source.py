#!/usr/bin/env python3
"""
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

Closed Solidity storage admission reusing the pure fragment's expression parser.
Private uint256/bool fields use declaration-order packing in the source model.
Boolean declaration initializers are not admitted yet; word initializers retain
checked arithmetic and forward references to other declared word fields.
Declaration initializers use checked word expressions and run in source order.
Optional parameterless constructors reuse the statement model and may be payable.
No inheritance, custom layout, shadowing, calls or implicit getters.
Braced if/else arms may join or return early. Conditions compose word comparisons
with short-circuit Boolean operators; loops and expression effects reject.
"""
from solidity_function_source import OPERATORS, Parser

CONDITION_OPERATORS = {**{op: (level + 20, name) for op, (level, name) in OPERATORS.items()},
    "<": (20, "lt"), "<=": (20, "le"), ">": (20, "gt"), ">=": (20, "ge"),
    "==": (15, "eq"), "!=": (15, "ne"), "&&": (10, "and"), "||": (5, "or")}


class StorageParser(Parser):
    def __init__(self, source):
        super().__init__(source)
        self.fields = []
        self.receiver = None
        self.return_type = "uint256"
        self.initializing = False
        self.constructing = False
        self.constructor = None
        self.condition_nodes = 0

    @property
    def storage(self):
        return [field["name"] for field in self.fields]

    def value_type(self, name):
        if name in self.parameters:
            return self.parameter_types[self.parameters.index(name)]
        return next((field["type"] for field in self.fields if field["name"] == name), None)

    def parameter_type(self):
        if self.take("bool"):
            return "bool"
        return super().parameter_type()

    def node(self, value):
        result = super().node(value)
        if len(self.nodes) + self.condition_nodes > 128:
            raise ValueError("source expression exceeds node limit")
        return result

    def condition_node(self, value):
        self.condition_nodes += 1
        if len(self.nodes) + self.condition_nodes > 128:
            raise ValueError("source expression exceeds node limit")
        return "bool", value

    def condition(self, precedence=0, depth=0):
        # Typed Pratt parsing distinguishes parenthesized words from conditions
        # without backtracking or accepting Solidity's nonexistent truthiness.
        if depth > 32:
            raise ValueError("source expression exceeds nesting limit")
        if self.take("("):
            kind, left = self.condition(depth=depth + 1)
            self.expect(")")
        elif self.take("!"):
            kind, child = self.condition(100, depth + 1)
            if kind != "bool":
                raise ValueError("logical negation requires a Boolean operand")
            kind, left = self.condition_node({"not": child})
        elif self.peek() in ("true", "false"):
            kind, left = self.condition_node({"literal": self.pop() == "true"})
        elif self.value_type(self.peek()) == "bool":
            kind, left = self.condition_node({"boolean": self.node({"input": self.pop()})})
        else:
            kind, left = "word", self.expression(100, depth + 1)
        while self.peek() in CONDITION_OPERATORS and CONDITION_OPERATORS[self.peek()][0] > precedence:
            token = self.pop()
            level, operation = CONDITION_OPERATORS[token]
            right_kind, right = self.condition(level, depth + 1)
            required = "bool" if token in ("&&", "||") else "word"
            if kind != required or right_kind != required:
                raise ValueError("condition operand type mismatch")
            if token in OPERATORS:
                left = self.node({"binary": {"op": operation, "left": left, "right": right}})
            elif required == "word":
                kind, left = self.condition_node({"compare": {"op": token, "left": left, "right": right}})
            else:
                kind, left = self.condition_node({operation: [left, right]})
        return kind, left

    def reference(self, name):
        # Expressions are word-typed. Boolean references enter only through the
        # condition parser, so storage/ABI bools cannot become uint256 operands.
        return self.value_type(name) == "uint256"

    def function(self, contract):
        self.condition_nodes = 0
        name = self.function_header(contract)
        if name in self.storage or any(parameter in self.storage for parameter in self.parameters):
            raise ValueError("storage declaration shadowing is not admitted")
        mutability = self.pop() if self.peek() in ("pure", "view", "payable") else "nonpayable"
        self.return_type = "none"
        if self.take("returns"):
            self.expect("(", "uint256", ")")
            self.return_type = "uint256"
        self.expect("{")
        unchecked = self.take("unchecked")
        if unchecked:
            self.expect("{")
        self.writes, self.branches, self.statements = 0, 0, 0
        body, returned = self.block()
        if self.return_type == "uint256" and not returned:
            raise ValueError("every function path must return explicitly")
        if unchecked:
            self.expect("}")
        if self.writes and mutability in ("pure", "view"):
            raise ValueError("pure/view functions cannot write storage")
        if mutability == "pure" and any(node.get("input") in self.storage for node in self.nodes):
            raise ValueError("pure functions cannot read storage")
        result = self.describe(contract, name, not unchecked, None)
        del result['root']  # The statement tree, not an ABI return expression, owns the body.
        return {**result, "body": body, "writes": self.writes, "branches": self.branches,
                "statements": self.statements, "conditionNodes": self.condition_nodes, "mutability": mutability,
                "parameterTypes": self.parameter_types, "returnType": self.return_type}

    def extra_declaration(self):
        if self.take("receive"):
            if self.receiver is not None:
                raise ValueError("duplicate receive declaration")
            self.nodes, self.parameters, self.parameter_types = [], [], []
            self.condition_nodes = 0
            self.return_type = "none"
            self.expect("(", ")", "external", "payable", "{")
            unchecked = self.take("unchecked")
            if unchecked:
                self.expect("{")
            self.writes, self.branches, self.statements = 0, 0, 0
            body, _ = self.block()
            if unchecked:
                self.expect("}")
            self.receiver = {"checked": not unchecked, "body": body, "nodes": self.nodes,
                "parameters": [], "parameterTypes": [], "returnType": "none", "mutability": "payable",
                "writes": self.writes, "branches": self.branches, "statements": self.statements,
                "conditionNodes": self.condition_nodes}
            return True
        if not self.take("constructor"):
            return False
        if self.constructor is not None:
            raise ValueError("duplicate constructor")
        self.nodes, self.parameters, self.parameter_types = [], [], []
        self.return_type = "none"
        self.condition_nodes = 0
        self.expect("(", ")")
        payable = self.take("payable")
        self.expect("{")
        unchecked = self.take("unchecked")
        if unchecked:
            self.expect("{")
        self.writes, self.branches, self.statements = 0, 0, 0
        self.constructing = True
        body, _ = self.block()
        self.constructing = False
        if unchecked:
            self.expect("}")
        self.constructor = {"explicit": True, "payable": payable, "checked": not unchecked,
            "body": body, "nodes": self.nodes, "writes": self.writes,
            "branches": self.branches, "statements": self.statements, "conditionNodes": self.condition_nodes}
        return True

    def block(self):
        body, returned = [], False
        while not self.take("}"):
            if returned:
                raise ValueError("unreachable statement after guaranteed return")
            self.statements += 1
            if self.statements > 32:
                raise ValueError("function exceeds statement limit")
            if self.take("return"):
                if self.constructing or self.return_type == "none":
                    body.append({"stop": True})
                else:
                    body.append({"return": self.expression()})
                self.expect(";")
                returned = True
            elif self.take("revert"):
                self.expect("(", ")", ";")
                body.append({"revert": True})
                returned = True
            elif self.take("if"):
                self.branches += 1
                if self.branches > 4:
                    raise ValueError("function exceeds branch limit")
                self.expect("(")
                kind, condition = self.condition()
                if kind != "bool":
                    raise ValueError("condition must have Boolean type")
                self.expect(")", "{")
                yes, yes_returned = self.block()
                no, no_returned = [], False
                if self.take("else"):
                    self.expect("{")
                    no, no_returned = self.block()
                body.append({"if": {"condition": condition, "yes": yes, "no": no}})
                returned = yes_returned and no_returned
            else:
                target = self.pop()
                if target not in self.storage:
                    raise ValueError("assignment target must be a declared storage word")
                self.writes += 1
                if self.writes > 8:
                    raise ValueError("function exceeds the storage write limit")
                self.expect("=")
                if self.value_type(target) == "bool":
                    kind, condition = self.condition()
                    if kind != "bool":
                        raise ValueError("Boolean assignment requires a Boolean value")
                    body.append({"writeBool": {"field": self.storage.index(target), "condition": condition}})
                else:
                    body.append({"write": {"slot": self.storage.index(target), "root": self.expression()}})
                self.expect(";")
        return body, returned

    def contract(self, limit):
        contract = self.contract_header()
        start = self.pos
        # Resolve types for forward references before parsing initializers.
        # The second pass still parses every initializer token; this inventory
        # scan grants no expression admission and ignores no declaration body.
        while self.peek() in ("uint256", "bool"):
            field_type = self.pop()
            self.expect("private")
            name = self.ident()
            if name in self.storage or name == contract or len(self.fields) == 8:
                raise ValueError("duplicate/conflicting storage name or more than eight fields")
            self.fields.append({"name": name, "type": field_type})
            if self.take("="):
                while self.peek() != ";":
                    self.pop()
            self.expect(";")
        if not self.fields:
            raise ValueError("storage contract must declare at least one field")
        self.pos = start
        self.initializing = True
        initializers = []
        for index, field in enumerate(self.fields):
            self.expect(field["type"], "private", field["name"])
            if self.take("="):
                if field["type"] == "bool":
                    raise ValueError("Boolean declaration initializers are not admitted")
                initializers.append({"slot": index, "root": self.expression()})
            self.expect(";")
        self.initializing = False
        initialization_nodes = self.nodes
        functions = self.functions(contract, limit, allow_empty=True)
        if not functions["functions"] and self.receiver is None:
            raise ValueError("storage contract must declare a function or receive")
        constructor = self.constructor or {"explicit": False, "payable": False, "checked": True,
            "body": [], "nodes": [], "writes": 0, "branches": 0, "statements": 0, "conditionNodes": 0}
        return {**functions, "storage": self.storage, "fields": self.fields, "constructor": constructor,
                "receive": self.receiver, "initialization": {"nodes": initialization_nodes, "initializers": initializers}}


def parse(source):
    return StorageParser(source).contract(8)
