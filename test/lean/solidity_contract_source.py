#!/usr/bin/env python3
"""
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

Closed admission of a complete selected expression contract. Every declaration in the
source unit is parsed; selection never skips unsupported source. The grammar
has no imports, inheritance or calls between declarations. Address results are
restricted to bounded literal conversions or 40-digit numeric address spellings.
Boolean results admit only true/false literals, reusing the existing word ABI.
Bytes32 results admit one explicit conversion of a printable ASCII string
literal without escapes, right-padded to exactly 32 bytes by a checked encoding.
Empty bodies with no return values also admit unused bytes4 parameters and view.
The closed mstore(0, literal)/return(0, 32) assembly body returns the raw word;
its declared scalar result type never authorizes boolean or address cleanup.
"""
import re
from solidity_function_source import Parser


class ContractParser(Parser):
    def parameter_name(self):
        # An unnamed parameter still occupies its ABI slot. It is admitted only
        # for empty or closed raw-return bodies, which cannot reference it.
        return None if self.peek() in (",", ")") else self.ident()

    def parameter_type(self):
        kind = self.pop()
        if kind not in ("uint256", "bytes4"):
            raise ValueError("only uint256 and unused bytes4 parameters are admitted")
        return kind

    def function_mutability(self):
        self.mutability = self.pop()
        if self.mutability not in ("pure", "payable", "view"):
            raise ValueError("only pure/payable expressions or empty view functions are admitted")
        self.payable = self.mutability == "payable"

    def function_body(self, contract, name):
        if self.peek() == "{":
            self.expect("{", "}")
            self.return_kind = "none"
            return {**self.describe(contract, name, False, None),
                    "parameterTypes": self.parameter_types, "mutability": self.mutability}
        head = self.tokens[self.pos:self.pos + 6]
        if len(head) == 6 and head[:2] == ["returns", "("] and head[3:] == [")", "{", "assembly"]:
            self.expect("returns", "(")
            self.result_type()
            if self.return_kind == "bytes32":
                raise ValueError("bytes32 results require a string literal conversion")
            self.expect(")", "{", "assembly", "{", "mstore", "(", "0", ",")
            value = self.integer_literal(256, "raw return word")
            self.expect(")", "return", "(", "0", ",", "32", ")", "}", "}")
            return {**self.describe(contract, name, False, None), "bodyScope": "rawWordReturn",
                    "rawReturnWord": str(value), "parameterTypes": self.parameter_types,
                    "mutability": self.mutability}
        if None in self.parameters:
            raise ValueError("unnamed parameters require an empty or raw-return body")
        if self.mutability == "view" or any(kind != "uint256" for kind in self.parameter_types):
            raise ValueError("view and bytes4 parameters require an empty body with no returns")
        return super().function_body(contract, name)

    def result_type(self):
        self.return_kind = self.pop()
        if self.return_kind not in ("uint256", "address", "bool", "bytes32"):
            raise ValueError("only uint256 expressions and address/bool/bytes32 literal returns are admitted")
        return self.return_kind

    def return_expression(self, result_type):
        if result_type == "uint256":
            return super().return_expression(result_type)
        if result_type == "bytes32":
            self.expect("bytes32", "(")
            token = self.pop()
            if not re.fullmatch(r'"[^"\\\x00-\x1f\x7f]{0,32}"', token):
                raise ValueError("bytes32 requires at most 32 printable ASCII bytes without escapes")
            self.expect(")")
            self.literal_bytes = list(token[1:-1].encode("ascii"))
            return self.node({"literal": str(int.from_bytes(bytes(self.literal_bytes).ljust(32, b"\0"), "big"))})
        if result_type == "bool":
            value = self.pop()
            if value not in ("true", "false"):
                raise ValueError("boolean result must be one true/false literal")
            return self.node({"literal": "1" if value == "true" else "0"})
        # Digits have no EIP-55 case choices. Other bare hexadecimal spellings
        # stay rejected until their checksum is independently admitted.
        if re.fullmatch(r"0x[0-9]{40}", self.peek()):
            return self.node({"literal": str(int(self.pop(), 16))})
        self.expect("address", "(")
        value = self.integer_literal(160, "address")
        self.expect(")")
        return self.node({"literal": str(value)})

    def describe(self, contract, name, checked, root):
        return {**super().describe(contract, name, checked, root), "returnType": self.return_kind,
                "payable": self.payable,
                **({"literalBytes": self.literal_bytes} if self.return_kind == "bytes32" else {})}

    def unit(self, selected=None):
        if selected is not None and not isinstance(selected, str):
            raise ValueError("selected contract must be a name")
        contract = self.contract_header()
        declarations = {}
        while True:
            if contract in declarations or len(declarations) == 8:
                raise ValueError("duplicate contract name or more than eight contracts")
            declarations[contract] = self.functions(contract, 8, allow_empty=True, final=False)
            if self.peek() == "<eof>":
                break
            contract = self.contract_declaration()
        if selected is None:
            if len(declarations) != 1:
                raise ValueError("multiple contracts require an explicit selected target")
            selected = next(iter(declarations))
        if selected not in declarations:
            raise ValueError("selected contract is absent")
        return {**declarations[selected], "sourceUnitContracts": list(declarations)}


def parse(source, selected=None):
    return ContractParser(source).unit(selected)
