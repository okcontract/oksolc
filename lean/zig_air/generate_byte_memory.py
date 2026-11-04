#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Decode initialized u32 byte views with explicit SSA/storage provenance.
// Copyright (C) 2026 OKcontract Pte. Ltd.

Alignment wrappers survive captured type checking. Their runtime erasure is
restricted to checked word casts and byte views derived from them. A view can
be saved only in a fresh, nonescaping, exactly typed stack slice slot. Every
write to such a slot is checked, so its successful loads retain the origin;
uninitialized loads still fault in the memory model. Joins/escapes/arithmetic
that would lose this evidence reject. This is not a generic byte heap decoder.
"""
import generate_memory as memory
from generate import fields

BYTE = ("int", False, 8)
WORD = ("int", False, 32)
USIZE = ("int", False, 64)


def has_alignment(ty):
    if ty[0] == "aligned":
        return True
    return ty[0] in ("ptr", "slice", "array") and has_alignment(ty[-1])


def unqualified(ty):
    return ty[2] if ty[0] == "aligned" else ty


def alignment(ty):
    return ty[1] if ty[0] == "aligned" else memory.layout(ty[-1])[1]


def erase(ty):
    if ty[0] == "aligned":
        return erase(ty[2])
    if ty[0] in ("ptr", "slice", "array"):
        return (*ty[:-1], erase(ty[-1]))
    return ty


class ByteDecoder(memory.Decoder):
    type_of = staticmethod(lambda record: memory.type_of(record, byte_alignment=True))
    lean_type = staticmethod(lambda ty: memory.lean_type(erase(ty)))

    def __init__(self, record):
        super().__init__(record)
        if any(has_alignment(ty) for ty in [*self.parameters, self.result]):
            raise ValueError("aligned signature needs an external memory contract")
        # Incoming pointers cannot alias metadata in a future stack slot.
        # Until a general live-argument/separation contract is available, admit
        # only pointers whose stores have the disjoint u32 leaf type.
        if any(ty[0] not in ("int", "bool", "void") and not (ty[0] == "ptr" and ty[3] == WORD)
               for ty in self.parameters):
            raise ValueError("byte profile parameters require scalar or u32-pointer types")
        self.byte_values, self.byte_slots = {}, {}
        self.byte_alignments = {}

    def byte_inventory(self):
        return {"values": [{"instruction": i, "origin": origin, "alignment": self.byte_alignments[i]}
                            for i, origin in sorted(self.byte_values.items())],
                "stackSlots": [{"instruction": i, "allocation": root} for i, root in sorted(self.byte_slots.items())]}

    @staticmethod
    def ref_id(value):
        return value.get("index") if isinstance(value, dict) and value.get("kind") == "instruction" else None

    def mark(self, index, origin, ty):
        self.byte_values[index] = origin
        self.byte_alignments[index] = alignment(ty)

    def extra_primitive(self, inst, ty, env):
        tag, index, base = inst["tag"], inst["index"], "index tag payloadVisited type "
        raw = unqualified(ty)
        if tag == "alloc" and has_alignment(ty):
            fields(inst, base + "allocationKind")
            if (ty[0] != "ptr" or ty[1:3] != (True, False) or ty[3][0] != "aligned" or
                    unqualified(ty[3])[0] != "slice" or inst["allocationKind"] != "stack"):
                raise ValueError("byte view storage must be a fresh stack slice slot")
            self.byte_slots[index] = index
            return f"(.alloc {self.lean_type(ty[3])})"
        if tag in ("ptr_cast", "load", "slice_len", "slice_ptr"):
            fields(inst, base + "operand")
            source, operand = self.ref(inst["operand"], env)
            parent = self.ref_id(inst["operand"])
            src = unqualified(source)
            if tag == "ptr_cast" and raw[0] == "ptr" and raw[-1] == BYTE and src[0] == "ptr" and src[-1] == WORD:
                if src[2] or (raw[1] and not src[1]) or alignment(ty) not in (1, 2, 4):
                    raise ValueError("unsupported word-to-byte cast contract")
                self.mark(index, index, ty)
                return f"(.wordByteCast {str(raw[1]).lower()} {str(raw[2]).lower()} {alignment(ty)} {operand})"
            if tag == "ptr_cast" and parent in self.byte_slots:
                if source[0] != "ptr" or ty != ("ptr", False, False, source[3]):
                    raise ValueError("byte slice slot cast changes storage or permissions")
                self.byte_slots[index] = self.byte_slots[parent]
                return f"(.pointerCast {self.lean_type(ty)} {operand})"
            if tag == "load" and parent in self.byte_slots:
                if source[0] != "ptr" or source[3] != ty:
                    raise ValueError("byte slice slot load changes its stored type")
                # A slot may be assigned by several checked casts. The slot is
                # its stable origin; every store below requires a proved view.
                self.mark(index, self.byte_slots[parent], ty)
                return f"(.load {operand})"
            if tag == "load" and parent in self.byte_values:
                if src[0] != "ptr" or ty != BYTE:
                    raise ValueError("byte view load changes its element type")
                return f"(.wordByteLoad .little {operand})"
            if tag in ("slice_len", "slice_ptr") and parent in self.byte_values:
                expected = USIZE if tag == "slice_len" else ("ptr", src[1], True, BYTE)
                if src[0] != "slice" or raw != expected or (tag == "slice_ptr" and alignment(ty) != alignment(source)):
                    raise ValueError("byte slice projection loses alignment or type")
                if tag == "slice_ptr":
                    self.mark(index, self.byte_values[parent], ty)
                return f"(.{'sliceLen' if tag == 'slice_len' else 'slicePtr'} {operand})"
            if parent in self.byte_values or parent in self.byte_slots or has_alignment(source) or has_alignment(ty):
                raise ValueError("unsupported byte view propagation")
        if tag in ("slice", "slice_elem_ptr", "store", "store_safe"):
            fields(inst, base + "lhs rhs")
            lt, left = self.ref(inst["lhs"], env)
            rt, right = self.ref(inst["rhs"], env)
            parent, value = self.ref_id(inst["lhs"]), self.ref_id(inst["rhs"])
            src = unqualified(lt)
            if tag == "slice" and parent in self.byte_values:
                if (raw[0] != "slice" or raw[-1] != BYTE or src != ("ptr", raw[1], True, BYTE) or
                        alignment(ty) != alignment(lt) or rt != USIZE or
                        inst["rhs"] != {"kind": "constant", "type": {"kind": "int", "bits": 64, "signedness": "unsigned"}, "value": 4}):
                    raise ValueError("byte slice must retain its four-byte extent and alignment")
                self.mark(index, self.byte_values[parent], ty)
                return f"(.slice {self.lean_type(ty)} {left} {right})"
            if tag == "slice_elem_ptr" and parent in self.byte_values:
                if src[0] != "slice" or raw != ("ptr", src[1], False, BYTE) or alignment(ty) != 1 or rt != USIZE:
                    raise ValueError("byte element loses type, alignment or permissions")
                self.mark(index, self.byte_values[parent], ty)
                return f"(.sliceElementPointer {left} {right})"
            if tag in ("store", "store_safe") and parent in self.byte_slots:
                if ty != ("void",) or lt[0] != "ptr" or not lt[1] or lt[3] != rt or value not in self.byte_values:
                    raise ValueError("byte slice slot store lost its checked origin")
                return f"(.store {left} {right})"
            if tag in ("store", "store_safe") and parent in self.byte_values:
                if ty != ("void",) or src[0] != "ptr" or not src[1] or rt != BYTE:
                    raise ValueError("ill-typed byte view store")
                return f"(.wordByteStore .little {left} {right})"
            if (parent in self.byte_values or value in self.byte_values or parent in self.byte_slots or value in self.byte_slots or
                    has_alignment(ty) or has_alignment(lt) or has_alignment(rt)):
                raise ValueError("byte view or stack slot escaped checked storage")
        # Reject other uses of these pointers, including jumps/returns and
        # ordinary pointer arithmetic. SSA dominance is still checked first.
        for key in ("operand", "lhs", "rhs"):
            if key in inst:
                operand_type, _ = self.ref(inst[key], env)
                operand_id = self.ref_id(inst[key])
                if operand_id in self.byte_values or operand_id in self.byte_slots or has_alignment(operand_type):
                    raise ValueError("byte provenance cannot escape through " + tag)
        if has_alignment(ty):
            raise ValueError("aligned result has no checked byte origin")
        return super().extra_primitive(inst, ty, env)


class ByteLoopDecoder(ByteDecoder):
    allow_loops = True
