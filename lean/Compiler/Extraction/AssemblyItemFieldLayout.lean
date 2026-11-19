/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyItemLayout

namespace Compiler.Extraction.AssemblyItem

-- Complete nested declarations; optional payloads are atomic typed values.
-- This declares allocation geometry, not initialized native values.
-- Source SHA-256: 294d255a0ddec3bbc2a00f95853e38e76a4a1ee88efda1f6b60784b75cc80c3d
-- Instruction source SHA-256: 49798b18d069e27354224c7aa6f551399c2b4bf3612bb7e1b55dacc764751ea2
-- Debug source SHA-256: c10453f84032d6d684f15750358315f0252ea6f733a756ae906bbefd4789f8ea
-- Source-location SHA-256: 918336eeb9ca13931ea21866147fa211a30dddd7b41d82ca6dbe666fb6d0dcc0
def data_valueOffset : Nat := 0
def pushed_valueOffset : Nat := 32
def verbatimOffset : Nat := 80
def debug_dataOffset : Nat := 120
def immutable_occurrencesOffset : Nat := 184
def modifier_depthOffset : Nat := 200
def item_typeOffset : Nat := 208
def jump_typeOffset : Nat := 212
def instruction_valueOffset : Nat := 216

def sourceNameType : Compiler.ZigAir.Memory.Ty := .optionalObject (.slice false (.scalar (.int false 8))) ⟨16, 8⟩
def source_location_source_nameOffset : Nat := 0
def source_location_startOffset : Nat := 16
def source_location_endOffset : Nat := 20
def sourceLocationType : Compiler.ZigAir.Memory.Ty :=
  .aggregate "liblangutil.source_location.SourceLocation" ⟨24, 8⟩ [(0, .object sourceNameType), (16, .scalar (.int true 32)), (20, .scalar (.int true 32))]
def verbatim_argumentsOffset : Nat := 0
def verbatim_return_variablesOffset : Nat := 8
def verbatim_dataOffset : Nat := 16
def verbatimType : Compiler.ZigAir.Memory.Ty :=
  .aggregate "libevmasm.assembly_item.VerbatimBytecode" ⟨32, 8⟩ [(0, .scalar (.int false 64)), (8, .scalar (.int false 64)), (16, .slice true (.int false 8))]
def debug_data_native_locationOffset : Nat := 0
def debug_data_origin_locationOffset : Nat := 24
def debug_data_ast_idOffset : Nat := 48
def debugDataType : Compiler.ZigAir.Memory.Ty :=
  .aggregate "liblangutil.debug_data.DebugData" ⟨64, 8⟩ [(0, .object sourceLocationType), (24, .object sourceLocationType), (48, .object (.optionalScalar (.int true 64)))]
def verbatimOptionalType : Compiler.ZigAir.Memory.Ty := .optionalObject verbatimType ⟨40, 8⟩

def itemTagValues : List Int := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
def jumpTagValues : List Int := [0, 1, 2]

def viewType : Compiler.ZigAir.Memory.Ty :=
  .aggregate "src/libevmasm/assembly_item.zig::AssemblyItem" ⟨224, 16⟩
    [(0, .scalar (.int false 256)),
    (32, .object (.optionalScalar (.int false 256))),
    (80, .object verbatimOptionalType),
    (120, .object debugDataType),
    (184, .object (.optionalScalar (.int false 64))),
    (200, .scalar (.int false 64)),
    (208, .scalar (.int true 32)),
    (212, .scalar (.int true 32)),
    (216, .object (.optionalScalar (.int false 8)))]

end Compiler.Extraction.AssemblyItem
