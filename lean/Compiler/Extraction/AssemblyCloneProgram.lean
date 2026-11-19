/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.AssemblyClone

namespace Compiler.Extraction.AssemblyClone

-- AssemblyItem source SHA-256: 294d255a0ddec3bbc2a00f95853e38e76a4a1ee88efda1f6b60784b75cc80c3d
def cloneCode : CloneCode := { copyPayload := true, arguments := .input, returns := .input, contents := .input, returnCopy := true }
def deinitCode : DeinitCode := { freePayload := true, invalidate := true }

end Compiler.Extraction.AssemblyClone
