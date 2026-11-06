/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Lake
open Lake DSL

package oksolcVerification where
  leanOptions := #[⟨`warningAsError, true⟩]

lean_lib Contract where
  globs := #[.andSubmodules `Contract]

@[default_target]
lean_lib Compiler where
  globs := #[.andSubmodules `Compiler]

lean_exe «oksolc-verify» where
  root := `Compiler.Validation.Main
