/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Lake
open Lake DSL

package oksolcVerification where
  leanOptions := #[⟨`warningAsError, true⟩]

lean_lib Contract where
  globs := #[.submodules `Contract]

@[default_target]
lean_lib Compiler where
  globs := #[.submodules `Compiler]
