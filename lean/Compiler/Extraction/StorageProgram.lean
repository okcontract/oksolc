/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.StorageRead

namespace Compiler.Extraction.Storage

-- Generated from the production insertOwned body.
-- Source SHA-256: d66c002eb6f32b6886bc4c6cb24b33b4551f47a98d95fd5c5ad84a97f64b0603
def insertProgram : Program :=
  (.command (.flag .normalized true) (.scope false (.guarded .normalized .normalized) (.branch .noRoom .capacityError .done (.branch .deterministic (.command .duplicateArguments .done) (.command (.flag .normalized false) (.command .aliasArguments .done)) (.command (.flag .arguments true) (.scope true (.guarded .arguments .arguments) (.command .createItem (.command (.flag .allocation true) (.scope true (.guarded .allocation .allocation) (.command .cloneItem (.command (.flag .value true) (.scope true (.guarded .value .value) (.command .captureId (.command .append (.command (.flag .arguments false) (.command (.flag .allocation false) (.command (.flag .value false) (.scope true (.sequence [.lastValue, .pop]) (.branch .deterministic (.command .publish (.command (.flag .normalized false) .done)) .done .ret)))))))))))))))))))

def representativeProgram : Lookup := { bound := .ge, index := .requested }

def constantProgram : ConstantRead := { lookup := representativeProgram, rejectOnPush := false }

def operationProgram : OperationRead := { lookup := representativeProgram, rejectOnOperation := false, rejectOnEqualOpcode := false, arguments := .stored }

end Compiler.Extraction.Storage
