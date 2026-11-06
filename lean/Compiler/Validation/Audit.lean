/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Check.Axioms
import Compiler.Validation.Normalize
import Compiler.Validation.Graph
import Compiler.Validation.GraphInventory
import Compiler.Validation.GraphFailure
import Compiler.Validation.WordBlock
import Compiler.Validation.Solidity
import Compiler.Validation.Bytecode

/-! Master kernel axiom audit for the `Compiler.Validation` translation validation
and contract certification stack. Every theorem must depend solely on Lean's
foundational axioms (`propext`, `Classical.choice`, `Quot.sound`), with zero
`sorryAx`, zero `Lean.ofReduceBool`, and zero `Lean.trustCompiler`. -/
namespace Compiler.Validation.Audit

#audit_contract_proof Compiler.Validation.normalize_sound
#audit_contract_proof Compiler.Validation.equivalent_sound

#audit_contract_proof Compiler.Validation.evaluate_expand
#audit_contract_proof Compiler.Validation.validate_sound

#audit_contract_proof Compiler.Validation.Inventory.validate_sound
#audit_contract_proof Compiler.Validation.Inventory.certify

#audit_contract_proof Compiler.Validation.Failure.attempt_sound
#audit_contract_proof Compiler.Validation.Failure.certifySweep

#audit_contract_proof Compiler.Validation.WordBlock.lowerSourceNodes_sound
#audit_contract_proof Compiler.Validation.WordBlock.validate_sound
#audit_contract_proof Compiler.Validation.WordBlock.validateSource_sound

#audit_contract_proof Compiler.Validation.Bytecode.previewSource_parsed_selector
#audit_contract_proof Compiler.Validation.Bytecode.previewCreation_run_exact
#audit_contract_proof Compiler.Validation.Bytecode.previewDeployment_certified
#audit_contract_proof Compiler.Validation.Bytecode.previewRuntime_run_universal
#audit_contract_proof Compiler.Validation.Bytecode.publicPreviewIdentity_certified
#audit_contract_proof Compiler.Validation.Bytecode.corruptedPreviewIdentity_rejected
#audit_contract_proof Compiler.Validation.Bytecode.validateContractArtifact_sound

end Compiler.Validation.Audit
