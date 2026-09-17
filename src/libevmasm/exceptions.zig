// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Error-set translation of the `libevmasm` exception hierarchy.

pub const AssemblyException = error{AssemblyException};
pub const AssemblyImportException = AssemblyException || error{AssemblyImportException};
pub const OptimizerException = AssemblyException || error{OptimizerException};
pub const StackTooDeepException = OptimizerException || error{StackTooDeepException};
pub const ItemNotAvailableException = OptimizerException || error{ItemNotAvailableException};

pub const Error = AssemblyImportException || StackTooDeepException || ItemNotAvailableException;

test "specialized assembly failures remain members of the common error surface" {
    const value: Error = error.StackTooDeepException;
    try @import("std").testing.expect(value == error.StackTooDeepException);
}
