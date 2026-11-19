/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
Generated from the four complete scalar asBytes specializations and their caller cuts.
The argument-slice helper and complete hash-caller execution remain separate obligations.
-/
import Compiler.ZigAir.ScalarBytesAir

namespace Compiler.ZigAir.GeneratedExpressionHashBytes
open Compiler.ZigAir.Memory

def kind : AggregateAir.Program :=
{ parameters := [(.pointer false false (.scalar (.int false 32)))], returnType := (.pointer false false (.array 4 (.scalar (.int false 8)))), body :=
  (.bind 0 (.pointer false false (.scalar (.int false 32)))
  (.argument 0)
  (.bind 1 (.pointer false false (.array 4 (.scalar (.int false 8))))
  (.scalarByteArray false 4 4 (.local 0))
  (.ret (.local 1)))) }

def kindView (next : AggregateCall.Code) : AggregateCall.Code :=
  .bind 8 (.pointer false false (.scalar (.int false 32)))
    (.primitive (.fieldPointer (.local 3) 48))
    (ScalarBytesAir.viewCode kind (.local 8) 13 14 4 next)

def instruction : AggregateAir.Program :=
{ parameters := [(.pointer false false (.scalar (.int false 8)))], returnType := (.pointer false false (.array 1 (.scalar (.int false 8)))), body :=
  (.bind 0 (.pointer false false (.scalar (.int false 8)))
  (.argument 0)
  (.bind 1 (.pointer false false (.array 1 (.scalar (.int false 8))))
  (.scalarByteArray false 1 1 (.local 0))
  (.ret (.local 1)))) }

def instructionView (next : AggregateCall.Code) : AggregateCall.Code :=
  .bind 16 (.pointer false false (.scalar (.int false 8)))
    (.primitive (.fieldPointer (.local 3) 56))
    (ScalarBytesAir.viewCode instruction (.local 16) 21 22 1 next)

def data : AggregateAir.Program :=
{ parameters := [(.pointer false false (.scalar (.int false 256)))], returnType := (.pointer false false (.array 32 (.scalar (.int false 8)))), body :=
  (.bind 0 (.pointer false false (.scalar (.int false 256)))
  (.argument 0)
  (.bind 1 (.pointer false false (.array 32 (.scalar (.int false 8))))
  (.scalarByteArray false 16 32 (.local 0))
  (.ret (.local 1)))) }

def dataView (next : AggregateCall.Code) : AggregateCall.Code :=
  .bind 24 (.pointer false false (.scalar (.int false 256)))
    (.primitive (.fieldPointer (.local 3) 0))
    (ScalarBytesAir.viewCode data (.local 24) 29 30 32 next)

def sequence : AggregateAir.Program :=
{ parameters := [(.pointer false false (.scalar (.int false 32)))], returnType := (.pointer false false (.array 4 (.scalar (.int false 8)))), body :=
  (.bind 0 (.pointer false false (.scalar (.int false 32)))
  (.argument 0)
  (.bind 1 (.pointer false false (.array 4 (.scalar (.int false 8))))
  (.scalarByteArray false 4 4 (.local 0))
  (.ret (.local 1)))) }

def sequenceView (next : AggregateCall.Code) : AggregateCall.Code :=
  .bind 41 (.pointer false false (.scalar (.int false 32)))
    (.primitive (.fieldPointer (.local 3) 52))
    (ScalarBytesAir.viewCode sequence (.local 41) 46 47 4 next)

end Compiler.ZigAir.GeneratedExpressionHashBytes
