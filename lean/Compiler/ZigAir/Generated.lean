/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
Generated from captured production AIR; do not edit.
Source validity and backend preservation are not asserted here.
-/
import Compiler.ZigAir.Scalar

namespace Compiler.ZigAir.Generated
open Scalar

def u2s : Program :=
{ parameters := [(.int false 256)], returnType := (.int true 256), body :=
  (.bind 0 (.int false 256)
  (.argument 0)
  (.block 1 .unit
  (.bind 2 .bool
  (.comparison .lt (.local 0) (.constant (.int false 256 (57896044618658097711785492504343953926634992332820282019728792003956564819968))))
  (.branch (.local 2)
  (.bind 3 (.int true 256)
  (.cast .unchecked (.int true 256) (.local 0))
  (.ret (.local 3)))
  (.jump 1 (.constant .unit))))
  (.bind 7 (.int false 256)
  (.arithmetic .sub .unchecked (.local 0) (.constant (.int false 256 (57896044618658097711785492504343953926634992332820282019728792003956564819968))))
  (.bind 8 (.int true 256)
  (.cast .unchecked (.int true 256) (.local 7))
  (.bind 9 (.int true 256)
  (.arithmetic .add .unchecked (.constant (.int true 256 (-57896044618658097711785492504343953926634992332820282019728792003956564819968))) (.local 8))
  (.ret (.local 9))))))) }

def s2u : Program :=
{ parameters := [(.int true 256)], returnType := (.int false 256), body :=
  (.bind 0 (.int true 256)
  (.argument 0)
  (.block 1 .unit
  (.bind 2 .bool
  (.comparison .ge (.local 0) (.constant (.int true 256 (0))))
  (.branch (.local 2)
  (.bind 3 (.int false 256)
  (.cast .unchecked (.int false 256) (.local 0))
  (.ret (.local 3)))
  (.jump 1 (.constant .unit))))
  (.bind 9 (.int true 256)
  (.arithmetic .sub .unchecked (.local 0) (.constant (.int true 256 (-57896044618658097711785492504343953926634992332820282019728792003956564819968))))
  (.bind 10 (.int false 256)
  (.cast .unchecked (.int false 256) (.local 9))
  (.bind 11 (.int false 256)
  (.arithmetic .add .unchecked (.constant (.int false 256 (57896044618658097711785492504343953926634992332820282019728792003956564819968))) (.local 10))
  (.ret (.local 11))))))) }

end Compiler.ZigAir.Generated
