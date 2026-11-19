/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
Generated from captured AIR; do not edit. Source/backend preservation remains open.
-/
import Compiler.ZigAir.MemoryExecution

namespace Compiler.ZigAir.GeneratedMemory
open MemoryAir

def fn_exp256 : Program true :=
{ parameters := [(.scalar (.int false 256)), (.scalar (.int false 256))], returnType := (.scalar (.int false 256)), body :=
  (.bind 0 (.scalar (.int false 256))
  (.argument 0)
  (.bind 1 (.scalar (.int false 256))
  (.argument 1)
  (.bind 2 (.pointer true false (.scalar (.int false 256)))
  (.alloc (.scalar (.int false 256)))
  (.bind 3 (.scalar .unit)
  (.store (.local 2) (.local 0))
  (.bind 5 (.pointer true false (.scalar (.int false 256)))
  (.alloc (.scalar (.int false 256)))
  (.bind 6 (.scalar .unit)
  (.store (.local 5) (.local 1))
  (.bind 8 (.pointer true false (.scalar (.int false 256)))
  (.alloc (.scalar (.int false 256)))
  (.bind 9 (.scalar .unit)
  (.store (.local 8) (.constant (.scalar (.int false 256 (1)))))
  (.block 10 (.scalar .unit)
  (.loop rfl 11
  (.block 12 (.scalar .unit)
  (.bind 13 (.scalar (.int false 256))
  (.load (.local 5))
  (.bind 14 (.scalar .bool)
  (.scalar (.comparison .ne (.local 13) (.constant (.int false 256 (0)))))
  (.branch (.local 14)
  (.block 16 (.scalar .unit)
  (.bind 17 (.scalar (.int false 256))
  (.load (.local 5))
  (.bind 18 (.scalar (.int false 256))
  (.scalar (.bitAnd (.local 17) (.constant (.int false 256 (1)))))
  (.bind 19 (.scalar .bool)
  (.scalar (.comparison .ne (.local 18) (.constant (.int false 256 (0)))))
  (.branch (.local 19)
  (.bind 20 (.scalar (.int false 256))
  (.load (.local 8))
  (.bind 21 (.scalar (.int false 256))
  (.load (.local 2))
  (.bind 22 (.scalar (.int false 256))
  (.scalar (.arithmetic .mul .wrapping (.local 20) (.local 21)))
  (.bind 23 (.scalar .unit)
  (.store (.local 8) (.local 22))
  (.jump 16 (.constant (.scalar .unit)))))))
  (.jump 16 (.constant (.scalar .unit)))))))
  (.bind 27 (.scalar (.int false 256))
  (.load (.local 2))
  (.bind 28 (.scalar (.int false 256))
  (.load (.local 2))
  (.bind 29 (.scalar (.int false 256))
  (.scalar (.arithmetic .mul .wrapping (.local 27) (.local 28)))
  (.bind 30 (.scalar .unit)
  (.store (.local 2) (.local 29))
  (.bind 32 (.scalar (.int false 256))
  (.load (.local 5))
  (.bind 33 (.scalar (.int false 256))
  (.scalar (.shiftRight (.local 32) (.constant (.int false 8 (1)))))
  (.bind 34 (.scalar .unit)
  (.store (.local 5) (.local 33))
  (.jump 12 (.constant (.scalar .unit)))))))))))
  (.jump 10 (.constant (.scalar .unit))))))
  (.repeat rfl 11)))
  (.bind 39 (.scalar (.int false 256))
  (.load (.local 8))
  (.ret (.local 39)))))))))))) }

end Compiler.ZigAir.GeneratedMemory
