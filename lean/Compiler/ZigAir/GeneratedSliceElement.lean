/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
Generated from captured AIR; do not edit. Source/backend preservation remains open.
-/
import Compiler.ZigAir.MemoryAir

namespace Compiler.ZigAir.GeneratedMemory
open MemoryAir

def fn_slice_element : Program :=
{ parameters := [(.pointer true true (.scalar (.int false 32))), (.scalar (.int false 64)), (.scalar (.int false 64))], returnType := (.pointer true false (.scalar (.int false 32))), body :=
  (.bind 0 (.pointer true true (.scalar (.int false 32)))
  (.argument 0)
  (.bind 1 (.scalar (.int false 64))
  (.argument 1)
  (.bind 2 (.scalar (.int false 64))
  (.argument 2)
  (.bind 3 (.pointer true false (.pointer true true (.scalar (.int false 32))))
  (.alloc (.pointer true true (.scalar (.int false 32))))
  (.bind 4 (.scalar .unit)
  (.store (.local 3) (.local 0))
  (.bind 5 (.pointer false false (.pointer true true (.scalar (.int false 32))))
  (.pointerCast (.pointer false false (.pointer true true (.scalar (.int false 32)))) (.local 3))
  (.bind 6 (.pointer true true (.scalar (.int false 32)))
  (.load (.local 5))
  (.bind 7 (.pointer true true (.scalar (.int false 32)))
  (.offsetPointer false (.local 6) (.constant (.scalar (.int false 64 (0)))))
  (.bind 8 (.scalar (.int false 64))
  (.scalar (.arithmetic .sub .unchecked (.local 1) (.constant (.int false 64 (0)))))
  (.bind 16 (.scalar .unit)
  (.checkBounds (.constant (.scalar (.int false 64 (0)))) (.local 1) .unbounded)
  (.bind 9 (.slice true (.scalar (.int false 32)))
  (.slice (.slice true (.scalar (.int false 32))) (.local 7) (.local 8))
  (.bind 10 (.pointer true false (.slice true (.scalar (.int false 32))))
  (.alloc (.slice true (.scalar (.int false 32))))
  (.bind 11 (.scalar .unit)
  (.store (.local 10) (.local 9))
  (.bind 12 (.pointer false false (.slice true (.scalar (.int false 32))))
  (.pointerCast (.pointer false false (.slice true (.scalar (.int false 32)))) (.local 10))
  (.bind 13 (.slice true (.scalar (.int false 32)))
  (.load (.local 12))
  (.bind 14 (.pointer true false (.scalar (.int false 32)))
  (.sliceElementPointer (.local 13) (.local 2))
  (.ret (.local 14)))))))))))))))))) }

end Compiler.ZigAir.GeneratedMemory
