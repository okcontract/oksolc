/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
Generated from captured AIR; do not edit. Source/backend preservation remains open.
-/
import Compiler.ZigAir.MemoryWordPair

namespace Compiler.ZigAir.GeneratedMemory
open MemoryAir

def fn_swap_u32 : WordPairProgram :=
{ program :=
  { parameters := [(.pointer true false (.scalar (.int false 32))), (.pointer true false (.scalar (.int false 32)))], returnType := (.scalar .unit), body :=
  (.bind 0 (.pointer true false (.scalar (.int false 32)))
  (.argument 0)
  (.bind 1 (.pointer true false (.scalar (.int false 32)))
  (.argument 1)
  (.bind 3 (.pointer true true (.scalar (.int false 8)))
  (.wordByteCast true true 4 (.local 0))
  (.bind 4 (.slice true (.scalar (.int false 8)))
  (.slice (.slice true (.scalar (.int false 8))) (.local 3) (.constant (.scalar (.int false 64 (4)))))
  (.bind 5 (.pointer true true (.scalar (.int false 8)))
  (.wordByteCast true true 4 (.local 1))
  (.bind 6 (.slice true (.scalar (.int false 8)))
  (.slice (.slice true (.scalar (.int false 8))) (.local 5) (.constant (.scalar (.int false 64 (4)))))
  (.bind 7 (.pointer true false (.scalar (.int false 64)))
  (.alloc (.scalar (.int false 64)))
  (.bind 8 (.scalar .unit)
  (.store (.local 7) (.constant (.scalar (.int false 64 (0)))))
  (.bind 9 (.scalar (.int false 64))
  (.sliceLen (.local 4))
  (.bind 10 (.scalar (.int false 64))
  (.sliceLen (.local 6))
  (.block 11 (.scalar .unit)
  (.loop rfl 12
  (.bind 13 (.scalar (.int false 64))
  (.load (.local 7))
  (.block 14 (.scalar .unit)
  (.bind 15 (.scalar (.int false 64))
  (.scalar (.cast .bitcast (.int false 64) (.local 13)))
  (.bind 16 (.scalar (.int false 64))
  (.scalar (.cast .bitcast (.int false 64) (.local 9)))
  (.bind 17 (.scalar .bool)
  (.scalar (.comparison .lt (.local 15) (.local 16)))
  (.branch (.local 17)
  (.bind 18 (.pointer true false (.scalar (.int false 8)))
  (.sliceElementPointer (.local 4) (.local 13))
  (.bind 19 (.pointer true false (.scalar (.int false 8)))
  (.sliceElementPointer (.local 6) (.local 13))
  (.bind 20 (.scalar (.int false 8))
  (.wordByteLoad .little (.local 18))
  (.bind 21 (.scalar (.int false 8))
  (.wordByteLoad .little (.local 19))
  (.bind 22 (.scalar .unit)
  (.wordByteStore .little (.local 18) (.local 21))
  (.bind 23 (.scalar .unit)
  (.wordByteStore .little (.local 19) (.local 20))
  (.jump 14 (.constant (.scalar .unit)))))))))
  (.jump 11 (.constant (.scalar .unit)))))))
  (.bind 27 (.scalar (.int false 64))
  (.scalar (.arithmetic .add .unchecked (.local 13) (.constant (.int false 64 (1)))))
  (.bind 28 (.scalar .unit)
  (.store (.local 7) (.local 27))
  (.repeat rfl 12))))))
  (.ret (.constant (.scalar .unit)))))))))))))) } }

end Compiler.ZigAir.GeneratedMemory
