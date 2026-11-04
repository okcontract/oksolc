/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
Generated from captured AIR; do not edit. Source/backend preservation remains open.
-/
import Compiler.ZigAir.MemoryAir

namespace Compiler.ZigAir.GeneratedMemory
open MemoryAir

def fn_read_word_byte : Program :=
{ parameters := [(.pointer false false (.scalar (.int false 32))), (.scalar (.int false 64))], returnType := (.scalar (.int false 8)), body :=
  (.bind 0 (.pointer false false (.scalar (.int false 32)))
  (.argument 0)
  (.bind 1 (.scalar (.int false 64))
  (.argument 1)
  (.bind 2 (.pointer false true (.scalar (.int false 8)))
  (.wordByteCast false true 4 (.local 0))
  (.bind 3 (.slice false (.scalar (.int false 8)))
  (.slice (.slice false (.scalar (.int false 8))) (.local 2) (.constant (.scalar (.int false 64 (4)))))
  (.bind 4 (.pointer true false (.slice false (.scalar (.int false 8))))
  (.alloc (.slice false (.scalar (.int false 8))))
  (.bind 5 (.scalar .unit)
  (.store (.local 4) (.local 3))
  (.bind 6 (.pointer false false (.slice false (.scalar (.int false 8))))
  (.pointerCast (.pointer false false (.slice false (.scalar (.int false 8)))) (.local 4))
  (.bind 7 (.slice false (.scalar (.int false 8)))
  (.load (.local 6))
  (.bind 8 (.pointer false false (.scalar (.int false 8)))
  (.sliceElementPointer (.local 7) (.local 1))
  (.bind 9 (.scalar (.int false 8))
  (.wordByteLoad .little (.local 8))
  (.ret (.local 9)))))))))))) }

def fn_write_word_byte : Program :=
{ parameters := [(.pointer true false (.scalar (.int false 32))), (.scalar (.int false 64)), (.scalar (.int false 8))], returnType := (.scalar .unit), body :=
  (.bind 0 (.pointer true false (.scalar (.int false 32)))
  (.argument 0)
  (.bind 1 (.scalar (.int false 64))
  (.argument 1)
  (.bind 2 (.scalar (.int false 8))
  (.argument 2)
  (.bind 3 (.pointer true true (.scalar (.int false 8)))
  (.wordByteCast true true 4 (.local 0))
  (.bind 4 (.slice true (.scalar (.int false 8)))
  (.slice (.slice true (.scalar (.int false 8))) (.local 3) (.constant (.scalar (.int false 64 (4)))))
  (.bind 5 (.pointer true false (.slice true (.scalar (.int false 8))))
  (.alloc (.slice true (.scalar (.int false 8))))
  (.bind 6 (.scalar .unit)
  (.store (.local 5) (.local 4))
  (.bind 7 (.pointer false false (.slice true (.scalar (.int false 8))))
  (.pointerCast (.pointer false false (.slice true (.scalar (.int false 8)))) (.local 5))
  (.bind 8 (.slice true (.scalar (.int false 8)))
  (.load (.local 7))
  (.bind 9 (.pointer true false (.scalar (.int false 8)))
  (.sliceElementPointer (.local 8) (.local 1))
  (.bind 10 (.scalar .unit)
  (.wordByteStore .little (.local 9) (.local 2))
  (.ret (.constant (.scalar .unit)))))))))))))) }

end Compiler.ZigAir.GeneratedMemory
