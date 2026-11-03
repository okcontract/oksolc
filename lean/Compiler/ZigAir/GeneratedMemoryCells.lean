/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
Generated from captured AIR; do not edit. Source/backend preservation remains open.
-/
import Compiler.ZigAir.MemoryAir

namespace Compiler.ZigAir.GeneratedMemory
open MemoryAir

def fn_move_back : Program :=
{ parameters := [(.pointer true true (.scalar (.int false 32))), (.scalar (.int false 64))], returnType := (.pointer true true (.scalar (.int false 32))), body :=
  (.bind 0 (.pointer true true (.scalar (.int false 32)))
  (.argument 0)
  (.bind 1 (.scalar (.int false 64))
  (.argument 1)
  (.bind 2 (.pointer true true (.scalar (.int false 32)))
  (.offsetPointer true (.local 0) (.local 1))
  (.ret (.local 2))))) }

def fn_load_store : Program :=
{ parameters := [(.pointer true false (.scalar (.int false 32))), (.scalar (.int false 32))], returnType := (.scalar (.int false 32)), body :=
  (.bind 0 (.pointer true false (.scalar (.int false 32)))
  (.argument 0)
  (.bind 1 (.scalar (.int false 32))
  (.argument 1)
  (.bind 2 (.scalar .unit)
  (.store (.local 0) (.local 1))
  (.bind 3 (.scalar (.int false 32))
  (.load (.local 0))
  (.ret (.local 3)))))) }

def fn_slice_fields : Program :=
{ parameters := [(.pointer true false (.slice true (.scalar (.int false 8)))), (.scalar (.int false 64))], returnType := (.pointer true true (.scalar (.int false 8))), body :=
  (.bind 0 (.pointer true false (.slice true (.scalar (.int false 8))))
  (.argument 0)
  (.bind 1 (.scalar (.int false 64))
  (.argument 1)
  (.bind 2 (.pointer true false (.pointer true false (.slice true (.scalar (.int false 8)))))
  (.alloc (.pointer true false (.slice true (.scalar (.int false 8)))))
  (.bind 3 (.scalar .unit)
  (.store (.local 2) (.local 0))
  (.bind 4 (.pointer false false (.pointer true false (.slice true (.scalar (.int false 8)))))
  (.pointerCast (.pointer false false (.pointer true false (.slice true (.scalar (.int false 8))))) (.local 2))
  (.bind 5 (.pointer true false (.slice true (.scalar (.int false 8))))
  (.load (.local 4))
  (.bind 6 (.pointer true false (.scalar (.int false 64)))
  (.pointerField true (.local 5))
  (.bind 7 (.scalar .unit)
  (.store (.local 6) (.local 1))
  (.bind 8 (.pointer true false (.slice true (.scalar (.int false 8))))
  (.load (.local 4))
  (.bind 9 (.pointer true false (.pointer true true (.scalar (.int false 8))))
  (.pointerField false (.local 8))
  (.bind 10 (.pointer true true (.scalar (.int false 8)))
  (.load (.local 9))
  (.ret (.local 10))))))))))))) }

def fn_buffer_alias : Program :=
{ parameters := [(.pointer true true (.scalar (.int false 32))), (.scalar (.int false 64)), (.scalar (.int false 32)), (.scalar (.int false 32))], returnType := (.scalar (.int false 32)), body :=
  (.bind 0 (.pointer true true (.scalar (.int false 32)))
  (.argument 0)
  (.bind 1 (.scalar (.int false 64))
  (.argument 1)
  (.bind 2 (.scalar (.int false 32))
  (.argument 2)
  (.bind 3 (.scalar (.int false 32))
  (.argument 3)
  (.bind 4 (.pointer true false (.scalar (.int false 32)))
  (.pointerCast (.pointer true false (.scalar (.int false 32))) (.local 0))
  (.bind 5 (.pointer true true (.scalar (.int false 32)))
  (.offsetPointer false (.local 0) (.local 1))
  (.bind 6 (.pointer true false (.scalar (.int false 32)))
  (.pointerCast (.pointer true false (.scalar (.int false 32))) (.local 5))
  (.bind 7 (.scalar .unit)
  (.store (.local 4) (.local 2))
  (.bind 8 (.scalar .unit)
  (.store (.local 6) (.local 3))
  (.bind 9 (.scalar (.int false 32))
  (.load (.local 4))
  (.ret (.local 9)))))))))))) }

def fn_initialize_slice : Program :=
{ parameters := [(.pointer true false (.slice true (.scalar (.int false 8)))), (.pointer true true (.scalar (.int false 8))), (.scalar (.int false 64))], returnType := (.scalar .unit), body :=
  (.bind 0 (.pointer true false (.slice true (.scalar (.int false 8))))
  (.argument 0)
  (.bind 1 (.pointer true true (.scalar (.int false 8)))
  (.argument 1)
  (.bind 2 (.scalar (.int false 64))
  (.argument 2)
  (.bind 3 (.pointer true false (.pointer true false (.slice true (.scalar (.int false 8)))))
  (.alloc (.pointer true false (.slice true (.scalar (.int false 8)))))
  (.bind 4 (.scalar .unit)
  (.store (.local 3) (.local 0))
  (.bind 5 (.pointer false false (.pointer true false (.slice true (.scalar (.int false 8)))))
  (.pointerCast (.pointer false false (.pointer true false (.slice true (.scalar (.int false 8))))) (.local 3))
  (.bind 6 (.pointer true false (.slice true (.scalar (.int false 8))))
  (.load (.local 5))
  (.bind 7 (.pointer true false (.pointer true true (.scalar (.int false 8))))
  (.pointerField false (.local 6))
  (.bind 8 (.scalar .unit)
  (.store (.local 7) (.local 1))
  (.bind 9 (.pointer true false (.slice true (.scalar (.int false 8))))
  (.load (.local 5))
  (.bind 10 (.pointer true false (.scalar (.int false 64)))
  (.pointerField true (.local 9))
  (.bind 11 (.scalar .unit)
  (.store (.local 10) (.local 2))
  (.ret (.constant (.scalar .unit))))))))))))))) }

def fn_initialize_length : Program :=
{ parameters := [(.pointer true false (.slice true (.scalar (.int false 8)))), (.scalar (.int false 64))], returnType := (.scalar (.int false 64)), body :=
  (.bind 0 (.pointer true false (.slice true (.scalar (.int false 8))))
  (.argument 0)
  (.bind 1 (.scalar (.int false 64))
  (.argument 1)
  (.bind 2 (.pointer true false (.pointer true false (.slice true (.scalar (.int false 8)))))
  (.alloc (.pointer true false (.slice true (.scalar (.int false 8)))))
  (.bind 3 (.scalar .unit)
  (.store (.local 2) (.local 0))
  (.bind 4 (.pointer false false (.pointer true false (.slice true (.scalar (.int false 8)))))
  (.pointerCast (.pointer false false (.pointer true false (.slice true (.scalar (.int false 8))))) (.local 2))
  (.bind 5 (.pointer true false (.slice true (.scalar (.int false 8))))
  (.load (.local 4))
  (.bind 6 (.pointer true false (.scalar (.int false 64)))
  (.pointerField true (.local 5))
  (.bind 7 (.scalar .unit)
  (.store (.local 6) (.local 1))
  (.bind 8 (.pointer true false (.slice true (.scalar (.int false 8))))
  (.load (.local 4))
  (.bind 9 (.pointer true false (.scalar (.int false 64)))
  (.pointerField true (.local 8))
  (.bind 10 (.scalar (.int false 64))
  (.load (.local 9))
  (.ret (.local 10))))))))))))) }

end Compiler.ZigAir.GeneratedMemory
