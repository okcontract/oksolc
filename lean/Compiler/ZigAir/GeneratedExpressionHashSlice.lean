/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
Generated from complete captured sliceAsBytes AIR and its caller cut.
Source/backend correspondence and complete caller execution remain open.
-/
import Compiler.ZigAir.AggregateCall

namespace Compiler.ZigAir.GeneratedExpressionHashSlice
open Compiler.ZigAir.Memory

def arguments : AggregateAir.Program :=
{ parameters := [(.slice false (.scalar (.int false 32)))], returnType := (.slice false (.scalar (.int false 8))), body :=
  (.bind 0 (.slice false (.scalar (.int false 32)))
  (.argument 0)
  (.bind 1 (.pointer true false (.slice false (.scalar (.int false 32))))
  (.memory (.alloc (.slice false (.scalar (.int false 32)))))
  (.bind 2 (.scalar .unit)
  (.store (.local 1) (.local 0))
  (.bind 3 (.pointer false false (.slice false (.scalar (.int false 32))))
  (.memory (.pointerCast (.pointer false false (.slice false (.scalar (.int false 32)))) (.local 1)))
  (.block 9 (.scalar .unit)
  (.bind 10 (.pointer false false (.scalar (.int false 64)))
  (.memory (.pointerField true (.local 3)))
  (.bind 11 (.scalar (.int false 64))
  (.load (.local 10))
  (.bind 12 (.scalar (.int false 64))
  (.memory (.scalar (.cast .bitcast (.int false 64) (.local 11))))
  (.bind 13 (.scalar .bool)
  (.memory (.scalar (.comparison .eq (.local 12) (.constant (.int false 64 (0))))))
  (.block 14 (.scalar .bool)
  (.branch (.local 13)
  (.jump 14 (.constant (.value (.scalar (.bool true)))))
  (.jump 14 (.constant (.value (.scalar (.bool false))))))
  (.branch (.local 14)
  (.ret (.constant .emptyBytes))
  (.jump 9 (.constant (.value (.scalar .unit))))))))))
  (.bind 30 (.pointer false true (.scalar (.int false 32)))
  (.memory (.slicePtr (.local 0)))
  (.bind 31 (.pointer false true (.scalar (.int false 8)))
  (.memory (.wordByteCast false true 4 (.local 30)))
  (.bind 32 (.pointer true false (.pointer false true (.scalar (.int false 8))))
  (.memory (.alloc (.pointer false true (.scalar (.int false 8)))))
  (.bind 33 (.scalar .unit)
  (.store (.local 32) (.local 31))
  (.bind 34 (.pointer false false (.pointer false true (.scalar (.int false 8))))
  (.memory (.pointerCast (.pointer false false (.pointer false true (.scalar (.int false 8)))) (.local 32)))
  (.bind 35 (.pointer false false (.scalar (.int false 64)))
  (.memory (.pointerField true (.local 3)))
  (.bind 36 (.scalar (.int false 64))
  (.load (.local 35))
  (.bind 37 (.scalar (.int false 64))
  (.memory (.scalar (.arithmetic .mul .unchecked (.local 36) (.constant (.int false 64 (4))))))
  (.bind 38 (.pointer false true (.scalar (.int false 8)))
  (.load (.local 34))
  (.bind 39 (.pointer false true (.scalar (.int false 8)))
  (.memory (.offsetPointer false (.local 38) (.constant (.scalar (.int false 64 (0))))))
  (.bind 40 (.scalar (.int false 64))
  (.memory (.scalar (.arithmetic .sub .unchecked (.local 37) (.constant (.int false 64 (0))))))
  (.bind 43 (.scalar .unit)
  (.memory (.checkBounds (.constant (.scalar (.int false 64 (0)))) (.local 37) .unbounded))
  (.bind 41 (.slice false (.scalar (.int false 8)))
  (.memory (.slice (.slice false (.scalar (.int false 8))) (.local 39) (.local 40)))
  (.ret (.local 41)))))))))))))))))))) }

def argumentsView (next : AggregateCall.Code) : AggregateCall.Code :=
  .bind 32 (.pointer false false (.slice false (.scalar (.int false 32))))
    (.primitive (.fieldPointer (.local 3) 32))
    (.bind 33 (.slice false (.scalar (.int false 32))) (.primitive (.load (.local 32)))
      (.bind 38 (.slice false (.scalar (.int false 8))) (.invoke arguments [(.local 33)])
        (.bind 39 (.slice false (.scalar (.int false 8))) (.primitive (.copy (.local 38))) next)))

end Compiler.ZigAir.GeneratedExpressionHashSlice
